From Coq Require Import String List Relations.Relation_Definitions.

From Paco Require Import paco.

Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts.
Import ListNotations.

Inductive Forall2Ind {a b : Type}
  (P : a -> b -> Prop)
  : coseq a -> coseq b -> Prop :=

| f2i_nil :
    Forall2Ind P conil conil

| f2i_cons :
    forall x y xs ys,
      P x y ->
      Forall2Ind P xs ys ->
      Forall2Ind P (cocons x xs) (cocons y ys).

Definition branch_rel
  (R : st -> st -> Prop)
  (u v : string * local.sort * st) : Prop :=
  exists l s T U,
    u = (l, s, T) /\
    v = (l, s, U) /\
    R T U.

Inductive BranchSubset
  {a b : Type}
  (P : a -> b -> Prop)
  : coseq a -> coseq b -> Prop :=

| bs_nil :
    BranchSubset P conil conil

| bs_keep :
    forall x y xs ys,
      P x y ->
      BranchSubset P xs ys ->
      BranchSubset P (cocons x xs) (cocons y ys)

| bs_skip :
    forall x xs ys,
      BranchSubset P xs ys ->
      BranchSubset P (cocons x xs) ys.

Definition BranchSubsetLabel
  (R : st -> st -> Prop)
  (xs ys : coseq (string * local.sort * st)) : Prop :=
  forall l s U,
    copathsel l s ys U ->
    exists T,
      copathsel l s xs T /\
      R T U.

Inductive permitted_send :
  string -> string -> local.sort -> st -> st -> Prop :=

| ps_base :
    forall p l s xs T,
      copathsel l s xs T ->
      permitted_send p l s (st_send p xs) T

| ps_through_send :
    forall p q l s xs ys,
      p <> q ->
      BranchSubsetLabel (permitted_send p l s) xs ys ->
      ys <> conil ->
      permitted_send p l s (st_send q xs) (st_send q ys)

| ps_through_receive :
    forall p q l s xs ys,
      Forall2Ind (branch_rel (permitted_send p l s)) xs ys ->
      permitted_send p l s  (st_receive q xs) (st_receive q ys).

Inductive permitted_receive :
  string -> string -> local.sort -> st -> st -> Prop :=

(* Direct receive *)
| pr_base :
    forall p l s xs T,
      copathsel l s xs T ->
      permitted_receive p l s
        (st_receive p xs) T

(* Anticipate receive through another participant's input *)
| pr_through_receive :
    forall p q l s xs ys,
      p <> q ->
      BranchSubsetLabel
        (permitted_receive p l s) xs ys ->
      ys <> conil ->
      permitted_receive p l s
        (st_receive q xs)
        (st_receive q ys)

(* Anticipate receive through an output *)
| pr_through_send :
    forall p q l s xs ys,
      Forall2Ind
        (branch_rel (permitted_receive p l s))
        xs ys ->
      permitted_receive p l s
        (st_send q xs)
        (st_send q ys).


Inductive Sends : string -> st -> Prop :=

| sends_base :
    forall p xs,
      xs <> conil ->
      Sends p (st_send p xs)

| sends_through_send :
    forall p q xs,
      xs <> conil ->
      (forall l s T,
        copathsel l s xs T ->
        Sends p T) ->
      Sends p (st_send q xs).

Inductive Recvs : string -> st -> Prop :=

| recvs_base :
    forall p xs,
      xs <> conil ->
      Recvs p (st_receive p xs)

| recvs_through_receive :
    forall p q xs,
      xs <> conil ->
      (forall l s T,
        copathsel l s xs T ->
        Recvs p T) ->
      Recvs p (st_receive q xs).

Definition subtype_directR
  (R : st -> st -> Prop)
  (T U : st) : Prop :=

  (* Clause 1: Outputs of T *)
  (match T with
   | st_send p xs =>
       forall l s T',
         copathsel l s xs T' ->
         exists U',
           permitted_send p l s U U' /\
           R T' U'
   | _ => True
   end)

  /\

  (* Clause 2: Inputs of T *)
  (match T with
   | st_receive p xs => Recvs p U
   | _ => True
   end)

  /\

  (* Clause 3: Outputs of U *)
  (match U with
   | st_send p xs => Sends p T
   | _ => True
   end)

  /\

  (* Clause 4: Inputs of U *)
  (match U with
   | st_receive p xs =>
       forall l s U',
         copathsel l s xs U' ->
         exists T',
           permitted_receive p l s T T' /\
           R T' U'
   | _ => True
   end).

Definition subtype_direct (T U : st) : Prop :=
  paco2 subtype_directR bot2 T U.

Lemma subtype_directR_mon :
  monotone2 subtype_directR.
Proof.
  unfold monotone2, subtype_directR.
  intros T U R R' H.
  destruct H as [H1 [H2 [H3 H4]]].
  repeat split.
  - destruct T; simpl in *; auto.
    intros l s0 T' Hsel.
    destruct (H1 l s0 T' Hsel) as [U' [Hp HR]].
    exists U'.
    split; auto.
  - exact H2.
  - exact H3.
  - destruct U; simpl in *; auto.
    intros l s0 U' Hsel.
    destruct (H4 l s0 U' Hsel) as [T' [Hp HR]].
    exists T'.
    split; auto.
Qed.

Definition input1 (p l : string) (s : local.sort) (T : st) : st :=
  st_receive p (cocons (l, s, T) conil).

Definition output1 (p l : string) (s : local.sort) (T : st) : st :=
  st_send p (cocons (l, s, T) conil).

Lemma test_direct_end :
  subtype_direct st_end st_end.
Proof.
  pfold.
  unfold subtype_directR.
  simpl. easy.
Qed.

Inductive R1_sim
  (a b la lb : string)
  (s : local.sort)
  : st -> st -> Prop :=

| R1_initial :
    R1_sim a b la lb s
      (input1 a la s (input1 b lb s st_end))
      (input1 b lb s (input1 a la s st_end))

| R1_cont :
    R1_sim a b la lb s
      (input1 a la s st_end)
      (input1 a la s st_end)

| R1_end :
    R1_sim a b la lb s st_end st_end.

Lemma copathsel_singleton :
  forall l s T l' s' U,
    copathsel l s (cocons (l', s', U) conil) T ->
    l = l' /\ s = s' /\ T = U.
Proof.
  intros l s T l' s' U Hsel.
  inversion Hsel; subst.
  - repeat split; reflexivity.
  - match goal with
    | H : copathsel _ _ conil _ |- _ =>
        inversion H
    end.
  inversion H7.
Qed.

Lemma R1_sim_step :
  forall a b la lb s T U,
    a <> b ->
    R1_sim a b la lb s T U ->
    subtype_directR (R1_sim a b la lb s) T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  inversion Hsim; subst; clear Hsim.
  - unfold subtype_directR.
    simpl.
    repeat split; try easy.
    + unfold input1.
      eapply recvs_through_receive.
      * discriminate.
      * intros l s0 V Hsel.
        inversion Hsel; subst.
        -- apply recvs_base.
           discriminate.
        -- match goal with
           | H : copathsel _ _ conil _ |- _ =>
               inversion H
           end.
        inversion H7.
        intros.
apply copathsel_singleton in H.
destruct H as [Hl [Hs HU]].
subst l s0 U'.

exists (input1 a la s st_end).
split.

- unfold input1.
  eapply pr_through_receive.
  + easy.
  + unfold BranchSubsetLabel.
    intros l0 s0 U Hsel.
    apply copathsel_singleton in Hsel.
    destruct Hsel as [Hl [Hs HU]].
    subst l0 s0 U.

    exists (input1 b lb s st_end).
    split.
    * constructor.
    * unfold input1.
      apply pr_base.
      constructor.
  + discriminate.
  constructor.
unfold subtype_directR.
simpl.
repeat split; try easy.

- (* Clause 2: Recvs *)
  unfold input1.
  apply recvs_base.
  discriminate.

- (* Clause 4: Match the input *)
  intros l s0 U' Hsel.

  apply copathsel_singleton in Hsel.
  destruct Hsel as [Hl [Hs HU]].
  subst l s0 U'.

  exists st_end.
  split.

  + (* Direct receive *)
    unfold input1.
    apply pr_base.
    constructor.

  + (* Continuations belong to R1_sim *)
    apply R1_end.
constructor; easy.
Qed.

Lemma R1_sim_sound :
  forall a b la lb s T U,
    a <> b ->
    R1_sim a b la lb s T U ->
    subtype_direct T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := R1_sim a b la lb s)
    (r := bot2).

  - intros rr INCr INCl x y Hxy.

    pfold.
eapply subtype_directR_mon. 
apply R1_sim_step.
- exact Hneq.
- exact Hxy.
- intros x' y' Hrel.
  right.
  apply INCl.
  exact Hrel.
 easy.
Qed.

Lemma test_R1 :
  forall a b la lb s,
    a <> b ->
    subtype_direct
      (input1 a la s (input1 b lb s st_end))
      (input1 b lb s (input1 a la s st_end)).
Proof.
  intros a b la lb s Hneq.
  eapply R1_sim_sound.
  - exact Hneq.
  - apply R1_initial.
Qed.

(* ============================================================ *)
(* R2 — Output anticipation across an input                     *)
(* ============================================================ *)

Inductive R2_sim
  (a la lb : string)
  (s : sort)
  : st -> st -> Prop :=

| R2_initial :
    R2_sim a la lb s
      (output1 a la s (input1 a lb s st_end))
      (input1 a lb s (output1 a la s st_end))

| R2_input :
    R2_sim a la lb s
      (input1 a lb s st_end)
      (input1 a lb s st_end)

| R2_output :
    R2_sim a la lb s
      (output1 a la s st_end)
      (output1 a la s st_end)

| R2_end :
    R2_sim a la lb s st_end st_end.

Lemma R2_sim_step :
  forall a la lb s T U,
    R2_sim a la lb s T U ->
    subtype_directR (R2_sim a la lb s) T U.
Proof.
  intros a la lb s T U Hsim.
  inversion Hsim; subst; clear Hsim.
- unfold subtype_directR.
  simpl.
  repeat split; try easy.
  intros.
apply copathsel_singleton in H.
destruct H as [Hl [Hs HT]].
subst l s0 T'.

exists (input1 a lb s st_end).
split.

- (* Output anticipation across an input *)
  unfold input1, output1.
  eapply ps_through_receive.

  apply f2i_cons.

  + unfold branch_rel.
    exists lb, s, (output1 a la s st_end), st_end.
    repeat split; try reflexivity.

    unfold output1.
    apply ps_base.
    constructor.

  + apply f2i_nil.
  constructor.
intros.
apply copathsel_singleton in H.
destruct H as [Hl [Hs HU]].
subst l s0 U'.

exists (output1 a la s st_end).
split.

- (* Anticipate the receive through an output *)
  unfold output1, input1.
  eapply pr_through_send.

  apply f2i_cons.

  + unfold branch_rel.
    exists la, s, (input1 a lb s st_end), st_end.
    repeat split; try reflexivity.

    unfold input1.
    apply pr_base.
    constructor.

  + apply f2i_nil.

- apply R2_output.

unfold subtype_directR.
simpl.
repeat split; try easy.

- (* Clause 2: Recvs *)
  unfold input1.
  apply recvs_base.
  discriminate.

- (* Clause 4: Match the input *)
  intros l s0 U' Hsel.

  apply copathsel_singleton in Hsel.
  destruct Hsel as [Hl [Hs HU]].
  subst l s0 U'.

  exists st_end.
  split.

  + (* Direct receive *)
    unfold input1.
    apply pr_base.
    constructor.

  + (* Continuations are related *)
    apply R2_end.
unfold subtype_directR.
simpl.
repeat split; try easy.

- (* Clause 1: Match the output *)
  intros l s0 T' Hsel.

  apply copathsel_singleton in Hsel.
  destruct Hsel as [Hl [Hs HT]].
  subst l s0 T'.

  exists st_end.
  split.

  + (* Direct send *)
    unfold output1.
    apply ps_base.
    constructor.

  + (* Continuations are related *)
    apply R2_end.

- (* Clause 3: Sends *)
  unfold output1.
  apply sends_base.
  discriminate.
constructor; easy.
Qed.

Lemma R2_sim_sound :
  forall a la lb s T U,
    R2_sim a la lb s T U ->
    subtype_direct T U.
Proof.
  intros a la lb s T U Hsim.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := R2_sim a la lb s)
    (r := bot2).

  - intros rr INCr INCl x y Hxy.
    pfold.

eapply subtype_directR_mon
  with (r := R2_sim a la lb s).

apply R2_sim_step.
exact Hxy.
    + intros x' y' Hrel.
      right.
      apply INCl.
      exact Hrel.

  - exact Hsim.
Qed.

Lemma test_R2 :
  forall a la lb s,
    subtype_direct
      (output1 a la s
        (input1 a lb s st_end))
      (input1 a lb s
        (output1 a la s st_end)).
Proof.
  intros a la lb s.
  eapply R2_sim_sound.
  apply R2_initial.
Qed.

(* ============================================================ *)
(* R2 — Output/output anticipation                               *)
(* ============================================================ *)

Inductive R2_out_sim
  (a b la lb : string)
  (s : sort)
  : st -> st -> Prop :=

| R2_out_initial :
    R2_out_sim a b la lb s
      (output1 a la s (output1 b lb s st_end))
      (output1 b lb s (output1 a la s st_end))

| R2_out_left :
    R2_out_sim a b la lb s
      (output1 b lb s st_end)
      (output1 b lb s st_end)

| R2_out_right :
    R2_out_sim a b la lb s
      (output1 a la s st_end)
      (output1 a la s st_end)

| R2_out_end :
    R2_out_sim a b la lb s st_end st_end.

Lemma R2_out_sim_step :
  forall a b la lb s T U,
    a <> b ->
    R2_out_sim a b la lb s T U ->
    subtype_directR (R2_out_sim a b la lb s) T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  inversion Hsim; subst; clear Hsim.
  - (* R2_out_initial *)
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the output to a *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (output1 b lb s st_end).
      split.

      * (* Anticipate output a through output b *)
        unfold output1.
        eapply ps_through_send.

        -- (* a <> b *)
           exact Hneq.

        -- (* BranchSubsetLabel *)
           unfold BranchSubsetLabel.
           intros l0 s1 U0 Hsel0.

           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HU]].
           subst l0 s1 U0.

           exists (output1 a la s st_end).
           split.

           ++ constructor.

           ++ apply ps_base.
              constructor.

        -- (* Nonempty resulting choice *)
           discriminate.

      * (* Continuation belongs to R2_out_sim *)
        apply R2_out_left.

    + (* Clause 3: Sends b *)
      unfold output1.

      eapply sends_through_send.

      * discriminate.

      * intros l s0 T' Hsel.

        apply copathsel_singleton in Hsel.
        destruct Hsel as [Hl [Hs HT]].
        subst l s0 T'.

        apply sends_base.
        discriminate.
  - (* R2_out_left *)
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Direct output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists st_end.
      split.

      * unfold output1.
        apply ps_base.
        constructor.

      * apply R2_out_end.

    + (* Clause 3: Sends b *)
      unfold output1.
      apply sends_base.
      discriminate.
  - (* R2_out_right *)
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Direct output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists st_end.
      split.

      * unfold output1.
        apply ps_base.
        constructor.

      * apply R2_out_end.

    + (* Clause 3: Sends a *)
      unfold output1.
      apply sends_base.
      discriminate.
constructor; easy.
Qed.

Lemma R2_out_sim_sound :
  forall a b la lb s T U,
    a <> b ->
    R2_out_sim a b la lb s T U ->
    subtype_direct T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := R2_out_sim a b la lb s)
    (r := bot2).

  - intros rr INCr INCl x y Hxy.
    pfold.

    pose proof
      (R2_out_sim_step a b la lb s x y Hneq Hxy)
      as Hstep.

    eapply subtype_directR_mon.
    + exact Hstep.
    + intros x' y' Hrel.
      right.
      apply INCl.
      exact Hrel.

  - exact Hsim.
Qed.

Lemma test_R2_outputs :
  forall a b la lb s,
    a <> b ->
    subtype_direct
      (output1 a la s
        (output1 b lb s st_end))
      (output1 b lb s
        (output1 a la s st_end)).
Proof.
  intros a b la lb s Hneq.

  eapply R2_out_sim_sound.
  - exact Hneq.
  - apply R2_out_initial.
Qed.

Lemma permitted_send_same_participant :
  forall p l s l0 s0 T U,
    permitted_send p l s
      (output1 p l0 s0 T) U ->
    l = l0.
Proof.
  intros p l s l0 s0 T U Hsend.
  unfold output1 in Hsend.
  remember (st_send p (cocons (l0, s0, T) conil))
    as X eqn:HX.
  induction Hsend.
  - (* ps_base *)
    inversion HX; subst.
    apply copathsel_singleton in H.
    destruct H as [Hl [Hs HT]].
    exact Hl.

  - (* ps_through_send *)
    inversion HX; subst.
    contradiction.

  - (* ps_through_receive *)
    discriminate.
Qed.


Lemma test_R2_same_recipient_invalid :
  forall a la lb s,
    la <> lb ->
    ~ subtype_direct
        (output1 a la s
          (output1 a lb s st_end))
        (output1 a lb s
          (output1 a la s st_end)).
Proof.
  intros a la lb s Hneq Hsub.

  unfold subtype_direct in Hsub.
  punfold Hsub.
  unfold subtype_directR in Hsub.
  simpl in Hsub.

  destruct Hsub as [Houtputs _].

  assert (Hsel :
    copathsel la s
      (cocons
        (la, s, output1 a lb s st_end)
        conil)
      (output1 a lb s st_end)).
  {
    constructor.
  }

  specialize (Houtputs la s
    (output1 a lb s st_end) Hsel).

  destruct Houtputs as [U' [Hsend _]].

  unfold output1 in Hsend.

  pose proof
    (permitted_send_same_participant
      a la s lb s
      (output1 a la s st_end)
      U' Hsend)
    as Heq.

  contradiction.
  apply subtype_directR_mon.
Qed.

