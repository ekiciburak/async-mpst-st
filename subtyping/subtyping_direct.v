From Coq Require Import String List Relations.Relation_Definitions.

From Paco Require Import paco.

Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts.
Import ListNotations.

Inductive Forall2Ind {a b : Type} (P : a -> b -> Prop): coseq a -> coseq b -> Prop :=
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

Inductive R1_general_sim
  (a b la lb : string)
  (s : sort)
  : st -> st -> Prop :=

| R1_gen_initial :
    forall T U,
      subtype_direct T U ->
      R1_general_sim a b la lb s
        (input1 a la s (input1 b lb s T))
        (input1 b lb s (input1 a la s U))

| R1_gen_cont :
    forall T U,
      subtype_direct T U ->
      R1_general_sim a b la lb s
        (input1 a la s T)
        (input1 a la s U)

| R1_gen_existing :
    forall T U,
      subtype_direct T U ->
      R1_general_sim a b la lb s T U.

Lemma subtype_direct_input_prefix :
  forall a la s T U,
    subtype_direct T U ->
    subtype_direct
      (input1 a la s T)
      (input1 a la s U).
Proof.
  intros a la s T U Hsub.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := fun X Y =>
       X = input1 a la s T /\
       Y = input1 a la s U)
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 2: Recvs *)
      unfold input1.
      apply recvs_base.
      discriminate.

    + (* Clause 4: Match the input *)
      intros l s0 U' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HU]].
      subst l s0 U'.

      exists T.
      split.

      * unfold input1.
        apply pr_base.
        constructor.

      * left.
       unfold subtype_direct in Hsub.
       eapply paco2_mon.
       - exact Hsub.
       - intros x y Hbot.
         destruct Hbot.
    - split; reflexivity.
Qed.

Lemma R1_general :
  forall a b la lb s T U,
    a <> b ->
    subtype_direct T U ->
    subtype_direct
      (input1 a la s (input1 b lb s T))
      (input1 b lb s (input1 a la s U)).
Proof.
  intros a b la lb s T U Hneq Hsub.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := fun X Y =>
       X = input1 a la s (input1 b lb s T) /\
       Y = input1 b lb s (input1 a la s U))
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 2: Recvs a *)
      unfold input1.
      eapply recvs_through_receive.
      * discriminate.
      * intros l s0 V Hsel.
        apply copathsel_singleton in Hsel.
        destruct Hsel as [Hl [Hs HV]].
        subst l s0 V.
        apply recvs_base.
        discriminate.

    + (* Clause 4: Match the input from b *)
      intros l s0 U' Hsel.
      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HU]].
      subst l s0 U'.

      exists (input1 a la s T).
      split.

      * (* Anticipate receive b through receive a *)
        unfold input1.
        eapply pr_through_receive. easy.

        -- unfold BranchSubsetLabel.
           intros l0 s1 V Hsel0.
           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HV]].
           subst l0 s1 V.

           exists (input1 b lb s T).
           split.

           ++ constructor.

           ++ unfold input1.
              apply pr_base.
              constructor.

        -- discriminate.

      * (* Continuations are already subtypes *)
        left.

        assert (Hprefix :
          subtype_direct
            (input1 a la s T)
            (input1 a la s U)).
        {
          apply subtype_direct_input_prefix.
          exact Hsub.
        }

        unfold subtype_direct in Hprefix.

        eapply paco2_mon.
        -- exact Hprefix.
        -- intros x y Hbot.
           destruct Hbot.

  - split; reflexivity.
Qed.

Lemma subtype_direct_output_prefix :
  forall a la s T U,
    subtype_direct T U ->
    subtype_direct
      (output1 a la s T)
      (output1 a la s U).
Proof.
  intros a la s T U Hsub.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := fun X Y =>
       X = output1 a la s T /\
       Y = output1 a la s U)
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists U.
      split.

      * (* Direct permitted send *)
        unfold output1.
        apply ps_base.
        constructor.

      * (* Existing continuation subtyping *)
        left.
        unfold subtype_direct in Hsub.

        eapply paco2_mon.
        -- exact Hsub.
        -- intros x y Hbot.
           destruct Hbot.

    + (* Clause 3: Required sending *)
      unfold output1.
      apply sends_base.
      discriminate.

  - split; reflexivity.
Qed.

Lemma R2_output_input_general :
  forall a b la lb s T U,
    subtype_direct T U ->
    subtype_direct
      (output1 a la s (input1 b lb s T))
      (input1 b lb s (output1 a la s U)).
Proof.
  intros a b la lb s T U Hsub.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := fun X Y =>
       X = output1 a la s (input1 b lb s T) /\
       Y = input1 b lb s (output1 a la s U))
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the subtype's output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (input1 b lb s U).
      split.

      * (* Anticipate output through input *)
        unfold input1, output1.
        eapply ps_through_receive.

        apply f2i_cons.

        -- unfold branch_rel.
           exists lb, s, (output1 a la s U), U.
           repeat split; try reflexivity.

           unfold output1.
           apply ps_base.
           constructor.

        -- apply f2i_nil.

      * (* Input-prefixed continuations are subtypes *)
        left.

        assert (Hprefix :
          subtype_direct
            (input1 b lb s T)
            (input1 b lb s U)).
        {
          apply subtype_direct_input_prefix.
          exact Hsub.
        }

        unfold subtype_direct in Hprefix.

        eapply paco2_mon.
        -- exact Hprefix.
        -- intros x y Hbot.
           destruct Hbot.

    + (* Clause 4: Match the supertype's input *)
      intros l s0 U' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HU]].
      subst l s0 U'.

      exists (output1 a la s T).
      split.

      * (* Anticipate input through output *)
        unfold input1, output1.
        eapply pr_through_send.

        apply f2i_cons.

        -- unfold branch_rel.
           exists la, s, (input1 b lb s T), T.
           repeat split; try reflexivity.

           unfold input1.
           apply pr_base.
           constructor.

        -- apply f2i_nil.

      * (* Output-prefixed continuations are subtypes *)
        left.

        assert (Hprefix :
          subtype_direct
            (output1 a la s T)
            (output1 a la s U)).
        {
          apply subtype_direct_output_prefix.
          exact Hsub.
        }

        unfold subtype_direct in Hprefix.

        eapply paco2_mon.
        -- exact Hprefix.
        -- intros x y Hbot.
           destruct Hbot.

  - split; reflexivity.
Qed.

Lemma R2_output_output_general :
  forall a b la lb s T U,
    a <> b ->
    subtype_direct T U ->
    subtype_direct
      (output1 a la s (output1 b lb s T))
      (output1 b lb s (output1 a la s U)).
Proof.
  intros a b la lb s T U Hneq Hsub.
  unfold subtype_direct.

  eapply paco2_acc with
    (l := fun X Y =>
       X = output1 a la s (output1 b lb s T) /\
       Y = output1 b lb s (output1 a la s U))
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_directR.
    simpl.
    repeat split; try easy.

    + (* Match output to a *)
      intros l s0 T' Hsel.
      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (output1 b lb s U).
      split.

      * (* Anticipate output a through output b *)
        unfold output1.
        eapply ps_through_send.

        -- exact Hneq.

        -- unfold BranchSubsetLabel.
           intros l0 s1 V Hsel0.
           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HV]].
           subst l0 s1 V.

           exists (output1 a la s U).
           split.
           ++ constructor.
           ++ unfold output1.
              apply ps_base.
              constructor.

        -- discriminate.

      * (* Continuation subtyping *)
        left.

        assert (Hprefix :
          subtype_direct
            (output1 b lb s T)
            (output1 b lb s U)).
        {
          apply subtype_direct_output_prefix.
          exact Hsub.
        }

        unfold subtype_direct in Hprefix.
        eapply paco2_mon.
        -- exact Hprefix.
        -- intros x y Hbot.
           destruct Hbot.

    + (* Sends b *)
      unfold output1.
      eapply sends_through_send.

      * discriminate.

      * intros l s0 V Hsel.
        apply copathsel_singleton in Hsel.
        destruct Hsel as [Hl [Hs HV]].
        subst l s0 V.

        apply sends_base.
        discriminate.

  - split; reflexivity.
Qed.

Inductive finite_coseq {A : Type} : coseq A -> Prop :=
| finite_conil :
    finite_coseq conil
| finite_cocons :
    forall x xs,
      finite_coseq xs ->
      finite_coseq (cocons x xs).

CoFixpoint list_to_coseq
  {a b : Type}
  (f : a -> b)
  (xs : list a) : coseq b :=
  match xs with
  | nil => conil
  | x :: ys => cocons (f x) (list_to_coseq f ys)
  end.

Lemma list_to_coseq_finite :
  forall (a b: Type) (f : a -> b) xs,
    finite_coseq (list_to_coseq f xs).
Proof.
  intros a b f xs.
  induction xs as [|x xs IH].
  - rewrite (coseq_eq (list_to_coseq f nil)).
    simpl.
    constructor.
  - rewrite (coseq_eq (list_to_coseq f (x :: xs))).
    simpl.
    constructor.
    exact IH.
Qed.

CoFixpoint branches_of_list
  (xs : list (string * sort * local))
  : coseq (string * sort * st) :=
  match xs with
  | [] => conil
  | (lbl, sr, t) :: ys =>
      cocons (lbl, sr, lt2st t) (branches_of_list ys)
  end.

Lemma branches_of_list_finite :
  forall xs,
    finite_coseq (branches_of_list xs).
Proof.
  induction xs as [| [[lbl sr] t] ys IH].
  - rewrite (coseq_eq (branches_of_list [])).
    simpl.
    constructor.
  - rewrite (coseq_eq
      (branches_of_list ((lbl, sr, t) :: ys))).
    simpl.
    constructor.
    exact IH.
Qed.

Lemma lt2st_branches_finite :
  forall L p xs,
    lt2st L = st_send p xs ->
    finite_coseq xs.
Proof.
  intros L p xs H.

  rewrite (st_eq (lt2st L)) in H.
  simpl in H.

  destruct (full_unf L) eqn:Hunf;
    try discriminate.
inversion H; subst; clear H.
clear Hunf.
induction l as [| [[lbl sr] t] tl IH].
-
- rewrite (coseq_eq
    ((cofix next (xs : list (string * sort * local))
        : coseq (string * sort * st) :=
        match xs with
        | [] => conil
        | (l1,s1,t1)::ys =>
            cocons (l1,s1,lt2st t1) (next ys)
        end) [])).
  simpl.
  constructor.
  rewrite(coseq_eq(
  ((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
      match xs with
      | [] => conil
      | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
      end) ((lbl, sr, t) :: tl))
  )). cbn. constructor.
  apply IH.
Qed.

Lemma lt2st_receive_branches_finite :
  forall L p xs,
    lt2st L = st_receive p xs ->
    finite_coseq xs.
Proof.
  intros L p xs H.

  rewrite (st_eq (lt2st L)) in H.
  simpl in H.

  destruct (full_unf L) eqn:Hunf;
    try discriminate.
inversion H; subst; clear H.
clear Hunf.
induction l as [| [[lbl sr] t] tl IH].
-
- rewrite (coseq_eq
    ((cofix next (xs : list (string * sort * local))
        : coseq (string * sort * st) :=
        match xs with
        | [] => conil
        | (l1,s1,t1)::ys =>
            cocons (l1,s1,lt2st t1) (next ys)
        end) [])).
  simpl.
  constructor.
  rewrite(coseq_eq(
  ((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
      match xs with
      | [] => conil
      | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
      end) ((lbl, sr, t) :: tl))
  )). cbn. constructor.
  apply IH.
Qed.


Lemma lt2st_send_branch :
  forall L p xs l s T,
    lt2st L = st_send p xs ->
    copathsel l s xs T ->
    exists L',
      T = lt2st L'.
Proof.
  intros L p xs lbl sr T Htree Hsel.

  rewrite (st_eq (lt2st L)) in Htree.
  simpl in Htree.

  destruct (full_unf L) eqn:Hunf;
    try discriminate.

  inversion Htree; subst; clear Htree.
    clear Hunf.
  revert lbl sr T Hsel.
  induction l as [| [[lbl0 sr0] t0] tl IH];
    intros lbl sr T Hsel.
  - (* Empty source list *)
    rewrite (coseq_eq
      ((cofix next xs :=
          match xs with
          | [] => conil
          | (l1, s1, t1) :: ys =>
              cocons (l1, s1, lt2st t1) (next ys)
          end) [])) in Hsel.
    simpl in Hsel.
    inversion Hsel.
rewrite (coseq_eq
  ((cofix next (xs : list (string * sort * local))
      : coseq (string * sort * st) :=
      match xs with
      | [] => conil
      | (l1, s1, t1) :: ys =>
          cocons (l1, s1, lt2st t1) (next ys)
      end) ((lbl0, sr0, t0) :: tl))) in Hsel.
simpl in Hsel.
inversion Hsel; subst.
exists t0.
reflexivity.
- apply IH with (lbl := lbl) (sr := sr).
  assumption.
inversion Hsel; subst.

- exists t0.
  reflexivity.

- eapply IH.
  eassumption.

- eapply IH.
  eassumption.
Qed.

Lemma lt2st_receive_branch :
  forall L p xs l s T,
    lt2st L = st_receive p xs ->
    copathsel l s xs T ->
    exists L',
      T = lt2st L'.
Proof.
  intros L p xs lbl sr T Htree Hsel.

  rewrite (st_eq (lt2st L)) in Htree.
  simpl in Htree.

  destruct (full_unf L) eqn:Hunf;
    try discriminate.

  inversion Htree; subst; clear Htree.
    clear Hunf.
  revert lbl sr T Hsel.
  induction l as [| [[lbl0 sr0] t0] tl IH];
    intros lbl sr T Hsel.
  - (* Empty source list *)
    rewrite (coseq_eq
      ((cofix next xs :=
          match xs with
          | [] => conil
          | (l1, s1, t1) :: ys =>
              cocons (l1, s1, lt2st t1) (next ys)
          end) [])) in Hsel.
    simpl in Hsel.
    inversion Hsel.
rewrite (coseq_eq
  ((cofix next (xs : list (string * sort * local))
      : coseq (string * sort * st) :=
      match xs with
      | [] => conil
      | (l1, s1, t1) :: ys =>
          cocons (l1, s1, lt2st t1) (next ys)
      end) ((lbl0, sr0, t0) :: tl))) in Hsel.
simpl in Hsel.
inversion Hsel; subst.
exists t0.
reflexivity.
- apply IH with (lbl := lbl) (sr := sr).
  assumption.
inversion Hsel; subst.

- exists t0.
  reflexivity.

- eapply IH.
  eassumption.

- eapply IH.
  eassumption.
Qed.

Definition finitely_branchingR
  (R : st -> Prop)
  (T : st) : Prop :=
  match T with
  | st_end => True
  | st_send p xs =>
      finite_coseq xs /\
      (forall l s U,
        copathsel l s xs U -> R U)
  | st_receive p xs =>
      finite_coseq xs /\
      (forall l s U,
        copathsel l s xs U -> R U)
  end.

Definition translated_tree (T : st) : Prop :=
  exists L, T = lt2st L.

Lemma translated_tree_step :
  forall T,
    translated_tree T ->
    finitely_branchingR translated_tree T.
Proof.
  intros T [L ->].

  unfold finitely_branchingR.

  rewrite (st_eq (lt2st L)).
  simpl.

  destruct (full_unf L) eqn:Hunf;
    try easy.

  - (* Receive *)
    split.
eapply lt2st_branches_finite.
rewrite (st_eq (lt2st L)).
simpl.
rewrite Hunf.
reflexivity.

    + intros l2 s2 U Hsel.
      unfold translated_tree.
eapply lt2st_send_branch with (L := L) (p := s).
- rewrite (st_eq (lt2st L)).
  simpl.
  rewrite Hunf.
  reflexivity.
- exact Hsel.
split.

- (* Finite receive branches *)
  eapply lt2st_receive_branches_finite
    with (L := L) (p := s).

  rewrite (st_eq (lt2st L)).
  simpl.
  rewrite Hunf.
  reflexivity.

- (* Every continuation is a translated tree *)
  intros lbl sr U Hsel.

  unfold translated_tree.

  eapply lt2st_receive_branch
    with (L := L) (p := s).

  + rewrite (st_eq (lt2st L)).
    simpl.
    rewrite Hunf.
    reflexivity.

  + exact Hsel.
Qed.

Definition finitely_branchingC (T : st) : Prop :=
  paco1 finitely_branchingR bot1 T.

Lemma finitely_branchingR_mon :
  monotone1 finitely_branchingR.
Proof.
  unfold monotone1.
  intros T R R' Hinc H.

  unfold finitely_branchingR in *.
  destruct T; simpl in *; auto.

  - destruct Hinc as [Hfin Hall].
    split.
    + exact Hfin.
    + intros l s0 U Hsel.
      apply H.
      apply Hall with (l := l) (s := s0).
      exact Hsel.

  - destruct Hinc as [Hfin Hall].
    split.
    + exact Hfin.
    + intros l s0 U Hsel.
      apply H.
      apply Hall with (l := l) (s := s0).
      exact Hsel.
Qed.

Lemma lt2st_finitely_branching :
  forall L,
    finitely_branchingC (lt2st L).
Proof.
  intro L.
  unfold finitely_branchingC.

  eapply paco1_acc with
    (l := translated_tree)
    (r := bot1).

  - intros rr INCr INCl T Htrans.

    pfold.

    eapply finitely_branchingR_mon.

    + apply translated_tree_step.
      exact Htrans.

    + intros U HU.
      right.
      apply INCl.
      exact HU.

  - unfold translated_tree.
    exists L.
    reflexivity.
Qed.

Fixpoint permitted_send_at
  (n : nat)
  (p l : string)
  (s : sort)
  (T U : st) : Prop :=

  match n with

  | O =>
      exists xs,
        T = st_send p xs /\
        copathsel l s xs U

  | S n' =>
      (* Direct send *)
      (exists xs,
        T = st_send p xs /\
        copathsel l s xs U)

      \/

      (* Anticipation through another output *)
      (exists q xs ys,
        p <> q /\
        T = st_send q xs /\
        U = st_send q ys /\
        ys <> conil /\
        BranchSubsetLabel
          (permitted_send_at n' p l s)
          xs ys)

      \/

      (* Anticipation through an input *)
      (exists q xs ys,
        T = st_receive q xs /\
        U = st_receive q ys /\
        Forall2Ind
          (branch_rel
            (permitted_send_at n' p l s))
          xs ys)
  end.

Lemma BranchSubsetLabel_mon :
  forall R R' xs ys,
    (forall T U, R T U -> R' T U) ->
    BranchSubsetLabel R xs ys ->
    BranchSubsetLabel R' xs ys.
Proof.
  intros R R' xs ys Hinc Hsub.
  unfold BranchSubsetLabel in *.
  intros l s U Hsel.
  destruct (Hsub l s U Hsel) as [T [HselT HR]].
  exists T.
  split.
  - exact HselT.
  - apply Hinc.
    exact HR.
Qed.

Lemma Forall2Ind_mon :
  forall (a b : Type) (P Q : a -> b -> Prop) xs ys,
    (forall x y, P x y -> Q x y) ->
    Forall2Ind P xs ys ->
    Forall2Ind Q xs ys.
Proof.
  intros a b P Q xs ys Hinc Hrel.
  induction Hrel.
  - constructor.
  - constructor.
    + apply Hinc.
      assumption.
    + exact IHHrel.
Qed.

Lemma permitted_send_at_succ :
  forall n p l s T U,
    permitted_send_at n p l s T U ->
    permitted_send_at (S n) p l s T U.
Proof.
  induction n as [|n IH];
    intros p l s T U Hperm.

  - (* Depth 0 *)
    simpl in Hperm.
    simpl.
    left.
    exact Hperm.

  - (* Depth S n *)
    simpl in Hperm.
    simpl.

    destruct Hperm as
      [Hbase | [Hsend | Hrecv]].

    + (* Direct send *)
      left.
      exact Hbase.

    + (* Anticipation through output *)
      right. left.

      destruct Hsend as
        [q [xs [ys
          [Hneq [HT [HU [Hnonempty Hbranches]]]]]]].

      exists q, xs, ys.
      repeat split;
        try assumption.

      eapply BranchSubsetLabel_mon.
      * intros T0 U0 Hstep.
        apply IH.
        exact Hstep.
      * exact Hbranches.

    + (* Anticipation through input *)
      right. right.

      destruct Hrecv as
        [q [xs [ys [HT [HU Hbranches]]]]].

      exists q, xs, ys.
      repeat split;
        try assumption.

assert (Hinc :
  forall x y,
    branch_rel (permitted_send_at n p l s) x y ->
    branch_rel (permitted_send_at (S n) p l s) x y).
{
  intros x y Hbranch.
  unfold branch_rel in *.

  destruct Hbranch as
    [lbl [sr [T0 [U0 [Hx [Hy Hstep]]]]]].

  exists lbl, sr, T0, U0.
  repeat split; try assumption.

  apply IH.
  exact Hstep.
}

exact
  (Forall2Ind_mon
    _ _
    (branch_rel (permitted_send_at n p l s))
    (branch_rel (permitted_send_at (S n) p l s))
    xs ys
    Hinc Hbranches).
Qed.

Lemma permitted_send_at_le :
  forall n m p l s T U,
    n <= m ->
    permitted_send_at n p l s T U ->
    permitted_send_at m p l s T U.
Proof.
  intros n m p l s T U Hle Hperm.
  induction Hle.
  - exact Hperm.
  - apply permitted_send_at_succ.
    exact IHHle.
Qed.

From Coq Require Import Arith.PeanoNat.

Lemma permitted_send_at_sound :
  forall n p l s T U,
    permitted_send_at n p l s T U ->
    permitted_send p l s T U.
Proof.
  induction n as [|n IH];
    intros p l s T U Hperm.

  - (* Depth 0: direct send *)
    simpl in Hperm.

    destruct Hperm as [xs [HT Hsel]].
    subst T.

    apply ps_base.
    exact Hsel.

  - (* Depth S n *)
    simpl in Hperm.

    destruct Hperm as
      [Hbase | [Hsend | Hrecv]].

    + (* Direct send *)
      destruct Hbase as [xs [HT Hsel]].
      subst T.

      apply ps_base.
      exact Hsel.

    + (* Anticipation through another output *)
      destruct Hsend as
        [q [xs [ys
          [Hneq [HT [HU [Hnonempty Hbranches]]]]]]].

      subst T U.

      eapply ps_through_send.
      * exact Hneq.

      * eapply BranchSubsetLabel_mon.
        -- intros T0 U0 Hstep.
           apply IH.
           exact Hstep.
        -- exact Hbranches.

      * exact Hnonempty.

    + (* Anticipation through an input *)
      destruct Hrecv as
        [q [xs [ys [HT [HU Hbranches]]]]].

      subst T U.

      eapply ps_through_receive.

      assert (Hinc :
        forall x y,
          branch_rel (permitted_send_at n p l s) x y ->
          branch_rel (permitted_send p l s) x y).
      {
        intros x y Hbranch.
        unfold branch_rel in *.

        destruct Hbranch as
          [lbl [sr [T0 [U0 [Hx [Hy Hstep]]]]]].

        exists lbl, sr, T0, U0.
        repeat split; try assumption.

        apply IH.
        exact Hstep.
      }

      exact
        (Forall2Ind_mon
          _ _
          (branch_rel (permitted_send_at n p l s))
          (branch_rel (permitted_send p l s))
          xs ys
          Hinc Hbranches).
Qed.

Lemma Forall2Ind_uniform_bound :
  forall p l s xs ys,
    Forall2Ind
      (branch_rel
        (fun T U =>
          exists n, permitted_send_at n p l s T U))
      xs ys ->
    exists n,
      Forall2Ind
        (branch_rel (permitted_send_at n p l s))
        xs ys.
Proof.
  intros p l s xs ys Hrel.
  induction Hrel.

  - (* Empty sequences *)
    exists 0.
    constructor.

  - (* Nonempty sequences *)
    unfold branch_rel in H.

    destruct H as
      [lbl [sr [T0 [U0
        [Hx [Hy [n Hstep]]]]]]].

    destruct IHHrel as [m Htail].

    exists (Nat.max n m).

    apply f2i_cons.

    + (* Head branch *)
      unfold branch_rel.

      exists lbl, sr, T0, U0.
      repeat split; try assumption.

      apply permitted_send_at_le with (n := n).
      * apply Nat.le_max_l.
      * exact Hstep.

    + 
eapply (Forall2Ind_mon
  _ _
  (branch_rel (permitted_send_at m p l s))
  (branch_rel (permitted_send_at (Nat.max n m) p l s))
  xs ys).

- intros x0 y0 Hbranch.
  unfold branch_rel in *.

  destruct Hbranch as
    [lbl0 [sr0 [T1 [U1
      [Hx0 [Hy0 Hstep0]]]]]].

  exists lbl0, sr0, T1, U1.
  repeat split; try assumption.

  eapply permitted_send_at_le.
  + apply Nat.le_max_r.
  + exact Hstep0.

- exact Htail.
Qed.

Lemma BranchSubsetLabel_at_le :
  forall n m p l s xs ys,
    n <= m ->
    BranchSubsetLabel
      (permitted_send_at n p l s) xs ys ->
    BranchSubsetLabel
      (permitted_send_at m p l s) xs ys.
Proof.
  intros n m p l s xs ys Hle Hsub.

  eapply BranchSubsetLabel_mon.
  - intros T U Hstep.
    eapply permitted_send_at_le.
    + exact Hle.
    + exact Hstep.
  - exact Hsub.
Qed.

Inductive coseq_member {A : Type} (x : A) : coseq A -> Prop :=
| cm_here :
    forall xs,
      coseq_member x (cocons x xs)

| cm_there :
    forall y xs,
      coseq_member x xs ->
      coseq_member x (cocons y xs).

Lemma copathsel_member :
  forall l s xs T,
    copathsel l s xs T ->
    coseq_member (l, s, T) xs.
Proof.
  intros l s xs T Hsel.
  induction Hsel.
  - constructor.
  - apply cm_there.
    exact IHHsel.
  - apply cm_there.
    exact IHHsel.
Qed.

Definition selectable_member
  (xs : coseq (string * sort * st))
  (x : string * sort * st) : Prop :=
  exists (l : string) (s : sort) (T : st),
    x = (l, s, T) /\
    copathsel l s xs T.

Lemma finite_coseq_member_bound :
  forall (A : Type) (xs : coseq A)
         (P : A -> nat -> Prop),
    finite_coseq xs ->
    (forall x,
       coseq_member x xs ->
       exists n : nat, P x n) ->
    (forall x n m,
       n <= m ->
       P x n ->
       P x m) ->
    exists bound : nat,
      forall x,
        coseq_member x xs ->
        P x bound.
Proof.
  intros A xs P Hfin.
  induction Hfin as [| hd tl Hfin IH];
    intros Hex Hmono.

  - (* Empty sequence *)
    exists 0.
    intros x Hmem.
    inversion Hmem.

  - (* Nonempty sequence *)

    assert (Hhead : exists n : nat, P hd n).
    {
      apply Hex.
      constructor.
    }

    destruct Hhead as [n Hhead].

    assert (Htail :
      forall x,
        coseq_member x tl ->
        exists n : nat, P x n).
    {
      intros x Hmem.
      apply Hex.
      apply cm_there.
      exact Hmem.
    }

    destruct (IH Htail Hmono) as [m Hbound].

    exists (Nat.max n m).

    intros x Hmem.
    inversion Hmem; subst.

    + (* Head *)
      eapply Hmono.
      * apply Nat.le_max_l.
      * exact Hhead.

    + (* Tail *)
      eapply Hmono.
      * apply Nat.le_max_r.
      * apply Hbound.
        assumption.
Qed.

From Coq Require Import Classical.

Lemma finite_coseq_selectable_bound :
  forall
    (xs : coseq (string * sort * st))
    (P : string * sort * st -> nat -> Prop),

    finite_coseq xs ->

    (forall x,
      selectable_member xs x ->
      exists n : nat, P x n) ->

    (forall x n m,
      n <= m ->
      P x n ->
      P x m) ->

    exists (bound : nat),
      forall x,
        selectable_member xs x ->
        P x bound.
Proof.
  intros xs P Hfin Hex Hmono.

  (* Extend P to all members, assigning a default
     bound to non-selectable branches. *)

  set (Q := fun x n =>
    selectable_member xs x -> P x n).

  assert (HexQ :
    forall x,
      coseq_member x xs ->
      exists n : nat, Q x n).
  {
    intros x Hmem.
    unfold Q.

    destruct (classic (selectable_member xs x))
      as [Hsel | Hnot].

    - destruct (Hex x Hsel) as [n Hn].
      exists n.
      intros _.
      exact Hn.

    - exists 0.
      intros Hsel.
      contradiction.
  }

  assert (HmonoQ :
    forall x n m,
      n <= m ->
      Q x n ->
      Q x m).
  {
    intros x n m Hle HQ Hsel.
    unfold Q in *.

    eapply Hmono.
    - exact Hle.
    - apply HQ.
      exact Hsel.
  }

  destruct
    (finite_coseq_member_bound
      _ xs Q Hfin HexQ HmonoQ)
    as [bound Hbound].

  exists bound.

  intros x Hsel.

  apply Hbound.

  - (* Selectable branches are members *)
    unfold selectable_member in Hsel.
    destruct Hsel as
      [lbl [sr [T [Hx Hpath]]]].
    subst x.

    eapply copathsel_member.
    exact Hpath.

  - exact Hsel.
Qed.

Lemma BranchSubsetLabel_uniform_bound :
  forall p l s xs ys,
    finite_coseq ys ->
    BranchSubsetLabel
      (fun T U =>
        exists n, permitted_send_at n p l s T U)
      xs ys ->
    exists bound,
      BranchSubsetLabel
        (permitted_send_at bound p l s)
        xs ys.
Proof.
  intros p l s xs ys Hfin Hsub.

  unfold BranchSubsetLabel in Hsub.

  (* Property of a selectable branch at depth n *)
  set (P := fun (x : string * sort * st) (n : nat) =>
    exists lbl sr U T,
      x = (lbl, sr, U) /\
      copathsel lbl sr xs T /\
      permitted_send_at n p l s T U).

  (* Every selectable branch has some bound. *)
  assert (Hex :
    forall x,
      selectable_member ys x ->
      exists n, P x n).
  {
    intros x Hsel.
    unfold selectable_member in Hsel.

    destruct Hsel as
      [lbl [sr [U [Hx Hpath]]]].

    destruct (Hsub lbl sr U Hpath)
      as [T [HpathT [n Hstep]]].

    exists n.
    unfold P.

    exists lbl, sr, U, T.
    repeat split; assumption.
  }

  (* Increasing the bound preserves P. *)
  assert (Hmono :
    forall x n m,
      n <= m ->
      P x n ->
      P x m).
  {
    intros x n m Hle HP.
    unfold P in *.

    destruct HP as
      [lbl [sr [U [T
        [Hx [Hpath Hstep]]]]]].

    exists lbl, sr, U, T.
    repeat split; try assumption.

    eapply permitted_send_at_le.
    - exact Hle.
    - exact Hstep.
  }

  (* Obtain a uniform bound. *)
  destruct
    (finite_coseq_selectable_bound
      ys P Hfin Hex Hmono)
    as [bound Hbound].

  exists bound.

  unfold BranchSubsetLabel.
  intros lbl sr U Hpath.

  assert (Hsel :
    selectable_member ys (lbl, sr, U)).
  {
    unfold selectable_member.
    exists lbl, sr, U.
    split.
    - reflexivity.
    - exact Hpath.
  }

  specialize (Hbound (lbl, sr, U) Hsel).

  unfold P in Hbound.

  destruct Hbound as
    [lbl0 [sr0 [U0 [T
      [Hx [HpathT Hstep]]]]]].

  inversion Hx; subst.

  exists T.
  split.
  - exact HpathT.
  - exact Hstep.
Qed.

CoFixpoint repeat_branch
  (l : string) (s : sort) (T : st)
  : coseq (string * sort * st) :=
  cocons (l, s, T) (repeat_branch l s T).

Lemma finite_coseq_tail :
  forall (A : Type) (x : A) (xs : coseq A),
    finite_coseq (cocons x xs) ->
    finite_coseq xs.
Proof.
  intros A x xs Hfin.
  inversion Hfin; subst.
  assumption.
Qed.

Lemma repeat_branch_not_finite :
  forall l s T,
    ~ finite_coseq (repeat_branch l s T).
Proof.
  intros l s T Hfin.

  remember (repeat_branch l s T) as xs eqn:Heq.

  induction Hfin.

  - (* Empty sequence *)
    rewrite (coseq_eq (repeat_branch l s T)) in Heq.
    simpl in Heq.
    discriminate.

  - (* Nonempty sequence *)
    rewrite (coseq_eq (repeat_branch l s T)) in Heq.
    simpl in Heq.

    inversion Heq; subst.

    apply IHHfin.
    reflexivity.
Qed.

Lemma repeat_branch_sel :
  forall l s l' s' T U,
    copathsel l' s'
      (repeat_branch l s T) U ->
    l' = l /\ s' = s /\ U = T.
Proof.
  intros l s l' s' T U Hsel.

  remember (repeat_branch l s T) as xs eqn:Heq.

  revert l s T Heq.

  induction Hsel;
    intros l0 s0 T0 Heq;
    rewrite (coseq_eq (repeat_branch l0 s0 T0)) in Heq;
    simpl in Heq;
    inversion Heq; subst.

  - (* Head selection *)
    repeat split; reflexivity.

  - (* Skip because labels differ *)
    destruct (IHHsel l0 s0 T0 eq_refl)
      as [Hl [Hs HT]].

    exfalso.
    apply H.
    symmetry.
    exact Hl.

  - (* Skip because sorts differ *)
    destruct (IHHsel l0 s0 T0 eq_refl)
      as [Hl [Hs HT]].

    exfalso.
    apply H.
    symmetry.
    exact Hs.
Qed.

Lemma BranchSubsetLabel_infinite_example :
  forall l s,
    BranchSubsetLabel
      (fun T U => T = U)
      (cocons (l, s, st_end) conil)
      (repeat_branch l s st_end).
Proof.
  intros l s.
  unfold BranchSubsetLabel.
  intros l' s' U Hsel.

  apply repeat_branch_sel in Hsel.
  destruct Hsel as [Hl [Hs HU]].
  subst.

  exists st_end.
  split.
  - constructor.
  - reflexivity.
Qed.

Lemma BranchSubsetLabel_finite_counterexample :
  forall (l : string) (s : sort),
    exists xs ys,
      finite_coseq xs /\
      BranchSubsetLabel
        (fun T U => T = U) xs ys /\
      ~ finite_coseq ys.
Proof.
  intros l s.

  exists (cocons (l, s, st_end) conil).
  exists (repeat_branch l s st_end).

  repeat split.
  - constructor.
    constructor.
  - apply BranchSubsetLabel_infinite_example.
  - apply repeat_branch_not_finite.
Qed.

Lemma finitely_branchingC_branch_send :
  forall p xs l s T,
    finitely_branchingC (st_send p xs) ->
    copathsel l s xs T ->
    finitely_branchingC T.
Proof.
  intros p xs l s T Hfb Hsel.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [Hfin Hall].

  specialize (Hall l s T Hsel).
unfold finitely_branchingC.
destruct Hall as [Hco | Hbot].
- exact Hco.
- destruct Hbot.
apply finitely_branchingR_mon.
Qed.

Lemma finitely_branchingC_branch_receive :
  forall p xs l s T,
    finitely_branchingC (st_receive p xs) ->
    copathsel l s xs T ->
    finitely_branchingC T.
Proof.
  intros p xs l s T Hfb Hsel.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [Hfin Hall].

  specialize (Hall l s T Hsel).

  unfold finitely_branchingC.
  destruct Hall as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.

  apply finitely_branchingR_mon.
Qed.

Lemma finitely_branchingC_send_finite :
  forall p xs,
    finitely_branchingC (st_send p xs) ->
    finite_coseq xs.
Proof.
  intros p xs Hfb.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [Hfin _].
  exact Hfin.

  apply finitely_branchingR_mon.
Qed.

Lemma finitely_branchingC_receive_finite :
  forall p xs,
    finitely_branchingC (st_receive p xs) ->
    finite_coseq xs.
Proof.
  intros p xs Hfb.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [Hfin _].
  exact Hfin.

  apply finitely_branchingR_mon.
Qed.

Definition permitted_sendF
  (R : string -> string -> sort -> st -> st -> Prop)
  (p l : string) (s : sort)
  (T U : st) : Prop :=

  (* Direct send *)
  (exists xs,
    T = st_send p xs /\
    copathsel l s xs U)

  \/

  (* Anticipation through another output *)
  (exists q xs ys,
    p <> q /\
    T = st_send q xs /\
    U = st_send q ys /\
    ys <> conil /\
    BranchSubsetLabel (R p l s) xs ys)

  \/

  (* Anticipation through an input *)
  (exists q xs ys,
    T = st_receive q xs /\
    U = st_receive q ys /\
    Forall2Ind (branch_rel (R p l s)) xs ys).

Lemma permitted_send_bounded_through_send :
  forall p q l s xs ys,
    p <> q ->
    finite_coseq ys ->
    BranchSubsetLabel
      (fun T U =>
        exists n, permitted_send_at n p l s T U)
      xs ys ->
    ys <> conil ->
    exists n,
      permitted_send_at n p l s
        (st_send q xs)
        (st_send q ys).
Proof.
  intros p q l s xs ys Hneq Hfin Hbranches Hnonempty.

  destruct
    (BranchSubsetLabel_uniform_bound
       p l s xs ys Hfin Hbranches)
    as [n Hbound].

  exists (S n).
  simpl.

  right.
  left.

  exists q, xs, ys.
  repeat split; try assumption.
Qed.

Lemma permitted_send_bounded_through_receive :
  forall p q l s xs ys,
    Forall2Ind
      (branch_rel
        (fun T U =>
          exists n, permitted_send_at n p l s T U))
      xs ys ->
    exists n,
      permitted_send_at n p l s
        (st_receive q xs)
        (st_receive q ys).
Proof.
  intros p q l s xs ys Hbranches.

  destruct
    (Forall2Ind_uniform_bound
       p l s xs ys Hbranches)
    as [n Hbound].

  exists (S n).
  simpl.

  right.
  right.

  exists q, xs, ys.
  repeat split; try reflexivity.

  exact Hbound.
Qed.

From Coq Require Import List.
Import ListNotations.

Definition branch_key : Type :=
  (string * sort)%type.

Definition fresh_branch
  (k : branch_key)
  (seen : list branch_key) : Prop :=
  ~ In k seen.

Inductive permitted_send_mut2 :
  string -> string -> sort -> st -> st -> Prop :=

| psm2_base :
    forall p l s xs T,
      copathsel l s xs T ->
      permitted_send_mut2 p l s
        (st_send p xs) T

| psm2_through_send :
    forall p q l s xs ys,
      p <> q ->
      send_branches_mut2 p l s xs ys nil ->
      ys <> conil ->
      permitted_send_mut2 p l s
        (st_send q xs)
        (st_send q ys)

| psm2_through_receive :
    forall p q l s xs ys,
      send_forall_mut2 p l s xs ys ->
      permitted_send_mut2 p l s
        (st_receive q xs)
        (st_receive q ys)

with send_branches_mut2 :
  string -> string -> sort ->
  coseq (string * sort * st) ->
  coseq (string * sort * st) ->
  list branch_key -> Prop :=

| sbm2_nil :
    forall p l s xs seen,
      send_branches_mut2 p l s
        xs conil seen

| sbm2_fresh :
    forall p l s xs lbl sr U ys seen T,

      fresh_branch (lbl, sr) seen ->

      copathsel lbl sr xs T ->

      permitted_send_mut2 p l s T U ->

      send_branches_mut2 p l s
        xs ys ((lbl, sr) :: seen) ->

      send_branches_mut2 p l s
        xs
        (cocons (lbl, sr, U) ys)
        seen

| sbm2_shadowed :
    forall p l s xs lbl sr U ys seen,

      In (lbl, sr) seen ->

      send_branches_mut2 p l s
        xs ys seen ->

      send_branches_mut2 p l s
        xs
        (cocons (lbl, sr, U) ys)
        seen

with send_forall_mut2 :
  string -> string -> sort ->
  coseq (string * sort * st) ->
  coseq (string * sort * st) -> Prop :=

| sfm2_nil :
    forall p l s,
      send_forall_mut2 p l s conil conil

| sfm2_cons :
    forall p l s lbl sr T U xs ys,

      permitted_send_mut2 p l s T U ->

      send_forall_mut2 p l s xs ys ->

      send_forall_mut2 p l s
        (cocons (lbl, sr, T) xs)
        (cocons (lbl, sr, U) ys).

Scheme send_mut2_ind :=
  Induction for permitted_send_mut2 Sort Prop
with branches_mut2_ind :=
  Induction for send_branches_mut2 Sort Prop
with forall_mut2_ind :=
  Induction for send_forall_mut2 Sort Prop.

Definition BranchSubsetLabel_seen
  (R : st -> st -> Prop)
  (xs ys : coseq (string * sort * st))
  (seen : list branch_key) : Prop :=
  forall lbl sr U,
    ~ In (lbl, sr) seen ->
    copathsel lbl sr ys U ->
    exists T,
      copathsel lbl sr xs T /\
      R T U.

Lemma BranchSubsetLabel_seen_nil :
  forall R xs ys,
    BranchSubsetLabel_seen R xs ys nil ->
    BranchSubsetLabel R xs ys.
Proof.
  intros R xs ys H.
  unfold BranchSubsetLabel_seen in H.
  unfold BranchSubsetLabel.

  intros lbl sr U Hsel.

  eapply H.
  - simpl.
    tauto.
  - exact Hsel.
Qed.

Lemma permitted_send_mut2_sound :
  forall p l s T U,
    permitted_send_mut2 p l s T U ->
    permitted_send p l s T U.
Proof.
  intros p l s T U Hperm.

  induction Hperm using send_mut2_ind
    with
    (P0 := fun p l s xs ys seen _ =>
       BranchSubsetLabel_seen
         (permitted_send p l s)
         xs ys seen)
    (P1 := fun p l s xs ys _ =>
       Forall2Ind
         (branch_rel (permitted_send p l s))
         xs ys).
- (* psm2_base *)
  eapply ps_base.
  eassumption.
- (* psm2_through_send *)
  eapply ps_through_send.
  + eassumption.
  + eapply BranchSubsetLabel_seen_nil.
    eassumption.
  + eassumption.
- (* psm2_through_receive *)
  eapply ps_through_receive.
  eassumption.
- (* sbm2_nil *)
  unfold BranchSubsetLabel_seen.
  intros lbl sr U Hfresh Hsel.
  inversion Hsel.
- (* sbm2_fresh *)
  unfold BranchSubsetLabel_seen in *.

  intros lbl' sr' U' Hfresh Hsel.

  inversion Hsel; subst.
  + exists T.
    split.
    * assumption.
    * assumption.
- apply IHHperm0.
  + simpl.
    intros [Heq | Hin].
    * inversion Heq; subst.
      contradiction.
    * apply Hfresh.
      exact Hin.
  + assumption.
- apply IHHperm0.
  + simpl.
    intros [Heq | Hin].
    * inversion Heq; subst.
      contradiction.
    * apply Hfresh.
      exact Hin.
  + assumption.
unfold BranchSubsetLabel_seen in *.
intros lbl' sr' U' Hfresh Hsel.

inversion Hsel; subst.

- (* Head selected: contradiction *)
  exfalso.
  apply Hfresh.
  exact i.

- (* Head skipped because labels differ *)
  eapply IHHperm.
  + exact Hfresh.
  + eassumption.

- (* Head skipped because sorts differ *)
  eapply IHHperm.
  + exact Hfresh.
  + eassumption.
- constructor.
apply f2i_cons.

- (* Head branches *)
  unfold branch_rel.

  exists lbl, sr, T, U.
  repeat split; try reflexivity.

  exact IHHperm.

- (* Tail branches *)
  exact IHHperm0.
Qed.

Lemma send_branches_mut2_complete_seen :
  forall p l s xs ys seen,
    finite_coseq ys ->
    BranchSubsetLabel_seen
      (permitted_send_mut2 p l s)
      xs ys seen ->
    send_branches_mut2 p l s xs ys seen.
Proof.
  intros p l s xs ys seen Hfin.
  revert seen.

  induction Hfin as [| x ys Hfin IH];
    intros seen Hsub.

  - (* Empty residual sequence *)
    apply sbm2_nil.

  - (* Nonempty residual sequence *)
    destruct x as [[lbl sr] U].
    destruct (classic (In (lbl, sr) seen))
      as [Hseen | Hfresh].
    + eapply sbm2_shadowed.
      * exact Hseen.
      * apply IH.
        unfold BranchSubsetLabel_seen in *.
        intros lbl' sr' U' Hfresh' Hsel.

        apply Hsub.
        -- exact Hfresh'.
        -- destruct
             (classic (lbl = lbl'))
             as [Hl | Hl].
           ++ subst lbl'.
              destruct
                (classic (sr = sr'))
                as [Hs | Hs].
              ** subst sr'.
                 exfalso.
                 apply Hfresh'.
                 exact Hseen.
              ** eapply pselneqs.
                 exact Hs.
                 exact Hsel.
           ++ eapply pselneql.
              ** exact Hl.
              ** exact Hsel.
    + assert (Hhead :
        exists T,
          copathsel lbl sr xs T /\
          permitted_send_mut2 p l s T U).
      {
        apply Hsub.
        - exact Hfresh.
        - apply psleeq.
      }

      destruct Hhead as [T [HselT Hperm]].
      eapply sbm2_fresh
        with (T := T).

      * exact Hfresh.
      * exact HselT.
      * exact Hperm.
      * apply IH.
        unfold BranchSubsetLabel_seen in *.
        intros lbl' sr' U' Hfresh' Hsel.

        apply Hsub.

        - (* The selected key is not in seen *)
          simpl in Hfresh'.
          intro Hin.
          apply Hfresh'.
          right.
          exact Hin.

        - (* Lift selection through the head *)
          destruct
            (classic (lbl = lbl'))
            as [Hl | Hl].

          + subst lbl'.
            destruct
              (classic (sr = sr'))
              as [Hs | Hs].

            * subst sr'.
              exfalso.
              apply Hfresh'.
              left.
              reflexivity.

            * eapply pselneqs.
              ** exact Hs.
              ** exact Hsel.

          + eapply pselneql.
            * exact Hl.
            * exact Hsel.
Qed.

Lemma send_branches_mut2_complete :
  forall p l s xs ys,
    finite_coseq ys ->
    BranchSubsetLabel
      (permitted_send_mut2 p l s)
      xs ys ->
    send_branches_mut2 p l s xs ys [].
Proof.
  intros p l s xs ys Hfin Hsub.

  eapply send_branches_mut2_complete_seen.
  - exact Hfin.
  - unfold BranchSubsetLabel_seen.
    intros lbl sr U Hfresh Hsel.
    unfold BranchSubsetLabel in Hsub.
    eapply Hsub.
    exact Hsel.
Qed.

Definition BranchSubsetLabel_at_seen
  (n : nat)
  (p l : string)
  (s : sort)
  (xs ys : coseq (string * sort * st))
  (seen : list branch_key) : Prop :=
  BranchSubsetLabel_seen
    (permitted_send_at n p l s)
    xs ys seen.

Lemma BranchSubsetLabel_seen_at_le :
  forall n m p l s xs ys seen,
    n <= m ->
    BranchSubsetLabel_at_seen n p l s xs ys seen ->
    BranchSubsetLabel_at_seen m p l s xs ys seen.
Proof.
  intros n m p l s xs ys seen Hle Hsub.

  unfold BranchSubsetLabel_at_seen in *.
  unfold BranchSubsetLabel_seen in *.

  intros lbl sr U Hfresh Hsel.

  destruct (Hsub lbl sr U Hfresh Hsel)
    as [T [HselT Hstep]].

  exists T.
  split.
  - exact HselT.
  - eapply permitted_send_at_le.
    + exact Hle.
    + exact Hstep.
Qed.

Lemma permitted_send_mut2_bounded :
  forall p l s T U,
    permitted_send_mut2 p l s T U ->
    exists n, permitted_send_at n p l s T U.
Proof.
  intros p l s T U Hperm.

  induction Hperm using send_mut2_ind
    with
    (P := fun p l s T U _ =>
       exists n, permitted_send_at n p l s T U)

    (P0 := fun p l s xs ys seen _ =>
       exists n,
         BranchSubsetLabel_at_seen n p l s xs ys seen)

    (P1 := fun p l s xs ys _ =>
       exists n,
         Forall2Ind
           (branch_rel (permitted_send_at n p l s))
           xs ys).
- (* psm2_base *)
  exists 0.
  simpl.
  exists xs.
  split.
  + reflexivity.
  + assumption.
  
- (* psm2_through_send *)
  destruct IHHperm as [m Hbound].

  exists (S m).
  simpl.
  right.
  left.

  exists q, xs, ys.
  repeat split; try assumption.

  eapply BranchSubsetLabel_seen_nil.
  exact Hbound.

- (* psm2_through_receive *)
  destruct IHHperm as [m Hbound].

  exists (S m).
  simpl.
  right.
  right.

  exists q, xs, ys.
  repeat split; try reflexivity.

  exact Hbound.

- (* sbm2_nil *)
  exists 0.

  unfold BranchSubsetLabel_at_seen.
  unfold BranchSubsetLabel_seen.

  intros lbl sr U Hfresh Hsel.
  inversion Hsel.

- (* sbm2_fresh *)
  destruct IHHperm as [n Hhead].
  destruct IHHperm0 as [m Htail].

  exists (Nat.max n m).

  unfold BranchSubsetLabel_at_seen.
  unfold BranchSubsetLabel_seen.

  intros lbl' sr' U' Hfresh Hsel.

  inversion Hsel; subst.
  + exists T.
    split.
    * exact c.
    * eapply permitted_send_at_le.
      -- apply Nat.le_max_l.
      -- exact Hhead.
  + assert (Hfresh' :
      ~ In (lbl', sr') ((lbl, sr) :: seen)).
    {
      simpl.
      intros [Heq | Hin].
      - inversion Heq; subst.
        contradiction.
      - apply Hfresh.
        exact Hin.
    }

    destruct (Htail lbl' sr' U' Hfresh')
      as [T' [HselT' Hstep]]. easy.

    exists T'.
    split.
    * exact HselT'.
    * eapply permitted_send_at_le.
      -- apply Nat.le_max_r.
      -- exact Hstep.

  + assert (Hfresh' :
      ~ In (lbl', sr') ((lbl, sr) :: seen)).
    {
      simpl.
      intros [Heq | Hin].
      - inversion Heq; subst.
        contradiction.
      - apply Hfresh.
        exact Hin.
    }

    destruct (Htail lbl' sr' U' Hfresh')
      as [T' [HselT' Hstep]]. easy.

    exists T'.
    split.
    * exact HselT'.
    * eapply permitted_send_at_le.
      -- apply Nat.le_max_r.
      -- exact Hstep.

- (* sbm2_shadowed *)
  destruct IHHperm as [n Htail].

  exists n.

  unfold BranchSubsetLabel_at_seen.
  unfold BranchSubsetLabel_seen.

  intros lbl' sr' U' Hfresh Hsel.

  inversion Hsel; subst.

  + exfalso.
    apply Hfresh.
    exact i.

  + eapply Htail.
    * exact Hfresh.
    * eassumption.

  + eapply Htail.
    * exact Hfresh.
    * eassumption.

- (* sfm2_nil *)
  exists 0.
  constructor.

- (* sfm2_cons *)
  destruct IHHperm as [n Hhead].
  destruct IHHperm0 as [m Htail].

  exists (Nat.max n m).

  apply f2i_cons.

  + unfold branch_rel.
    exists lbl, sr, T, U.
    repeat split; try reflexivity.

    eapply permitted_send_at_le.
    * apply Nat.le_max_l.
    * exact Hhead.

  + eapply Forall2Ind_mon
      with
      (P := branch_rel (permitted_send_at m p l s)).

    * intros x y Hbranch.
      unfold branch_rel in *.

      destruct Hbranch as
        [lbl0 [sr0 [T0 [U0
          [Hx [Hy Hstep]]]]]].

      exists lbl0, sr0, T0, U0.
      repeat split; try assumption.

      eapply permitted_send_at_le.
      -- apply Nat.le_max_r.
      -- exact Hstep.

    * exact Htail.
Qed.

