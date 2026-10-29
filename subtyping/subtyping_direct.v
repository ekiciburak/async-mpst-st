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

Fixpoint permitted_receive_at
  (n : nat)
  (p l : string)
  (s : sort)
  (T U : st) : Prop :=

  match n with

  | O =>
      exists xs,
        T = st_receive p xs /\
        copathsel l s xs U

  | S n' =>

      (* Direct receive *)
      (exists xs,
        T = st_receive p xs /\
        copathsel l s xs U)

      \/

      (* Anticipation through another input *)
      (exists q xs ys,
        p <> q /\
        T = st_receive q xs /\
        U = st_receive q ys /\
        ys <> conil /\
        BranchSubsetLabel
          (permitted_receive_at n' p l s)
          xs ys)

      \/

      (* Anticipation through an output *)
      (exists q xs ys,
        T = st_send q xs /\
        U = st_send q ys /\
        Forall2Ind
          (branch_rel
            (permitted_receive_at n' p l s))
          xs ys)

  end.

Definition subtype_direct_finR
  (R : st -> st -> Prop)
  (T U : st) : Prop :=

  (* Clause 1: Outputs of T *)
  (match T with
   | st_send p xs =>
       forall l s T',
         copathsel l s xs T' ->
         exists U',
           (exists n,
             permitted_send_at n p l s U U') /\
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
           (exists n,
             permitted_receive_at n p l s T T') /\
           R T' U'
   | _ => True
   end).

Definition subtype_direct_fin (T U : st) : Prop :=
  paco2 subtype_direct_finR bot2 T U.

Lemma subtype_direct_finR_mon :
  monotone2 subtype_direct_finR.
Proof.
  unfold monotone2, subtype_direct_finR.
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

Lemma R1_sim_step_fin :
  forall a b la lb s T U,
    a <> b ->
    R1_sim a b la lb s T U ->
    subtype_direct_finR (R1_sim a b la lb s) T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  inversion Hsim; subst; clear Hsim.

  - (* R1_initial *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 2: Recvs *)
      unfold input1.
      eapply recvs_through_receive.

      * discriminate.

      * intros l s0 V Hsel.
        apply copathsel_singleton in Hsel.
        destruct Hsel as [Hl [Hs HV]].
        subst l s0 V.

        unfold input1.
        apply recvs_base.
        discriminate.

    + (* Clause 4: Match the input *)
      intros l s0 U' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HU]].
      subst l s0 U'.

      exists (input1 a la s st_end).
      split.

      * (* Bounded receive anticipation *)
        exists 1.
        simpl.

        right. left.

        unfold input1.

        exists a,
          (cocons
            (la, s, input1 b lb s st_end)
            conil),
          (cocons
            (la, s, st_end)
            conil).

        repeat split. easy. easy.


        -- (* BranchSubsetLabel *)
           unfold BranchSubsetLabel.
           intros l0 s0 V Hsel0.

           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HV]].
           subst l0 s0 V.

           exists (input1 b lb s st_end).
           split.

           ++ constructor.

           ++ (* Depth 0: direct receive *)
              simpl.
              unfold input1.
              exists (cocons (lb, s, st_end) conil).
              split.
              ** reflexivity.
              ** constructor.

      * (* Continuations belong to R1_sim *)
        apply R1_cont.

  - (* R1_cont *)
    unfold subtype_direct_finR.
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

      exists st_end.
      split.

      * (* Direct receive at depth 0 *)
        exists 0.
        simpl.
        unfold input1.
        exists (cocons (la, s, st_end) conil).
        split.
        -- reflexivity.
        -- constructor.

      * apply R1_end.

  - (* R1_end *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; easy.
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

Lemma R1_sim_sound_fin :
  forall a b la lb s T U,
    a <> b ->
    R1_sim a b la lb s T U ->
    subtype_direct_fin T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := R1_sim a b la lb s)
    (r := bot2).

  - intros rr INCr INCl x y Hxy.

    pfold.
    eapply subtype_direct_finR_mon.

    + apply R1_sim_step_fin.
      * exact Hneq.
      * exact Hxy.

    + intros x' y' Hrel.
      right.
      apply INCl.
      exact Hrel.

  - exact Hsim.
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

Lemma test_R1_fin :
  forall a b la lb s,
    a <> b ->
    subtype_direct_fin
      (input1 a la s (input1 b lb s st_end))
      (input1 b lb s (input1 a la s st_end)).
Proof.
  intros a b la lb s Hneq.

  eapply R1_sim_sound_fin.
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


Lemma R2_sim_step_fin :
  forall a la lb s T U,
    R2_sim a la lb s T U ->
    subtype_direct_finR (R2_sim a la lb s) T U.
Proof.
  intros a la lb s T U Hsim.
  inversion Hsim; subst; clear Hsim.

  - (* R2_initial *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (input1 a lb s st_end).
      split.

      * (* Output anticipation through an input:
           depth 1 *)
        exists 1.
        simpl.
        right. right.

        unfold input1, output1.

        exists a,
          (cocons
            (lb, s, output1 a la s st_end)
            conil),
          (cocons
            (lb, s, st_end)
            conil).

        repeat split; try reflexivity.

        apply f2i_cons.

        -- (* Head branch *)
           unfold branch_rel.

           exists lb, s,
             (output1 a la s st_end),
             st_end.

           repeat split; try reflexivity.

           (* Direct send at depth 0 *)
           simpl.
           unfold output1.

           exists
             (cocons (la, s, st_end) conil).

           split.
           ++ reflexivity.
           ++ constructor.

        -- (* Empty tail *)
           apply f2i_nil.

      * (* Continuations belong to R2_sim *)
        apply R2_input.

    + (* Clause 4: Match the input *)
      intros l s0 U' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HU]].
      subst l s0 U'.

      exists (output1 a la s st_end).
      split.

      * (* Receive anticipation through an output:
           depth 1 *)
        exists 1.
        simpl.
        right. right.

        unfold output1, input1.

        exists a,
          (cocons
            (la, s, input1 a lb s st_end)
            conil),
          (cocons
            (la, s, st_end)
            conil).

        repeat split; try reflexivity.

        apply f2i_cons.

        -- (* Head branch *)
           unfold branch_rel.

           exists la, s,
             (input1 a lb s st_end),
             st_end.

           repeat split; try reflexivity.

           (* Direct receive at depth 0 *)
           simpl.
           unfold input1.

           exists
             (cocons (lb, s, st_end) conil).

           split.
           ++ reflexivity.
           ++ constructor.

        -- (* Empty tail *)
           apply f2i_nil.

      * (* Continuations belong to R2_sim *)
        apply R2_output.

  - (* R2_input *)
    unfold subtype_direct_finR.
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

      exists st_end.
      split.

      * (* Direct receive: depth 0 *)
        exists 0.
        simpl.
        unfold input1.

        exists
          (cocons (lb, s, st_end) conil).

        split.
        -- reflexivity.
        -- constructor.

      * (* Continuations belong to R2_sim *)
        apply R2_end.

  - (* R2_output *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists st_end.
      split.

      * (* Direct send: depth 0 *)
        exists 0.
        simpl.
        unfold output1.

        exists
          (cocons (la, s, st_end) conil).

        split.
        -- reflexivity.
        -- constructor.

      * (* Continuations belong to R2_sim *)
        apply R2_end.

    + (* Clause 3: Sends *)
      unfold output1.
      apply sends_base.
      discriminate.

  - (* R2_end *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; easy.
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

Lemma R2_sim_sound_fin :
  forall a la lb s T U,
    R2_sim a la lb s T U ->
    subtype_direct_fin T U.
Proof.
  intros a la lb s T U Hsim.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := R2_sim a la lb s)
    (r := bot2).

  - intros rr INCr INCl x y Hxy.
    pfold.

    eapply subtype_direct_finR_mon
      with (r := R2_sim a la lb s).

    + apply R2_sim_step_fin.
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

Lemma test_R2_fin :
  forall a la lb s,
    subtype_direct_fin
      (output1 a la s
        (input1 a lb s st_end))
      (input1 a lb s
        (output1 a la s st_end)).
Proof.
  intros a la lb s.
  eapply R2_sim_sound_fin.
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

Lemma R2_out_sim_step_fin :
  forall a b la lb s T U,
    a <> b ->
    R2_out_sim a b la lb s T U ->
    subtype_direct_finR (R2_out_sim a b la lb s) T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  inversion Hsim; subst; clear Hsim.

  - (* R2_out_initial *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the output to a *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (output1 b lb s st_end).
      split.

      * (* Anticipate output a through output b:
           depth 1 *)
        exists 1.
        simpl.
        right. left.

        unfold output1.

        exists b,
          (cocons
            (lb, s, output1 a la s st_end)
            conil),
          (cocons
            (lb, s, st_end)
            conil).

        repeat split; try reflexivity.

        -- (* a <> b *)
           exact Hneq.

        -- (* Resulting branches are nonempty *)
           discriminate.

        -- (* BranchSubsetLabel at depth 0 *)
           unfold BranchSubsetLabel.
           intros l0 s1 U0 Hsel0.

           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HU]].
           subst l0 s1 U0.

           exists (output1 a la s st_end).
           split.

           ++ constructor.

           ++ (* Direct send at depth 0 *)
              simpl.
              exists
                (cocons (la, s, st_end) conil).

              split.
              ** reflexivity.
              ** constructor.

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
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Direct output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists st_end.
      split.

      * (* Direct send: depth 0 *)
        exists 0.
        simpl.
        unfold output1.

        exists
          (cocons (lb, s, st_end) conil).

        split.
        -- reflexivity.
        -- constructor.

      * apply R2_out_end.

    + (* Clause 3: Sends b *)
      unfold output1.
      apply sends_base.
      discriminate.

  - (* R2_out_right *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Direct output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists st_end.
      split.

      * (* Direct send: depth 0 *)
        exists 0.
        simpl.
        unfold output1.

        exists
          (cocons (la, s, st_end) conil).

        split.
        -- reflexivity.
        -- constructor.

      * apply R2_out_end.

    + (* Clause 3: Sends a *)
      unfold output1.
      apply sends_base.
      discriminate.

  - (* R2_out_end *)
    unfold subtype_direct_finR.
    simpl.
    repeat split; easy.
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

Lemma R2_out_sim_sound_fin :
  forall a b la lb s T U,
    a <> b ->
    R2_out_sim a b la lb s T U ->
    subtype_direct_fin T U.
Proof.
  intros a b la lb s T U Hneq Hsim.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := R2_out_sim a b la lb s)
    (r := bot2).

  - intros rr INCr INCl x y Hxy.
    pfold.

    pose proof
      (R2_out_sim_step_fin a b la lb s x y Hneq Hxy)
      as Hstep.

    eapply subtype_direct_finR_mon.
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

Lemma test_R2_outputs_fin :
  forall a b la lb s,
    a <> b ->
    subtype_direct_fin
      (output1 a la s
        (output1 b lb s st_end))
      (output1 b lb s
        (output1 a la s st_end)).
Proof.
  intros a b la lb s Hneq.

  eapply R2_out_sim_sound_fin.
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

Lemma permitted_send_at_same_participant :
  forall n p l s l0 s0 T U,
    permitted_send_at n p l s
      (output1 p l0 s0 T) U ->
    l = l0.
Proof.
  induction n as [| n IH];
    intros p l s l0 s0 T U Hsend.

  - (* Depth 0: direct output *)
    simpl in Hsend.

    destruct Hsend as [xs [HT Hsel]].

    unfold output1 in HT.
    inversion HT; subst.

    apply copathsel_singleton in Hsel.
    destruct Hsel as [Hl [Hs HU]].

    exact Hl.

  - (* Depth S n *)
    simpl in Hsend.

    destruct Hsend as
      [Hbase | [Hthrough_send | Hthrough_receive]].

    + (* Direct output *)
      destruct Hbase as [xs [HT Hsel]].

      unfold output1 in HT.
      inversion HT; subst.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HU]].

      exact Hl.

    + (* Anticipation through another output *)
      destruct Hthrough_send as
        [q [xs [ys
          [Hneq [HT [HU [Hnonempty Hbranches]]]]]]].

      unfold output1 in HT.
      inversion HT; subst.

      contradiction.

    + (* Anticipation through an input *)
      destruct Hthrough_receive as
        [q [xs [ys [HT [HU Hbranches]]]]].

      unfold output1 in HT.
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

Lemma test_R2_same_recipient_invalid_fin :
  forall a la lb s,
    la <> lb ->
    ~ subtype_direct_fin
        (output1 a la s
          (output1 a lb s st_end))
        (output1 a lb s
          (output1 a la s st_end)).
Proof.
  intros a la lb s Hneq Hsub.

  unfold subtype_direct_fin in Hsub.
  punfold Hsub.
  unfold subtype_direct_finR in Hsub.
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

  destruct Houtputs as [U' [[n Hsend] _]].

  pose proof
    (permitted_send_at_same_participant
      n a la s lb s
      (output1 a la s st_end)
      U' Hsend)
    as Heq.

  contradiction.

  apply subtype_direct_finR_mon.
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

Lemma subtype_direct_input_prefix_fin :
  forall a la s T U,
    subtype_direct_fin T U ->
    subtype_direct_fin
      (input1 a la s T)
      (input1 a la s U).
Proof.
  intros a la s T U Hsub.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := fun X Y =>
       X = input1 a la s T /\
       Y = input1 a la s U)
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_direct_finR.
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

      * (* Direct receive at depth 0 *)
        exists 0.
        simpl.

        unfold input1.
        exists (cocons (la, s, T) conil).

        split.
        -- reflexivity.
        -- constructor.

      * (* Existing continuation subtyping *)
        left.
        unfold subtype_direct_fin in Hsub.

        eapply paco2_mon.
        -- exact Hsub.
        -- intros x y Hbot.
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

Lemma R1_general_fin :
  forall a b la lb s T U,
    a <> b ->
    subtype_direct_fin T U ->
    subtype_direct_fin
      (input1 a la s (input1 b lb s T))
      (input1 b lb s (input1 a la s U)).
Proof.
  intros a b la lb s T U Hneq Hsub.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := fun X Y =>
       X = input1 a la s (input1 b lb s T) /\
       Y = input1 b lb s (input1 a la s U))
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_direct_finR.
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

      * (* Anticipate receive b through receive a:
           depth 1 *)
        exists 1.
        simpl.
        right. left.

        unfold input1.

        exists a,
          (cocons
            (la, s, input1 b lb s T)
            conil),
          (cocons
            (la, s, T)
            conil).

        repeat split.

        -- (* b <> a *)
           intro Heq.
           apply Hneq.
           symmetry.
           exact Heq. easy.


        -- (* BranchSubsetLabel at depth 0 *)
           unfold BranchSubsetLabel.
           intros l0 s1 V Hsel0.

           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HV]].
           subst l0 s1 V.

           exists (input1 b lb s T).
           split.

           ++ constructor.

           ++ (* Direct receive at depth 0 *)
              simpl.
              exists
                (cocons (lb, s, T) conil).

              split.
              ** reflexivity.
              ** constructor.

      * (* Continuations are already subtypes *)
        left.

        assert (Hprefix :
          subtype_direct_fin
            (input1 a la s T)
            (input1 a la s U)).
        {
          apply subtype_direct_input_prefix_fin.
          exact Hsub.
        }

        unfold subtype_direct_fin in Hprefix.

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

Lemma subtype_direct_output_prefix_fin :
  forall a la s T U,
    subtype_direct_fin T U ->
    subtype_direct_fin
      (output1 a la s T)
      (output1 a la s U).
Proof.
  intros a la s T U Hsub.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := fun X Y =>
       X = output1 a la s T /\
       Y = output1 a la s U)
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists U.
      split.

      * (* Direct permitted send at depth 0 *)
        exists 0.
        simpl.

        unfold output1.
        exists (cocons (la, s, U) conil).

        split.
        -- reflexivity.
        -- constructor.

      * (* Existing continuation subtyping *)
        left.
        unfold subtype_direct_fin in Hsub.

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

Lemma R2_output_input_general_fin :
  forall a b la lb s T U,
    subtype_direct_fin T U ->
    subtype_direct_fin
      (output1 a la s (input1 b lb s T))
      (input1 b lb s (output1 a la s U)).
Proof.
  intros a b la lb s T U Hsub.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := fun X Y =>
       X = output1 a la s (input1 b lb s T) /\
       Y = input1 b lb s (output1 a la s U))
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Clause 1: Match the subtype's output *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (input1 b lb s U).
      split.

      * (* Anticipate output through input:
           depth 1 *)
        exists 1.
        simpl.
        right. right.

        unfold input1, output1.

        exists b,
          (cocons
            (lb, s, output1 a la s U)
            conil),
          (cocons
            (lb, s, U)
            conil).

        repeat split; try reflexivity.

        apply f2i_cons.

        -- (* Head branch *)
           unfold branch_rel.

           exists lb, s,
             (output1 a la s U), U.

           repeat split; try reflexivity.

           (* Direct send at depth 0 *)
           simpl.
           unfold output1.

           exists
             (cocons (la, s, U) conil).

           split.
           ++ reflexivity.
           ++ constructor.

        -- (* Empty tail *)
           apply f2i_nil.

      * (* Input-prefixed continuations are subtypes *)
        left.

        assert (Hprefix :
          subtype_direct_fin
            (input1 b lb s T)
            (input1 b lb s U)).
        {
          apply subtype_direct_input_prefix_fin.
          exact Hsub.
        }

        unfold subtype_direct_fin in Hprefix.

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

      * (* Anticipate input through output:
           depth 1 *)
        exists 1.
        simpl.
        right. right.

        unfold input1, output1.

        exists a,
          (cocons
            (la, s, input1 b lb s T)
            conil),
          (cocons
            (la, s, T)
            conil).

        repeat split; try reflexivity.

        apply f2i_cons.

        -- (* Head branch *)
           unfold branch_rel.

           exists la, s,
             (input1 b lb s T), T.

           repeat split; try reflexivity.

           (* Direct receive at depth 0 *)
           simpl.
           unfold input1.

           exists
             (cocons (lb, s, T) conil).

           split.
           ++ reflexivity.
           ++ constructor.

        -- (* Empty tail *)
           apply f2i_nil.

      * (* Output-prefixed continuations are subtypes *)
        left.

        assert (Hprefix :
          subtype_direct_fin
            (output1 a la s T)
            (output1 a la s U)).
        {
          apply subtype_direct_output_prefix_fin.
          exact Hsub.
        }

        unfold subtype_direct_fin in Hprefix.

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

Lemma R2_output_output_general_fin :
  forall a b la lb s T U,
    a <> b ->
    subtype_direct_fin T U ->
    subtype_direct_fin
      (output1 a la s (output1 b lb s T))
      (output1 b lb s (output1 a la s U)).
Proof.
  intros a b la lb s T U Hneq Hsub.
  unfold subtype_direct_fin.

  eapply paco2_acc with
    (l := fun X Y =>
       X = output1 a la s (output1 b lb s T) /\
       Y = output1 b lb s (output1 a la s U))
    (r := bot2).

  - intros rr INCr INCl X Y [HX HY].
    subst X Y.

    pfold.
    unfold subtype_direct_finR.
    simpl.
    repeat split; try easy.

    + (* Match output to a *)
      intros l s0 T' Hsel.

      apply copathsel_singleton in Hsel.
      destruct Hsel as [Hl [Hs HT]].
      subst l s0 T'.

      exists (output1 b lb s U).
      split.

      * (* Anticipate output a through output b:
           depth 1 *)
        exists 1.
        simpl.
        right. left.

        unfold output1.

        exists b,
          (cocons
            (lb, s, output1 a la s U)
            conil),
          (cocons
            (lb, s, U)
            conil).

        repeat split; try reflexivity.

        -- (* Different participants *)
           exact Hneq. easy.

        -- (* BranchSubsetLabel at depth 0 *)
           unfold BranchSubsetLabel.
           intros l0 s1 V Hsel0.

           apply copathsel_singleton in Hsel0.
           destruct Hsel0 as [Hl [Hs HV]].
           subst l0 s1 V.

           exists (output1 a la s U).
           split.

           ++ constructor.

           ++ (* Direct send at depth 0 *)
              simpl.
              exists
                (cocons (la, s, U) conil).

              split.
              ** reflexivity.
              ** constructor.


      * (* Continuation subtyping *)
        left.

        assert (Hprefix :
          subtype_direct_fin
            (output1 b lb s T)
            (output1 b lb s U)).
        {
          apply subtype_direct_output_prefix_fin.
          exact Hsub.
        }

        unfold subtype_direct_fin in Hprefix.

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


Definition all_branches_fb
  (ys : coseq (string * sort * st)) : Prop :=
  forall lbl sr U,
    coseq_member (lbl, sr, U) ys ->
    finitely_branchingC U.

Lemma send_forall_at_mut2_aux :
  forall n p l s xs ys,
    (forall T U,
      finitely_branchingC U ->
      permitted_send_at n p l s T U ->
      permitted_send_mut2 p l s T U) ->
    all_branches_fb ys ->
    Forall2Ind
      (branch_rel (permitted_send_at n p l s))
      xs ys ->
    send_forall_mut2 p l s xs ys.
Proof.
  intros n p l s xs ys Hconvert Hfb Hrel.

  revert Hfb.

  induction Hrel as
    [| x y xs' ys' Hhead Htail IHtail];
    intro Hfb.

  - constructor.

  - destruct Hhead as
      [lbl [sr [T0 [U0
        [Hx [Hy Hstep]]]]]].

    subst x y.

    apply sfm2_cons.

    + apply Hconvert.
      * apply (Hfb lbl sr U0).
        apply cm_here.
      * exact Hstep.

    + apply IHtail.
      unfold all_branches_fb in *.
      intros lbl' sr' U' Hmem.
      apply (Hfb lbl' sr' U').
      apply cm_there.
      exact Hmem.
Qed.

Inductive NoDupBranchKeys :
  coseq (string * sort * st) -> Prop :=

| ndb_nil :
    NoDupBranchKeys conil

| ndb_cons :
    forall lbl sr T xs,
      (forall U,
        ~ coseq_member (lbl, sr, U) xs) ->
      NoDupBranchKeys xs ->
      NoDupBranchKeys (cocons (lbl, sr, T) xs).

Lemma coseq_member_copathsel :
  forall xs lbl sr U,
    NoDupBranchKeys xs ->
    coseq_member (lbl, sr, U) xs ->
    copathsel lbl sr xs U.
Proof.
  intros xs lbl sr U Hnodup.
  induction Hnodup as
    [| lbl0 sr0 T0 xs Hfresh Hnodup IH];
    intro Hmem.

  - inversion Hmem.

  - inversion Hmem; subst.

    + (* Head branch *)
      apply psleeq.

    + (* Branch in the tail *)
      assert (Hdiff :
        lbl0 <> lbl \/ sr0 <> sr).
      {
        destruct (classic (lbl0 = lbl)) as [Hl | Hl].
        - right.
          intro Hs.
          subst.
          eapply Hfresh.
          exact H0.
        - left.
          exact Hl.
      }

      destruct Hdiff as [Hl | Hs].

      * apply pselneql.
        -- exact Hl.
        -- apply IH.
           assumption.

      * apply pselneqs.
        -- exact Hs.
        -- apply IH.
           assumption.
Qed.

Lemma finitely_branchingC_receive_all_unique :
  forall q ys,
    NoDupBranchKeys ys ->
    finitely_branchingC (st_receive q ys) ->
    all_branches_fb ys.
Proof.
  intros q ys Hnodup Hfb.

  unfold all_branches_fb.
  intros lbl sr U Hmem.

  eapply finitely_branchingC_branch_receive.
  - exact Hfb.
  - eapply coseq_member_copathsel.
    + exact Hnodup.
    + exact Hmem.
Qed.

Definition wf_branchingR
  (R : st -> Prop) (T : st) : Prop :=
  match T with
  | st_end => True
  | st_send p xs
  | st_receive p xs =>
      finite_coseq xs /\
      NoDupBranchKeys xs /\
      (forall lbl sr U,
        coseq_member (lbl, sr, U) xs ->
        R U)
  end.

Definition wf_branchingC (T : st) : Prop :=
  paco1 wf_branchingR bot1 T.

Lemma wf_branchingR_mon :
  monotone1 wf_branchingR.
Proof.
  unfold monotone1.
  intros T R R' LE H.
  unfold wf_branchingR in *.
  destruct T; simpl in *; auto.
  all: destruct LE as [Hfin [Hnodup Hall]].
  all: repeat split; try assumption.
  all: intros lbl sr U Hmem.
  all: apply H.
  all: eapply Hall; eassumption.
Qed.

Lemma wf_branchingC_member_receive :
  forall q ys lbl sr U,
    wf_branchingC (st_receive q ys) ->
    coseq_member (lbl, sr, U) ys ->
    wf_branchingC U.
Proof.
  intros q ys lbl sr U Hwf Hmem.

  unfold wf_branchingC in Hwf.
  punfold Hwf.

  unfold wf_branchingR in Hwf.
  simpl in Hwf.

  destruct Hwf as [Hfin [Hnodup Hall]].

  specialize (Hall lbl sr U Hmem).

  unfold wf_branchingC.
  destruct Hall as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.

  apply wf_branchingR_mon.
Qed.

Lemma wf_branchingC_finitely_branching :
  forall U,
    wf_branchingC U ->
    finitely_branchingC U.
Proof.
  unfold finitely_branchingC.
  pcofix CIH.
  intros U Hwf.
  unfold wf_branchingC in Hwf.
  punfold Hwf.

  pfold.
  unfold finitely_branchingR.

  destruct U as [| p xs | p xs];
    simpl in *.

  - (* End *)
    easy.

  - (* Receive *)
    destruct Hwf as [Hfin [Hnodup Hall]].

    split.
    + exact Hfin.

    + intros lbl sr U0 Hsel.

      apply copathsel_member in Hsel.

      specialize (Hall lbl sr U0 Hsel).

      destruct Hall as [Hco | Hbot].

      * right.
        apply CIH.
        exact Hco.

      * destruct Hbot.

  - (* Send *)
    destruct Hwf as [Hfin [Hnodup Hall]].

    split.
    + exact Hfin.

    + intros lbl sr U0 Hsel.

      apply copathsel_member in Hsel.

      specialize (Hall lbl sr U0 Hsel).

      destruct Hall as [Hco | Hbot].

      * right.
        apply CIH.
        exact Hco.

      * destruct Hbot.

  apply wf_branchingR_mon.
Qed.

Lemma wf_branchingC_member_send :
  forall q ys lbl sr U,
    wf_branchingC (st_send q ys) ->
    coseq_member (lbl, sr, U) ys ->
    wf_branchingC U.
Proof.
  intros q ys lbl sr U Hwf Hmem.

  unfold wf_branchingC in Hwf.
  punfold Hwf.

  unfold wf_branchingR in Hwf.
  simpl in Hwf.

  destruct Hwf as [Hfin [Hnodup Hall]].

  specialize (Hall lbl sr U Hmem).

  unfold wf_branchingC.
  destruct Hall as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.

  apply wf_branchingR_mon.
Qed.

Lemma send_forall_at_mut2_aux_wf :
  forall n p l s xs ys,
    (forall T U,
      wf_branchingC U ->
      permitted_send_at n p l s T U ->
      permitted_send_mut2 p l s T U) ->
    (forall lbl sr U,
      coseq_member (lbl, sr, U) ys ->
      wf_branchingC U) ->
    Forall2Ind
      (branch_rel (permitted_send_at n p l s))
      xs ys ->
    send_forall_mut2 p l s xs ys.
Proof.
  intros n p l s xs ys Hconvert Hall Hrel.

  revert Hall.

  induction Hrel as
    [| x y xs' ys' Hhead Htail IHtail];
    intro Hall.

  - (* Empty branches *)
    constructor.

  - (* Nonempty branches *)
    destruct Hhead as
      [lbl [sr [T0 [U0 [Hx [Hy Hstep]]]]]].

    subst x y.

    apply sfm2_cons.

    + (* Convert the head continuation *)
      apply Hconvert.

      * apply (Hall lbl sr U0).
        apply cm_here.

      * exact Hstep.

    + (* Convert the remaining branches *)
      apply IHtail.

      intros lbl' sr' U' Hmem.

      apply (Hall lbl' sr' U').
      apply cm_there.
      exact Hmem.
Qed.

Lemma permitted_send_at_mut2 :
  forall n p l s T U,
    wf_branchingC U ->
    permitted_send_at n p l s T U ->
    permitted_send_mut2 p l s T U.
Proof.
  induction n as [| n IH];
    intros p l s T U Hfb Hperm.

  - (* Depth zero *)
    simpl in Hperm.
    destruct Hperm as [xs [-> Hsel]].
    eapply psm2_base.
    exact Hsel.

  - (* Successor depth *)
    simpl in Hperm.
    destruct Hperm as
      [Hbase | [Hsend | Hrecv]].

    + (* Direct output *)
      destruct Hbase as [xs [-> Hsel]].
      eapply psm2_base.
      exact Hsel.

    + (* Anticipation through output *)
      destruct Hsend as
        [q [xs [ys
          [Hneq [-> [-> [Hnonempty Hbranches]]]]]]].

      eapply psm2_through_send.
      * exact Hneq.
      * eapply send_branches_mut2_complete.
        -- eapply finitely_branchingC_send_finite.
           apply wf_branchingC_finitely_branching in Hfb.
           exact Hfb.
        -- unfold BranchSubsetLabel in *.
           intros lbl sr U0 Hsel.

           destruct (Hbranches lbl sr U0 Hsel)
             as [T0 [HselT Hstep]].

           exists T0.
           split.
           ++ exact HselT.
           ++ apply IH.
              **
              eapply wf_branchingC_member_send.
- exact Hfb.
- eapply copathsel_member.
  exact Hsel. easy. easy.

+ (* Anticipation through input *)
  destruct Hrecv as
    [q [xs [ys [-> [-> Hbranches]]]]].

  eapply psm2_through_receive.

  eapply send_forall_at_mut2_aux_wf.

  - (* Convert individual bounded transitions *)
    intros T0 U0 HwfU Hstep.
    eapply IH.
    + exact HwfU.
    + exact Hstep.

  - (* Every positional continuation is well formed *)
    intros lbl sr U0 Hmem.
    eapply wf_branchingC_member_receive.
    + exact Hfb.
    + exact Hmem.

  - (* Original positional correspondence *)
    exact Hbranches.
Qed.

Lemma send_forall_at_mut2_wf :
  forall n p l s xs ys,
    (forall T U,
      wf_branchingC U ->
      permitted_send_at n p l s T U ->
      permitted_send_mut2 p l s T U) ->
    (forall lbl sr U,
      coseq_member (lbl, sr, U) ys ->
      wf_branchingC U) ->
    Forall2Ind
      (branch_rel (permitted_send_at n p l s))
      xs ys ->
    send_forall_mut2 p l s xs ys.
Proof.
  intros n p l s xs ys Hconvert Hall Hrel.

  revert Hall.

  induction Hrel as
    [| x y xs' ys' Hhead Htail IHtail];
    intro Hall.

  - constructor.

  - destruct Hhead as
      [lbl [sr [T0 [U0 [Hx [Hy Hstep]]]]]].
    subst x y.

    apply sfm2_cons.

    + apply Hconvert.
      * apply (Hall lbl sr U0).
        apply cm_here.
      * exact Hstep.

    + apply IHtail.
      intros lbl' sr' U' Hmem.
      apply (Hall lbl' sr' U').
      apply cm_there.
      exact Hmem.
Qed.

Lemma permitted_send_at_mut2_wf :
  forall n p l s T U,
    wf_branchingC U ->
    permitted_send_at n p l s T U ->
    permitted_send_mut2 p l s T U.
Proof.
  induction n as [| n IH];
    intros p l s T U Hwf Hperm.

  - (* Depth zero: direct output *)
    simpl in Hperm.
    destruct Hperm as [xs [-> Hsel]].
    eapply psm2_base.
    exact Hsel.

  - (* Successor depth *)
    simpl in Hperm.
    destruct Hperm as
      [Hbase | [Hsend | Hrecv]].

    + (* Direct output *)
      destruct Hbase as [xs [-> Hsel]].
      eapply psm2_base.
      exact Hsel.

    + (* Anticipation through another output *)
      destruct Hsend as
        [q [xs [ys
          [Hneq [-> [-> [Hnonempty Hbranches]]]]]]].

      eapply psm2_through_send.

      * (* Different participants *)
        exact Hneq.

      * (* Convert label-based branch correspondence *)
        eapply send_branches_mut2_complete.

        -- (* Residual branches are finite *)
           unfold wf_branchingC in Hwf.
           punfold Hwf.

           unfold wf_branchingR in Hwf.
           simpl in Hwf.

           destruct Hwf as [Hfin [Hnodup Hall]].
           exact Hfin.

           apply wf_branchingR_mon.

        -- (* Convert every selected branch *)
           unfold BranchSubsetLabel in *.
           intros lbl sr U0 Hsel.

           destruct (Hbranches lbl sr U0 Hsel)
             as [T0 [HselT Hstep]].

           exists T0.
           split.

           ++ exact HselT.

           ++ eapply IH.

              ** (* Residual continuation is well formed *)
                 eapply wf_branchingC_member_send.

                 --- exact Hwf.

                 --- apply copathsel_member.
                     exact Hsel.

              ** (* Smaller anticipation depth *)
                 exact Hstep.

      * (* Residual sequence is nonempty *)
        exact Hnonempty.

    + (* Anticipation through an input *)
      destruct Hrecv as
        [q [xs [ys [-> [-> Hbranches]]]]].

      eapply psm2_through_receive.

      eapply send_forall_at_mut2_wf.

      * (* Convert individual depth-n transitions *)
        intros T0 U0 HwfU Hstep.

        eapply IH.
        -- exact HwfU.
        -- exact Hstep.

      * (* Every positional continuation is well formed *)
        intros lbl sr U0 Hmem.

        eapply wf_branchingC_member_receive.
        -- exact Hwf.
        -- exact Hmem.

      * (* Original positional correspondence *)
        exact Hbranches.
Qed.

Lemma translated_tree_finitely_branching :
  forall T,
    translated_tree T ->
    finitely_branchingC T.
Proof.
  intros T [L ->].
  apply lt2st_finitely_branching.
Qed.

Lemma translated_tree_send_branch :
  forall T p xs l s U,
    translated_tree T ->
    T = st_send p xs ->
    copathsel l s xs U ->
    translated_tree U.
Proof.
  intros T p xs l s U [L HL] Heq Hsel.
  subst T.
  destruct (lt2st_send_branch L p xs l s U Heq Hsel)
    as [L' HU].
  exists L'.
  exact HU.
Qed.

Scheme permitted_send_ind2 :=
  Induction for permitted_send Sort Prop.

Check permitted_send_ind2.
Print permitted_send_ind2.

Definition BranchSubsetLabel_map
  (R S : st -> st -> Prop)
  (Hmap : forall T U, R T U -> S T U)
  (xs ys : coseq (string * sort * st))
  (H : BranchSubsetLabel R xs ys)
  : BranchSubsetLabel S xs ys.
Proof.
  unfold BranchSubsetLabel in *.
  intros lbl sr U Hsel.
  destruct (H lbl sr U Hsel) as [T [HselT HR]].
  exists T.
  split.
  - exact HselT.
  - apply Hmap.
    exact HR.
Qed.

Lemma branch_rel_map :
  forall
    (R S : st -> st -> Prop),
    (forall T U, R T U -> S T U) ->
    forall x y,
      branch_rel R x y ->
      branch_rel S x y.
Proof.
  intros R S Hmap x y Hbranch.
  unfold branch_rel in *.

  destruct Hbranch as
    [lbl [sr [T [U [Hx [Hy HR]]]]]].

  exists lbl, sr, T, U.
  repeat split; try assumption.

  apply Hmap.
  exact HR.
Defined.

Lemma permitted_send_at_cases :
  forall n p l s T U,
    permitted_send_at n p l s T U ->
    (exists xs,
       T = st_send p xs /\
       copathsel l s xs U)
    \/
    (exists k q xs ys,
       p <> q /\
       T = st_send q xs /\
       U = st_send q ys /\
       ys <> conil /\
       BranchSubsetLabel
         (permitted_send_at k p l s) xs ys)
    \/
    (exists k q xs ys,
       T = st_receive q xs /\
       U = st_receive q ys /\
       Forall2Ind
         (branch_rel (permitted_send_at k p l s))
         xs ys).
Proof.
  intros n p l s T U Hsend.
  destruct n as [|n].

  - simpl in Hsend.
    left.
    exact Hsend.

  - simpl in Hsend.
    destruct Hsend as
      [Hbase | [Hthrough_send | Hthrough_receive]].

    + left.
      exact Hbase.

    + right. left.
      destruct Hthrough_send as
        [q [xs [ys
          [Hneq [HT [HU [Hnonempty Hbranches]]]]]]].
      exists n, q, xs, ys.
      repeat split; assumption.

    + right. right.
      destruct Hthrough_receive as
        [q [xs [ys [HT [HU Hbranches]]]]].
      exists n, q, xs, ys.
      repeat split; assumption.
Qed.

Lemma upaco2_fin_bot :
  forall T U,
    upaco2 subtype_direct_finR bot2 T U ->
    subtype_direct_fin T U.
Proof.
  intros T U H.
  destruct H as [H | H].
  - exact H.
  - destruct H.
Qed.

Lemma wf_branchingC_branch_send :
  forall p xs l s U,
    wf_branchingC (st_send p xs) ->
    copathsel l s xs U ->
    wf_branchingC U.
Proof.
  intros p xs l s U Hwf Hsel.

  eapply wf_branchingC_member_send.
  - exact Hwf.
  - apply copathsel_member.
    exact Hsel.
Qed.

Lemma wf_branchingC_branch_receive :
  forall p xs l s U,
    wf_branchingC (st_receive p xs) ->
    copathsel l s xs U ->
    wf_branchingC U.
Proof.
  intros p xs l s U Hwf Hsel.

  eapply wf_branchingC_member_receive.
  - exact Hwf.
  - apply copathsel_member.
    exact Hsel.
Qed.

Inductive permitted_receive_mut2 :
  string -> string -> sort -> st -> st -> Prop :=

| prm2_base :
    forall p l s xs T,
      copathsel l s xs T ->
      permitted_receive_mut2 p l s
        (st_receive p xs) T

| prm2_through_receive :
    forall p q l s xs ys,
      p <> q ->
      receive_branches_mut2 p l s xs ys nil ->
      ys <> conil ->
      permitted_receive_mut2 p l s
        (st_receive q xs)
        (st_receive q ys)

| prm2_through_send :
    forall p q l s xs ys,
      receive_forall_mut2 p l s xs ys ->
      permitted_receive_mut2 p l s
        (st_send q xs)
        (st_send q ys)

with receive_branches_mut2 :
  string -> string -> sort ->
  coseq (string * sort * st) ->
  coseq (string * sort * st) ->
  list branch_key -> Prop :=

| rbm2_nil :
    forall p l s xs seen,
      receive_branches_mut2 p l s
        xs conil seen

| rbm2_fresh :
    forall p l s xs lbl sr U ys seen T,

      fresh_branch (lbl, sr) seen ->

      copathsel lbl sr xs T ->

      permitted_receive_mut2 p l s T U ->

      receive_branches_mut2 p l s
        xs ys ((lbl, sr) :: seen) ->

      receive_branches_mut2 p l s
        xs
        (cocons (lbl, sr, U) ys)
        seen

| rbm2_shadowed :
    forall p l s xs lbl sr U ys seen,

      In (lbl, sr) seen ->

      receive_branches_mut2 p l s
        xs ys seen ->

      receive_branches_mut2 p l s
        xs
        (cocons (lbl, sr, U) ys)
        seen

with receive_forall_mut2 :
  string -> string -> sort ->
  coseq (string * sort * st) ->
  coseq (string * sort * st) -> Prop :=

| rfm2_nil :
    forall p l s,
      receive_forall_mut2 p l s conil conil

| rfm2_cons :
    forall p l s lbl sr T U xs ys,

      permitted_receive_mut2 p l s T U ->

      receive_forall_mut2 p l s xs ys ->

      receive_forall_mut2 p l s
        (cocons (lbl, sr, T) xs)
        (cocons (lbl, sr, U) ys).

Scheme receive_mut_ind' :=
  Induction for permitted_receive_mut2 Sort Prop
with receive_branches_ind' :=
  Induction for receive_branches_mut2 Sort Prop
with receive_forall_ind' :=
  Induction for receive_forall_mut2 Sort Prop.

Scheme receive_main_scheme :=
  Induction for permitted_receive_mut2 Sort Prop
with receive_branch_scheme :=
  Induction for receive_branches_mut2 Sort Prop
with receive_all_scheme :=
  Induction for receive_forall_mut2 Sort Prop.

Definition subtype_direct_mut2R
  (R : st -> st -> Prop)
  (T U : st) : Prop :=

  (* Clause 1: Outputs of T *)
  (match T with
   | st_send p xs =>
       forall l s T',
         copathsel l s xs T' ->
         exists U',
           permitted_send_mut2 p l s U U' /\
           R T' U'
   | _ => True
   end)

  /\

  (* Clause 2: Inputs of T *)
  (match T with
   | st_receive p xs =>
       Recvs p U
   | _ => True
   end)

  /\

  (* Clause 3: Outputs of U *)
  (match U with
   | st_send p xs =>
       Sends p T
   | _ => True
   end)

  /\

  (* Clause 4: Inputs of U *)
  (match U with
   | st_receive p xs =>
       forall l s U',
         copathsel l s xs U' ->
         exists T',
           permitted_receive_mut2 p l s T T' /\
           R T' U'
   | _ => True
   end).

Definition subtype_direct_mut2 (T U : st) : Prop :=
  paco2 subtype_direct_mut2R bot2 T U.

Lemma subtype_direct_mut2R_mon :
  monotone2 subtype_direct_mut2R.
Proof.
  unfold monotone2, subtype_direct_mut2R.
  intros T U R R' H.

  destruct H as [H1 [H2 [H3 H4]]].

  repeat split.

  - (* Clause 1: Outputs of T *)
    destruct T; simpl in *; auto.

    intros l s0 T' Hsel.

    destruct (H1 l s0 T' Hsel)
      as [U' [Hp HR]].

    exists U'.
    split; auto.

  - (* Clause 2: Inputs of T *)
    exact H2.

  - (* Clause 3: Outputs of U *)
    exact H3.

  - (* Clause 4: Inputs of U *)
    destruct U; simpl in *; auto.

    intros l s0 U' Hsel.

    destruct (H4 l s0 U' Hsel)
      as [T' [Hp HR]].

    exists T'.
    split; auto.
Qed.

Lemma permitted_send_mut2_transport_base :
  forall p l s xs U' V,
    copathsel l s xs U' ->
    subtype_direct_mut2 (st_send p xs) V ->
    exists V',
      permitted_send_mut2 p l s V V' /\
      subtype_direct_mut2 U' V'.
Proof.
  intros p l s xs U' V Hsel Hsub.

  unfold subtype_direct_mut2 in Hsub.
  punfold Hsub.

  unfold subtype_direct_mut2R in Hsub.
  simpl in Hsub.

  destruct Hsub as [Houtputs _].

  specialize (Houtputs l s U' Hsel).

  destruct Houtputs as [V' [Hsend Hrel]].

  exists V'.
  split.
  - exact Hsend.
  - destruct Hrel as [Hco | Hbot].
    + exact Hco.
    + destruct Hbot.

  apply subtype_direct_mut2R_mon.
Qed.

Lemma subtype_mut2_output_first :
  forall p xs U V l s T',
    subtype_direct_mut2 (p ! xs) U ->
    subtype_direct_mut2 U V ->
    copathsel l s xs T' ->
    exists U',
      permitted_send_mut2 p l s U U' /\
      subtype_direct_mut2 T' U'.
Proof.
  intros p xs U V l s T' HTU HUV Hsel.

  eapply permitted_send_mut2_transport_base.
  - exact Hsel.
  - exact HTU.
Qed.

Scheme send_mut_ind' :=
  Induction for permitted_send_mut2 Sort Prop
with send_branches_ind' :=
  Induction for send_branches_mut2 Sort Prop
with send_forall_ind' :=
  Induction for send_forall_mut2 Sort Prop.

Combined Scheme permitted_send_mut2_mutind
  from send_mut_ind',
       send_branches_ind',
       send_forall_ind'.

Lemma test_empty_receive_send :
  forall p q l s,
    permitted_send_mut2 p l s
      (st_receive q conil)
      (st_receive q conil).
Proof.
  intros.
  apply psm2_through_receive.
  apply sfm2_nil.
Qed.

Lemma permitted_receive_mut2_empty_source :
  forall p l s U,
    ~ permitted_receive_mut2 p l s
        (st_receive p conil) U.
Proof.
  intros p l s U Hrecv.

  remember (st_receive p conil) as X eqn:HX.

  induction Hrecv.

  - (* prm2_base *)
    inversion HX; subst.
    inversion H.

  - (* prm2_through_receive *)
    inversion HX; subst.
    contradiction.

  - (* prm2_through_send *)
    discriminate.
Qed.

Definition send_finite_P
  p l s T U
  (_ : permitted_send_mut2 p l s T U) : Prop :=
  wf_branchingC T ->
  finitely_branchingC T ->
  finitely_branchingC U.

Definition send_finite_Pbranches
  p l s xs ys seen
  (_ : send_branches_mut2 p l s xs ys seen) : Prop :=
  forall q,
    wf_branchingC (st_send q xs) ->
    finitely_branchingC (st_send q xs) ->
    finite_coseq ys /\
    (forall lbl sr U,
      copathsel lbl sr ys U ->
      In (lbl, sr) seen \/
      finitely_branchingC U).

Definition send_finite_Pforall
  p l s xs ys
  (_ : send_forall_mut2 p l s xs ys) : Prop :=
  forall q,
    wf_branchingC (st_receive q xs) ->
    finitely_branchingC (st_receive q xs) ->
    finite_coseq ys /\
    (forall lbl sr U,
      copathsel lbl sr ys U ->
      finitely_branchingC U).

Lemma finitely_branchingC_member_send :
  forall q xs lbl sr T,
    finitely_branchingC (st_send q xs) ->
    copathsel lbl sr xs T ->
    finitely_branchingC T.
Proof.
  intros q xs lbl sr T Hfb Hsel.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [_ Hall].

  specialize (Hall lbl sr T Hsel).

  destruct Hall as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.

  apply finitely_branchingR_mon.
Qed.


Lemma finitely_branchingC_member_receive :
  forall q xs lbl sr T,
    finitely_branchingC (st_receive q xs) ->
    copathsel lbl sr xs T ->
    finitely_branchingC T.
Proof.
  intros q xs lbl sr T Hfb Hsel.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [_ Hall].

  specialize (Hall lbl sr T Hsel).

  destruct Hall as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.

  apply finitely_branchingR_mon.
Qed.

Lemma wf_branchingC_receive_tail :
  forall q lbl sr T xs,
    wf_branchingC
      (st_receive q (cocons (lbl, sr, T) xs)) ->
    wf_branchingC (st_receive q xs).
Proof.
  intros q lbl sr T xs Hwf.

  unfold wf_branchingC in Hwf.
  punfold Hwf.
  2: apply wf_branchingR_mon.

  unfold wf_branchingR in Hwf.
  simpl in Hwf.

  destruct Hwf as [Hfin [Hnodup Hall]].

  unfold wf_branchingC.
  pfold.

  unfold wf_branchingR.
  simpl.

  repeat split.

  - (* Finite tail *)
    eapply finite_coseq_tail.
    exact Hfin.

  - (* Unique branch keys in the tail *)
    inversion Hnodup; subst.
    assumption.

  - (* Every tail continuation remains well formed *)
    intros lbl' sr' U Hmem.

    apply (Hall lbl' sr' U).

    apply cm_there.
    exact Hmem.
Qed.

Lemma permitted_send_mut2_residual_finite :
  forall p l s T U,
    wf_branchingC T ->
    finitely_branchingC T ->
    permitted_send_mut2 p l s T U ->
    finitely_branchingC U.
Proof.
  intros p l s T U Hwf Hfb Hsend.

  revert Hwf Hfb.

  change (send_finite_P p l s T U Hsend).

  eapply
    (send_mut2_ind
       send_finite_P
       send_finite_Pbranches
       send_finite_Pforall).
- (* psm2_base *)
  intros p0 l0 s0 xs T0 Hsel.

  unfold send_finite_P.
  intros Hwf Hfb.

  unfold finitely_branchingC in Hfb.
  punfold Hfb.

  unfold finitely_branchingR in Hfb.
  simpl in Hfb.

  destruct Hfb as [_ Hall].

  specialize (Hall l0 s0 T0 Hsel).

  destruct Hall as [Hco | Hbot].
  + exact Hco.
  + destruct Hbot.

  apply finitely_branchingR_mon.

- (* psm2_through_send *)
  intros p0 q l0 s0 xs ys
         Hneq Hbranches IHbranches Hnonempty.

  unfold send_finite_P.
  intros Hwf Hfb.

  unfold send_finite_Pbranches in IHbranches.

  specialize (IHbranches q Hwf Hfb).

  destruct IHbranches as [Hfinite Hselected].

  unfold finitely_branchingC.
  pfold.

  unfold finitely_branchingR.
  simpl.

  split.

  + (* The residual branch sequence is finite *)
    exact Hfinite.

  + (* Every selected residual continuation is finite *)
    intros lbl sr U0 Hsel.

    destruct (Hselected lbl sr U0 Hsel)
      as [Hseen | HfiniteU].

    * (* No keys are initially seen *)
      contradiction.

    * (* Residual continuation *)
      left.
      exact HfiniteU.

- (* psm2_through_receive *)
  intros p0 q l0 s0 xs ys Hforall IHforall.

  unfold send_finite_P.
  intros Hwf Hfb.

  unfold send_finite_Pforall in IHforall.
  specialize (IHforall q Hwf Hfb).

  destruct IHforall as [Hfinite Hselected].

  unfold finitely_branchingC.
  pfold.

  unfold finitely_branchingR.
  simpl.

  split.

  + (* The residual branch sequence is finite *)
    exact Hfinite.

  + (* Every selected residual continuation is finite *)
    intros lbl sr U0 Hsel.

    left.
    apply Hselected with (lbl := lbl) (sr := sr).
    exact Hsel.

- (* sbm2_nil *)
  intros p0 l0 s0 xs seen.

  unfold send_finite_Pbranches.
  intros q Hwf Hfb.

  split.

  + (* conil is finite *)
    constructor.

  + (* No selectable branches in conil *)
    intros lbl sr U0 Hsel.
    inversion Hsel.
- (* sbm2_fresh *)
  intros p0 l0 s0 xs lbl sr U0 ys seen T0
         Hfresh Hsel Hstep IHstep
         Htail IHtail.

  unfold send_finite_Pbranches.
  intros q Hwf Hfb.
  assert (HfiniteU0 : finitely_branchingC U0).
  {
    apply IHstep.

    - (* Well-formedness of T0 *)
      eapply wf_branchingC_member_send.
      + exact Hwf.
      + apply copathsel_member.
        exact Hsel.

    - (* Finite branching of T0 *)
      eapply finitely_branchingC_member_send.
      + exact Hfb.
      + exact Hsel.
  } 
unfold send_finite_Pbranches in IHtail.
specialize (IHtail q Hwf Hfb).

destruct IHtail as [HfiniteTail HselectedTail].
split.

- constructor.
  exact HfiniteTail.
- intros lbl0 sr0 U1 HselU1.

  inversion HselU1; subst.
  right.
  exact HfiniteU0.
specialize (HselectedTail lbl0 sr0 U1 H7).

destruct HselectedTail as [Hseen | Hfinite].

- simpl in Hseen.
  destruct Hseen as [Heq | Hseen].

  + (* Impossible: lbl = lbl0 *)
    exfalso.
    apply H6.
    inversion Heq.
    reflexivity.

  + (* Key already belongs to seen *)
    left.
    exact Hseen.

- (* Continuation is finitely branching *)
  right.
  exact Hfinite.

specialize (HselectedTail lbl0 sr0 U1 H7).

destruct HselectedTail as [Hseen | Hfinite].

- (* Key belongs to the extended seen list *)
  simpl in Hseen.
  destruct Hseen as [Heq | Hseen].

  + (* Impossible: sr = sr0 *)
    exfalso.
    apply H6.
    inversion Heq.
    reflexivity.

  + (* Key belongs to the original seen list *)
    left.
    exact Hseen.

- (* Continuation is finitely branching *)
  right.
  exact Hfinite.
- (* sbm2_shadowed *)
  intros p0 l0 s0 xs lbl sr U0 ys seen
         Hin Htail IHtail.

  unfold send_finite_Pbranches.
  intros q Hwf Hfb.

  unfold send_finite_Pbranches in IHtail.
  specialize (IHtail q Hwf Hfb).

  destruct IHtail as [HfiniteTail HselectedTail].

  split.

  + (* Finite residual sequence *)
    constructor.
    exact HfiniteTail.

  + (* Selected continuations *)
    intros lbl0 sr0 U1 Hsel.

    inversion Hsel; subst.

    * (* Head branch: already in seen *)
      left.
      exact Hin.

    * (* Tail selection *)
      eapply HselectedTail.
      eassumption.

    * (* Tail selection, sort mismatch *)
      eapply HselectedTail.
      eassumption.
- (* sfm2_nil *)
  intros p0 l0 s0.

  unfold send_finite_Pforall.
  intros q Hwf Hfb.

  split.

  + (* Empty sequence is finite *)
    constructor.

  + (* No selectable continuations *)
    intros lbl sr U0 Hsel.
    inversion Hsel.
- (* sfm2_cons *)
  intros p0 l0 s0 lbl sr T0 U0 xs ys
         Hstep IHstep Htail IHtail.

  unfold send_finite_Pforall.
  intros q Hwf Hfb.

  (* Finiteness of the new head continuation *)
  assert (HfiniteU0 : finitely_branchingC U0).
  {
    unfold send_finite_P in IHstep.
    apply IHstep.

    - (* Well-formedness of T0 *)
      eapply wf_branchingC_member_receive.
      + exact Hwf.
      + apply copathsel_member.
        constructor.

eapply finitely_branchingC_member_receive.
- exact Hfb.
- constructor.
}

unfold send_finite_Pforall in IHtail.
split.

assert (Hwftail : wf_branchingC (q & xs)).
{
  eapply wf_branchingC_receive_tail.
  exact Hwf.
}

assert (Hfbtail : finitely_branchingC (q & xs)).
{
  apply wf_branchingC_finitely_branching.
  exact Hwftail.
}

destruct (IHtail q Hwftail Hfbtail)
  as [Hfinys Hall].

constructor.
exact Hfinys.

assert (Hwftail : wf_branchingC (q & xs)).
{
  eapply wf_branchingC_receive_tail.
  exact Hwf.
}

assert (Hfbtail : finitely_branchingC (q & xs)).
{
  apply wf_branchingC_finitely_branching.
  exact Hwftail.
}

destruct (IHtail q Hwftail Hfbtail)
  as [Hfinys Hall].

intros lbl0 sr0 U1 Hsel.

inversion Hsel; subst.

- (* Head selected *)
  exact HfiniteU0.

- (* Different label: selection from tail *)
  eapply Hall.
  eassumption.

- (* Different sort: selection from tail *)
  eapply Hall.
  eassumption.
Qed.


CoInductive sti : Type :=
  | sti_end : sti
  | sti_send :
      string -> list (string * sort * sti) -> sti
  | sti_receive :
      string -> list (string * sort * sti) -> sti.

Inductive branches_equiv
  (R : st -> sti -> Prop)
  : coseq (string * sort * st) ->
    list (string * sort * sti) -> Prop :=

| branches_equiv_nil :
    branches_equiv R conil []

| branches_equiv_cons :
    forall l s T U xs ys,
      R T U ->
      branches_equiv R xs ys ->
      branches_equiv R
        (cocons (l, s, T) xs)
        ((l, s, U) :: ys).

Definition st_sti_equivR
  (R : st -> sti -> Prop)
  (T : st) (U : sti) : Prop :=
  match T, U with

  | st_end, sti_end =>
      True

  | st_send p xs, sti_send q ys =>
      p = q /\
      branches_equiv R xs ys

  | st_receive p xs, sti_receive q ys =>
      p = q /\
      branches_equiv R xs ys

  | _, _ =>
      False
  end.

Definition st_sti_equiv (T : st) (U : sti) : Prop :=
  paco2 st_sti_equivR bot2 T U.

Inductive coseq_list_equiv {A : Type}
  : coseq A -> list A -> Prop :=

| cle_nil :
    coseq_list_equiv conil []

| cle_cons :
    forall x xs ys,
      coseq_list_equiv xs ys ->
      coseq_list_equiv
        (cocons x xs)
        (x :: ys).

Lemma finite_coseq_has_list :
  forall (A : Type) (xs : coseq A),
    finite_coseq xs ->
    exists ys : list A,
      coseq_list_equiv xs ys.
Proof.
  intros A xs Hfinite.
  induction Hfinite as [| x xs Hfin IH].

  - exists [].
    constructor.

  - destruct IH as [ys Hequiv].
    exists (x :: ys).
    constructor.
    exact Hequiv.
Qed.

Lemma finitely_branching_one_step :
  forall T,
    finitely_branchingC T ->
    finitely_branchingR finitely_branchingC T.
Proof.
  intros T Hfin.

  unfold finitely_branchingC in Hfin.
  punfold Hfin.
  2: apply finitely_branchingR_mon.

  eapply finitely_branchingR_mon.
  - exact Hfin.
  - intros X HX.
    destruct HX as [HX | HX].
    + exact HX.
    + destruct HX.
Qed.

Inductive sti_layer (A : Type) : Type :=
| layer_end : sti_layer A
| layer_send :
    string -> list (string * sort * A) -> sti_layer A
| layer_receive :
    string -> list (string * sort * A) -> sti_layer A.

Lemma wf_branching_has_finite_layer :
  forall T,
    wf_branchingC T ->
    match T with
    | st_end => True
    | st_send _ xs =>
        exists ys : list (string * sort * st),
          coseq_list_equiv xs ys
    | st_receive _ xs =>
        exists ys : list (string * sort * st),
          coseq_list_equiv xs ys
    end.
Proof.
  intros T Hwf.
  unfold wf_branchingC in Hwf.
  punfold Hwf.
  2: apply wf_branchingR_mon.

  destruct T; simpl in *.
  - easy.
  - destruct Hwf as [Hfinite _].
    now apply finite_coseq_has_list.
  - destruct Hwf as [Hfinite _].
    now apply finite_coseq_has_list.
Qed.

From Coq Require Import Logic.ClassicalEpsilon.

Check constructive_indefinite_description.

Definition observe_st
  (T : st)
  (Hwf : wf_branchingC T)
  : sti_layer st.
Proof.
  destruct T as [ | p xs | p xs].

  - (* st_end *)
exact (layer_end st).

  - (* st_send *)
    assert (Hex :
      exists ys : list (string * sort * st),
        coseq_list_equiv xs ys).
    {
      exact (wf_branching_has_finite_layer (st_receive p xs) Hwf).
    }


exact
  (layer_receive st p
    (proj1_sig
      (constructive_indefinite_description
        (fun ys : list (string * sort * st) =>
          coseq_list_equiv xs ys)
        Hex))).

(*     destruct
      (indefinite_description
         (fun ys : list (string * sort * st) =>
            coseq_list_equiv xs ys)
         Hex)
      as [ys Hequiv].

    exact (layer_send p ys). *)

  - (* st_receive *)
    assert (Hex :
      exists ys : list (string * sort * st),
        coseq_list_equiv xs ys).
    {
exact
  (wf_branching_has_finite_layer
     (st_send p xs) Hwf).
    }

pose proof
  (constructive_indefinite_description
    (fun ys : list (string * sort * st) =>
       coseq_list_equiv xs ys)
    Hex)
  as Hchoice.

exact (layer_send st p (proj1_sig Hchoice)).
Defined.

Definition observe_st_spec
  (T : st)
  (L : sti_layer st) : Prop :=
  match T, L with
  | st_end, layer_end => True

  | st_receive p xs, layer_receive q ys =>
      p = q /\ coseq_list_equiv xs ys

  | st_send p xs, layer_send q ys =>
      p = q /\ coseq_list_equiv xs ys

  | _, _ => False
  end.

Lemma observe_st_correct :
  forall T (Hwf : wf_branchingC T),
    observe_st_spec T (observe_st T Hwf).
Proof.
  intros T Hwf.
  destruct T as [| p xs | p xs].

  - (* st_end *)
    unfold observe_st_spec.
    unfold observe_st.
    simpl.
    easy.

  - (* st_receive *)
    unfold observe_st_spec.
    unfold observe_st.
    simpl.

    match goal with
    | |- context [
        constructive_indefinite_description ?P ?Hex
      ] =>
        destruct (constructive_indefinite_description P Hex)
          as [ys Hequiv]
    end.

    simpl.
    split.
    + reflexivity.
    + exact Hequiv.

  - (* st_send *)
    unfold observe_st_spec.
    unfold observe_st.
    simpl.

    match goal with
    | |- context [
        constructive_indefinite_description ?P ?Hex
      ] =>
        destruct (constructive_indefinite_description P Hex)
          as [ys Hequiv]
    end.

    simpl.
    split.
    + reflexivity.
    + exact Hequiv.
Qed.

Definition wf_st := { T : st | wf_branchingC T }.

Fixpoint lift_wf_branches
  (xs : list (string * sort * st))
  (Hwf : forall lbl sr T,
      In (lbl, sr, T) xs ->
      wf_branchingC T)
  {struct xs}
  : list (string * sort * wf_st).
Proof.
  destruct xs as [| [[lbl sr] T] xs].

  - (* nil *)
    exact [].

  - (* cons *)
    refine
      ((lbl, sr, exist _ T _) ::
       lift_wf_branches xs _).

    + (* Head continuation is well-formed *)
      apply Hwf with (sr := sr) (lbl := lbl).
      simpl.
      left.
      reflexivity.

    + (* Every tail continuation is well-formed *)
      intros lbl0 sr0 T0 Hin.
      apply Hwf with (sr := sr0) (lbl := lbl0).
      simpl.
      right.
      exact Hin.
Defined.

Lemma coseq_list_equiv_member :
  forall (A : Type)
         (xs : coseq A)
         (ys : list A)
         (x : A),
    coseq_list_equiv xs ys ->
    In x ys ->
    coseq_member x xs.
Proof.
  intros A xs ys x Hequiv.
  induction Hequiv.

  - (* Empty *)
    simpl.
    contradiction.

  - (* Cons *)
    simpl.
    intros [Heq | Hin].

    + subst.
      constructor.

    + econstructor 2.
      apply IHHequiv.
      exact Hin.
Qed.

Lemma wf_branchingC_list_members_receive :
  forall p xs ys,
    wf_branchingC (st_receive p xs) ->
    coseq_list_equiv xs ys ->
    forall lbl sr T,
      In (lbl, sr, T) ys ->
      wf_branchingC T.
Proof.
  intros p xs ys Hwf Hequiv lbl sr T Hin.

  apply coseq_list_equiv_member
    with (x := (lbl, sr, T)) in Hequiv;
    [| exact Hin].

  eapply wf_branchingC_member_receive.
  - exact Hwf.
  - exact Hequiv.
Qed.

Lemma wf_branchingC_list_members_send :
  forall p xs ys,
    wf_branchingC (st_send p xs) ->
    coseq_list_equiv xs ys ->
    forall lbl sr T,
      In (lbl, sr, T) ys ->
      wf_branchingC T.
Proof.
  intros p xs ys Hwf Hequiv lbl sr T Hin.

  apply coseq_list_equiv_member
    with (x := (lbl, sr, T)) in Hequiv;
    [| exact Hin].

  eapply wf_branchingC_member_send.
  - exact Hwf.
  - exact Hequiv.
Qed.

Definition observe_wf_st
  (X : wf_st)
  : sti_layer wf_st.
Proof.
  destruct X as [T Hwf].
  destruct T as [| p xs | p xs].

  - (* st_end *)
    exact (layer_end wf_st).

  - (* st_receive *)
    pose proof
      (wf_branching_has_finite_layer
         (st_receive p xs) Hwf)
      as Hex.

    destruct
      (constructive_indefinite_description
         (fun zs : list (string * sort * st) =>
            coseq_list_equiv xs zs)
         Hex)
      as [zs Hequiv].

    refine
      (layer_receive wf_st p
        (lift_wf_branches zs _)).

    intros lbl sr T Hin.
    eapply wf_branchingC_list_members_receive.
    + exact Hwf.
    + exact Hequiv.
    + exact Hin.

  - (* st_send *)
    pose proof
      (wf_branching_has_finite_layer
         (st_send p xs) Hwf)
      as Hex.

    destruct
      (constructive_indefinite_description
         (fun zs : list (string * sort * st) =>
            coseq_list_equiv xs zs)
         Hex)
      as [zs Hequiv].

    refine
      (layer_send wf_st p
        (lift_wf_branches zs _)).

    intros lbl sr T Hin.
    eapply wf_branchingC_list_members_send.
    + exact Hwf.
    + exact Hequiv.
    + exact Hin.
Defined.

CoInductive wf_st_to_sti_rel : wf_st -> sti -> Prop :=

| wf_st_to_sti_end :
    forall X,
      observe_wf_st X = layer_end wf_st ->
      wf_st_to_sti_rel X sti_end

| wf_st_to_sti_send :
    forall X p xs ys,
      observe_wf_st X = layer_send wf_st p xs ->
      wf_branches_to_sti_rel xs ys ->
      wf_st_to_sti_rel X (sti_send p ys)

| wf_st_to_sti_receive :
    forall X p xs ys,
      observe_wf_st X = layer_receive wf_st p xs ->
      wf_branches_to_sti_rel xs ys ->
      wf_st_to_sti_rel X (sti_receive p ys)

with wf_branches_to_sti_rel :
  list (string * sort * wf_st) ->
  list (string * sort * sti) -> Prop :=

| wf_branches_nil :
    wf_branches_to_sti_rel [] []

| wf_branches_cons :
    forall lbl sr X U xs ys,
      wf_st_to_sti_rel X U ->
      wf_branches_to_sti_rel xs ys ->
      wf_branches_to_sti_rel
        ((lbl, sr, X) :: xs)
        ((lbl, sr, U) :: ys).

Fixpoint approximate_sti
  (n : nat)
  (X : wf_st) {struct n} : sti :=
  match n with
  | O => sti_end
  | S k =>
      match observe_wf_st X with
      | layer_end =>
          sti_end

      | layer_send p xs =>
          sti_send p
            (List.map
               (fun '(lbl, sr, X') =>
                  (lbl, sr, approximate_sti k X'))
               xs)

      | layer_receive p xs =>
          sti_receive p
            (List.map
               (fun '(lbl, sr, X') =>
                  (lbl, sr, approximate_sti k X'))
               xs)
      end
  end.

Fixpoint sti_agree
  (n : nat)
  (T U : sti) : Prop :=
  match n with
  | O => True
  | S k =>
      match T, U with
      | sti_end, sti_end =>
          True

      | sti_send p xs, sti_send q ys =>
          p = q /\
          Forall2
            (fun x y =>
               let '(lbl1, sr1, T1) := x in
               let '(lbl2, sr2, U1) := y in
               lbl1 = lbl2 /\
               sr1 = sr2 /\
               sti_agree k T1 U1)
            xs ys

      | sti_receive p xs, sti_receive q ys =>
          p = q /\
          Forall2
            (fun x y =>
               let '(lbl1, sr1, T1) := x in
               let '(lbl2, sr2, U1) := y in
               lbl1 = lbl2 /\
               sr1 = sr2 /\
               sti_agree k T1 U1)
            xs ys

      | _, _ => False
      end
  end.

(*contained based*)

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Vectors.Fin.

Record wf_branch_shape : Type := {
  wf_shape_branches : list (string * sort * wf_st)
}.

Definition wf_branch_pos (sh : wf_branch_shape) : Type :=
  Fin.t (List.length (wf_shape_branches sh)).

CoInductive stc : Type :=
| stc_end : stc
| stc_send :
    forall (p : string) (sh : wf_branch_shape),
      (wf_branch_pos sh -> stc) -> stc
| stc_receive :
    forall (p : string) (sh : wf_branch_shape),
      (wf_branch_pos sh -> stc) -> stc.

CoFixpoint infinite_stc (p : string) (sh : wf_branch_shape) : stc :=
  stc_send p sh
    (fun _ => infinite_stc p sh).

From Coq Require Import Vectors.Vector Vectors.Fin.
Import ListNotations.

Definition fin_nth {A : Type}
  (xs : list A)
  (i : Fin.t (List.length xs)) : A :=
  Vector.nth (Vector.of_list xs) i.

Definition wf_branch_next
  (sh : wf_branch_shape)
  (i : wf_branch_pos sh) : wf_st :=
  let '(_, _, X) :=
    fin_nth (wf_shape_branches sh) i
  in X.

CoFixpoint wf_st_to_stc (X : wf_st) : stc :=
  match observe_wf_st X with
  | layer_end =>
      stc_end

  | layer_send p xs =>
      let sh := {| wf_shape_branches := xs |} in
      stc_send p sh
        (fun i =>
          wf_st_to_stc (wf_branch_next sh i))

  | layer_receive p xs =>
      let sh := {| wf_shape_branches := xs |} in
      stc_receive p sh
        (fun i =>
          wf_st_to_stc (wf_branch_next sh i))
  end.

(* Definition stc_branches_equiv
  (R : st -> stc -> Prop)
  (xs : coseq (string * sort * st))
  (sh : wf_branch_shape)
  (next : wf_branch_pos sh -> stc) : Prop :=

  exists ys : list (string * sort * st),
    coseq_list_equiv xs ys /\

    exists Hlen :
      List.length ys =
      List.length (wf_shape_branches sh),

    forall i : wf_branch_pos sh,

      let j :=
        eq_rect
          (List.length (wf_shape_branches sh))
          Fin.t i
          (List.length ys)
          (eq_sym Hlen)
      in

      let '(lbl, sr, T) := fin_nth ys j in

      let '(lbl', sr', X) :=
        fin_nth (wf_shape_branches sh) i
      in

      lbl = lbl' /\
      sr = sr' /\
      proj1_sig X = T /\
      R T (next i).
 *)
Definition erase_wf_branch
  (b : string * sort * wf_st)
  : string * sort * st :=
  let '(lbl, sr, X) := b in
  (lbl, sr, proj1_sig X).

Definition stc_branches_equiv
  (R : st -> stc -> Prop)
  (xs : coseq (string * sort * st))
  (sh : wf_branch_shape)
  (next : wf_branch_pos sh -> stc) : Prop :=

  coseq_list_equiv xs
    (List.map erase_wf_branch (wf_shape_branches sh))

  /\

  forall i : wf_branch_pos sh,
    let '(_, _, X) :=
      fin_nth (wf_shape_branches sh) i
    in
    R (proj1_sig X) (next i).

Definition st_stc_equivR
  (R : st -> stc -> Prop)
  (T : st) (U : stc) : Prop :=
  match T, U with
  | st_end, stc_end =>
      True

  | st_send p xs, stc_send q sh next =>
      p = q /\
      stc_branches_equiv R xs sh next

  | st_receive p xs, stc_receive q sh next =>
      p = q /\
      stc_branches_equiv R xs sh next

  | _, _ =>
      False
  end.

Definition st_stc_equiv : st -> stc -> Prop :=
  paco2 st_stc_equivR bot2.

Lemma st_stc_equivR_mon :
  monotone2 st_stc_equivR.
Proof.
  unfold monotone2.
  intros T U R R' Hle H.

  unfold st_stc_equivR in *.

  destruct T as [| p xs | p xs];
  destruct U as [| q sh next | q sh next];
  simpl in *; try contradiction; auto.

  all: destruct Hle as [Heq Hbranches].
  all: split; [exact Heq |].

  all: unfold stc_branches_equiv in *.
all: destruct Hbranches as [Hequiv Hnext].
all: split.
exact Hequiv.

intro i.
specialize (Hnext i).
destruct (fin_nth (wf_shape_branches sh) i)
       as [[lbl sr] X].
simpl in *.
apply H.
exact Hnext.
exact Hequiv.

intro i.
specialize (Hnext i).

destruct (fin_nth (wf_shape_branches sh) i)
  as [[lbl sr] X].

simpl in *.
apply H.
exact Hnext.
Qed.


Lemma lift_wf_branches_length :
  forall xs Hwf,
    List.length (lift_wf_branches xs Hwf) =
    List.length xs.
Proof.
  intros xs.
  induction xs as [| [[lbl sr] T] xs IH].
  - intros Hwf.
    reflexivity.
  - intros Hwf.
    simpl.
    f_equal.
    apply IH.
Qed.

Lemma lift_wf_branches_erase :
  forall zs Hwf,
    List.map
      (fun '(lbl, sr, X) =>
         (lbl, sr, proj1_sig X))
      (lift_wf_branches zs Hwf)
    = zs.
Proof.
  induction zs as [| [[lbl sr] T] zs IH].
  - intros Hwf.
    reflexivity.
  - intros Hwf.
    simpl.
    f_equal.
    apply IH.
Qed.

Lemma vector_nth_map_triple :
  forall (n : nat)
         (v : Vector.t (string * sort * wf_st) n)
         (i : Fin.t n),
    let '(lbl, sr, X) := Vector.nth v i in
    let '(lbl', sr', T) :=
      Vector.nth
        (Vector.map
          (fun '(l, s, X0) =>
             (l, s, proj1_sig X0))
          v) i
    in
    lbl = lbl' /\
    sr = sr' /\
    proj1_sig X = T.
Proof.
  intros n v i.

  erewrite VectorSpec.nth_map.
  2: reflexivity.

  remember (Vector.nth v i) as b eqn:Hb.

  destruct b as [[lbl sr] X].

  cbn beta iota zeta.
assert (Hmap :
  VectorDef.nth
    (Vector.map
      (fun '(l, s, X0) =>
         (l, s, proj1_sig X0))
      v) i
  =
  (let '(l, s, X0) := Vector.nth v i in
   (l, s, proj1_sig X0))).
{
  erewrite VectorSpec.nth_map.
  reflexivity.
  easy.
}

apply (f_equal
  (fun b : string * sort * wf_st =>
     let '(l, s, X0) := b in
     (l, s, proj1_sig X0))) in Hb.

pose proof Hb as Htriple.
destruct (Vector.nth v i) as [[l s] Y] eqn:E.
simpl in Htriple.
injection Htriple as H1 H2 H3.
destruct (Vector.nth v i) as [[l0 s0] Y0] eqn:Enth.

rewrite <- Enth in E.
inversion E; subst.

cbn. subst.
set (b := Vector.nth v i) in *.
destruct b as [[l1 s1] Y1].
cbn in *.
subst.
repeat split; auto.

assert (Hlookup :
  (let '(a, b, Z) := VectorDef.nth v i in
   (a, b, proj1_sig Z))
  = (l, s, proj1_sig Y)).
{
  rewrite <- (VectorSpec.nth_map
    (fun '(a, b, Z) => (a, b, proj1_sig Z)) v i).
  exact Hmap.
  easy.
}

change (
  let '(a, b, Z) :=
    (let '(a, b, Z) := VectorDef.nth v i in
     (a, b, proj1_sig Z))
  in
  l = a /\ s = b /\ proj1_sig X = Z
).

rewrite Hlookup.
cbn.
repeat split; try reflexivity.
exact H3.
Qed.


Lemma wf_st_to_stc_correct :
  forall X : wf_st,
    st_stc_equiv
      (proj1_sig X)
      (wf_st_to_stc X).
Proof.
  pcofix CIH.
  intro X.

  pfold.
destruct X as [T Hwf].
destruct T as [| p xs | p xs].


  constructor.

unfold st_stc_equivR.
cbn [wf_st_to_stc].
set (X := exist (fun T => wf_branchingC T)
                (p & xs) Hwf).

remember (observe_wf_st X) as L eqn:Hobs.

unfold X in Hobs.
unfold observe_wf_st in Hobs.
cbn in Hobs.
destruct L as [| q ys | q ys].

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p & xs) Hwf))
  as [zs Hequiv] eqn:Hchoice
  in Hobs.

cbn in Hobs.
discriminate Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p & xs) Hwf))
  as [zs Hequiv] eqn:Hchoice
  in Hobs.

cbn in Hobs.
discriminate Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p & xs) Hwf))
  as [zs Hequiv] eqn:Hchoice in Hobs.

cbn in Hobs.
injection Hobs as Hq Hys.
subst q.
subst ys.
cbn [proj1_sig].
split.
- reflexivity.
- 
unfold stc_branches_equiv.

split.
-
cbn [wf_shape_branches].

rewrite lift_wf_branches_erase.

exact Hequiv.

intro i.
unfold wf_branch_next.
cbn [wf_shape_branches].

set (bs :=
  lift_wf_branches zs
    (fun lbl sr T Hin =>
       wf_branchingC_list_members_receive
         p xs zs Hwf Hequiv lbl sr T Hin)).

set (b := fin_nth bs i).

destruct b as [[lbl sr] X0].

cbn.
right.
apply CIH.

cbn [proj1_sig].

unfold wf_st_to_stc at 1.
cbn.

set (X := exist (fun T => wf_branchingC T)
                (p ! xs) Hwf).

remember (observe_wf_st X) as L eqn:Hobs.

destruct L as [| q ys | q ys].

unfold X in Hobs.
unfold observe_wf_st in Hobs.
cbn in Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p ! xs) Hwf))
  as [zs Hequiv] eqn:Hchoice in Hobs.

cbn in Hobs.
discriminate Hobs.


unfold X in Hobs.
unfold observe_wf_st in Hobs.
cbn in Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p ! xs) Hwf))
  as [zs Hequiv] eqn:Hchoice in Hobs.

cbn in Hobs.

injection Hobs as Hq Hys.
subst q.
subst ys.

cbn [proj1_sig].

rewrite Hchoice.
cbn.

split.
- reflexivity.
- unfold stc_branches_equiv.
  split.
  + cbn [wf_shape_branches].
    rewrite lift_wf_branches_erase.
    exact Hequiv.

intro i.

set (bs :=
  lift_wf_branches zs
    (fun lbl sr T Hin =>
       wf_branchingC_list_members_send
         p xs zs Hwf Hequiv lbl sr T Hin)).

fold wf_st_to_stc.

unfold wf_branch_next.
cbn [wf_shape_branches].

remember (fin_nth bs i) as b eqn:Hb.

destruct b as [[lbl sr] X0].

cbn.
right.
apply CIH.

unfold X in Hobs.
unfold observe_wf_st in Hobs.
cbn in Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p ! xs) Hwf))
  as [zs Hequiv] eqn:Hchoice in Hobs.

cbn in Hobs.
discriminate Hobs.
Qed.

Theorem wf_branching_st_to_stc :
  forall T,
    wf_branchingC T ->
    exists U : stc,
      st_stc_equiv T U.
Proof.
  intros T Hwf.

  exists (wf_st_to_stc (exist wf_branchingC T Hwf)).

  exact
    (wf_st_to_stc_correct
       (exist wf_branchingC T Hwf)).
Qed.

Theorem wf_branching_st_to_stc_explicit :
  forall T (Hwf : wf_branchingC T),
    st_stc_equiv T
      (wf_st_to_stc (exist wf_branchingC T Hwf)).
Proof.
  intros T Hwf.
  exact
    (wf_st_to_stc_correct
       (exist wf_branchingC T Hwf)).
Qed.

Theorem wf_st_to_stc_witness :
  forall X : wf_st,
    exists U : stc,
      wf_st_to_stc X = U /\
      st_stc_equiv (proj1_sig X) U.
Proof.
  intro X.
  exists (wf_st_to_stc X).
  split.
  - reflexivity.
  - apply wf_st_to_stc_correct.
Qed.

Definition stc_branches_bisim
  (R : stc -> stc -> Prop)
  (sh1 sh2 : wf_branch_shape)
  (next1 : wf_branch_pos sh1 -> stc)
  (next2 : wf_branch_pos sh2 -> stc) : Prop :=

  exists Hlen :
    List.length (wf_shape_branches sh1) =
    List.length (wf_shape_branches sh2),

    forall i : wf_branch_pos sh1,

      let j :=
        eq_rect
          (List.length (wf_shape_branches sh1))
          Fin.t i
          (List.length (wf_shape_branches sh2))
          Hlen
      in

      let '(l1, s1, _) :=
        fin_nth (wf_shape_branches sh1) i
      in

      let '(l2, s2, _) :=
        fin_nth (wf_shape_branches sh2) j
      in

      l1 = l2 /\
      s1 = s2 /\
      R (next1 i) (next2 j).

Definition stc_equivR
  (R : stc -> stc -> Prop)
  (T U : stc) : Prop :=
  match T, U with

  | stc_end, stc_end =>
      True

  | stc_send p sh1 next1,
    stc_send q sh2 next2 =>
      p = q /\
      stc_branches_bisim R sh1 sh2 next1 next2

  | stc_receive p sh1 next1,
    stc_receive q sh2 next2 =>
      p = q /\
      stc_branches_bisim R sh1 sh2 next1 next2

  | _, _ =>
      False
  end.

Definition stc_equiv : stc -> stc -> Prop :=
  paco2 stc_equivR bot2.

Axiom stcExt :
  forall T U : stc,
    stc_equiv T U ->
    T = U.

From Coq Require Import Logic.ProofIrrelevance.

Lemma wf_st_to_stc_proof_irrelevant_eq :
  forall T
         (H1 H2 : wf_branchingC T),
    wf_st_to_stc (exist wf_branchingC T H1) =
    wf_st_to_stc (exist wf_branchingC T H2).
Proof.
  intros T H1 H2.
  assert (Heq : H1 = H2).
  {
    apply proof_irrelevance.
  }
  subst H2.
  reflexivity.
Qed.

Lemma stc_equiv_refl :
  forall U : stc,
    stc_equiv U U.
Proof.
  pcofix CIH.
  intro U.
  pfold.

  destruct U as
    [| p sh next
     | p sh next].

  - (* stc_end *)
    simpl.
    easy.

  - (* stc_send *)
    simpl.
    split.
    + reflexivity.
    + unfold stc_branches_bisim.
      exists eq_refl.
      intro i.

      simpl.
destruct (fin_nth (wf_shape_branches sh) i)
  as [[lbl sr] X] eqn:Hnth.

cbn.
repeat split; try reflexivity.

right.
apply CIH.


  - (* stc_receive *)
    simpl.
    split.
    + reflexivity.
    + unfold stc_branches_bisim.
      exists eq_refl.
      intro i.

      simpl.
destruct (fin_nth (wf_shape_branches sh) i)
  as [[lbl sr] X] eqn:Hnth.

cbn.
repeat split; try reflexivity.

right.
apply CIH.
Qed.

Lemma wf_st_to_stc_proof_irrelevant :
  forall T
         (H1 H2 : wf_branchingC T),
    stc_equiv
      (wf_st_to_stc (exist wf_branchingC T H1))
      (wf_st_to_stc (exist wf_branchingC T H2)).
Proof.
  intros T H1 H2.

  rewrite
    (wf_st_to_stc_proof_irrelevant_eq T H1 H2).

  apply stc_equiv_refl.
Qed.


Lemma wf_st_to_stc_respects_equiv_eq :
  forall X Y : wf_st,
    st_equivC (proj1_sig X) (proj1_sig Y) ->
    wf_st_to_stc X = wf_st_to_stc Y.
Proof.
  intros [T HT] [U HU] Hequiv.
  simpl in Hequiv.

  apply stExt in Hequiv.
  subst U.

  apply wf_st_to_stc_proof_irrelevant_eq.
Qed.

Lemma wf_st_to_stc_respects_equiv :
  forall X Y : wf_st,
    st_equivC (proj1_sig X) (proj1_sig Y) ->
    stc_equiv
      (wf_st_to_stc X)
      (wf_st_to_stc Y).
Proof.
  intros [T HT] [U HU] Hequiv.

  simpl in Hequiv.

  apply stExt in Hequiv.
  subst U.

  apply wf_st_to_stc_proof_irrelevant.
Qed.

Record branch_shape : Type := {
  branch_labels : list (string * sort)
}.

Definition branch_pos (sh : branch_shape) : Type :=
  Fin.t (List.length (branch_labels sh)).

CoInductive stc_pure : Type :=
| stc_pure_end : stc_pure

| stc_pure_send :
    forall (p : string) (sh : branch_shape),
      (branch_pos sh -> stc_pure) ->
      stc_pure

| stc_pure_receive :
    forall (p : string) (sh : branch_shape),
      (branch_pos sh -> stc_pure) ->
      stc_pure.

Definition branch_keys
  (xs : list (string * sort * wf_st))
  : list (string * sort) :=
  List.map
    (fun '(lbl, sr, _) => (lbl, sr))
    xs.

Definition shape_of_branches
  (xs : list (string * sort * wf_st))
  : branch_shape :=
  {| branch_labels := branch_keys xs |}.

Lemma branch_keys_length :
  forall xs,
    List.length (branch_keys xs) =
    List.length xs.
Proof.
  intro xs.
  unfold branch_keys.
  rewrite List.map_length.
  reflexivity.
Qed.

Definition pure_branch_next
  (xs : list (string * sort * wf_st))
  (i : branch_pos (shape_of_branches xs))
  : wf_st :=
  let j :=
    eq_rect
      (List.length (branch_keys xs))
      Fin.t i
      (List.length xs)
      (branch_keys_length xs)
  in
  let '(_, _, X) := fin_nth xs j in
  X.

CoFixpoint wf_st_to_stc_pure
  (X : wf_st) : stc_pure :=
  match observe_wf_st X with

  | layer_end =>
      stc_pure_end

  | layer_send p xs =>
      stc_pure_send p
        (shape_of_branches xs)
        (fun i =>
          wf_st_to_stc_pure
            (pure_branch_next xs i))

  | layer_receive p xs =>
      stc_pure_receive p
        (shape_of_branches xs)
        (fun i =>
          wf_st_to_stc_pure
            (pure_branch_next xs i))

  end.

Definition erase_pure_keys
  (xs : list (string * sort * st))
  : list (string * sort) :=
  List.map (fun '(l, s, _) => (l, s)) xs.

Definition stc_pure_branches_equiv
  (R : st -> stc_pure -> Prop)
  (xs : coseq (string * sort * st))
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure) : Prop :=

  exists ys : list (string * sort * st),

    coseq_list_equiv xs ys /\

    exists Hlen :
      List.length ys =
      List.length (branch_labels sh),

      forall i : branch_pos sh,

        let j :=
          eq_rect
            (List.length (branch_labels sh))
            Fin.t i
            (List.length ys)
            (eq_sym Hlen)
        in

        let '(lbl, sr, T) := fin_nth ys j in
        let '(lbl', sr') :=
          fin_nth (branch_labels sh) i in

        lbl = lbl' /\
        sr = sr' /\
        R T (next i).

Definition st_stc_pure_equivR
  (R : st -> stc_pure -> Prop)
  (T : st)
  (U : stc_pure) : Prop :=
  match T, U with

  | st_end, stc_pure_end =>
      True

  | st_send p xs, stc_pure_send q sh next =>
      p = q /\
      stc_pure_branches_equiv R xs sh next

  | st_receive p xs, stc_pure_receive q sh next =>
      p = q /\
      stc_pure_branches_equiv R xs sh next

  | _, _ =>
      False
  end.

Definition st_stc_pure_equiv : st -> stc_pure -> Prop :=
  paco2 st_stc_pure_equivR bot2.

Lemma st_stc_pure_equivR_mon :
  monotone2 st_stc_pure_equivR.
Proof.
  unfold monotone2.
  intros T U R R' Hle Hrel.

  destruct T as [| p xs | p xs];
  destruct U as [| q sh next | q sh next];
  simpl in *;
  try contradiction;
  auto.

all: destruct Hle as [Heq Hbranches].
all: split; [exact Heq |].
all: unfold stc_pure_branches_equiv in *.

all: destruct Hbranches as
  [ys [Hequiv [Hlen Hpositions]]].

all: exists ys.
all: split; [exact Hequiv |].

all: exists Hlen.
all: intro i.

all: specialize (Hpositions i).

all: destruct
  (fin_nth ys
    (eq_rect
      (List.length (branch_labels sh))
      Fin.t i
      (List.length ys)
      (eq_sym Hlen)))
  as [[lbl sr] T0].

all: destruct
  (fin_nth (branch_labels sh) i)
  as [lbl' sr'].

all: cbn in *.

all: destruct Hpositions as
  [Hlbl [Hsort Hrec]].

all: repeat split; try assumption.

all: apply Hrel.
all: exact Hrec.
Qed.

Definition example_tree
  (p q : string)
  (s1 s2 s3 s4 : sort)
  (T : stc_pure) : stc_pure :=

  stc_pure_send p
    {| branch_labels :=
         [("a"%string, s1);
          ("b"%string, s2);
          ("d"%string, s4)] |}

    (fun i =>
       match i with
       | @Fin.F1 _ =>
           stc_pure_end

       | @Fin.FS _ (@Fin.F1 _) =>
           stc_pure_receive q
             {| branch_labels := [("c"%string, s3)] |}
             (fun _ => stc_pure_end)

       | @Fin.FS _ (@Fin.FS _ _) =>
           T
       end).

From Coq Require Import Logic.FunctionalExtensionality.

Lemma branch_keys_lift_wf :
  forall zs Hmembers,
    branch_keys (lift_wf_branches zs Hmembers) =
    List.map
      (fun '(lbl, sr, _) => (lbl, sr))
      zs.
Proof.
  induction zs as [| [[lbl sr] T] zs IH].

  - (* nil *)
    intros Hmembers.
    reflexivity.

  - (* cons *)
    intros Hmembers.
    unfold branch_keys.
    simpl.
    f_equal.

    apply IH.
Qed.

Lemma nth_map_pure :
  forall (a b : Type)
         (n : nat)
         (f : a -> b)
         (v : Vector.t a n)
         (i : Fin.t n),
    Vector.nth (Vector.map f v) i =
    f (Vector.nth v i).
Proof.
  intros a b n f v i.
  erewrite VectorSpec.nth_map.
  - reflexivity.
  - reflexivity.
Qed.

Lemma vector_nth_map_pure :
  forall (n : nat)
         (v : Vector.t (string * sort * stc_pure) n)
         (i : Fin.t n),
    let '(lbl, sr, U) := Vector.nth v i in
    let '(lbl', sr') :=
      Vector.nth
        (Vector.map
          (fun '(l, s, _) => (l, s))
          v) i
    in
    lbl = lbl' /\ sr = sr'.
Proof.
  intros n v i.

  erewrite VectorSpec.nth_map.
  2: reflexivity.

  remember (Vector.nth v i) as b.
  destruct b as [[lbl sr] U].

  cbn.
  split; reflexivity.
Qed.

Definition pure_branch_length
  (zs : list (string * sort * st))
  (Hmembers :
     forall lbl sr T,
       List.In (lbl, sr, T) zs ->
       wf_branchingC T)
  :
  List.length zs =
  List.length
    (branch_keys (lift_wf_branches zs Hmembers)).
Proof.
  rewrite branch_keys_length.
  symmetry.
  apply lift_wf_branches_length.
Defined.

Definition pure_branch_erase
  (b : string * sort * wf_st)
  : string * sort * st :=
  let '(lbl, sr, X) := b in
  (lbl, sr, proj1_sig X).

Definition pure_branch_key
  (b : string * sort * wf_st)
  : string * sort :=
  let '(lbl, sr, _) := b in
  (lbl, sr).

Lemma vector_nth_branch_observe :
  forall (n : nat)
         (v : Vector.t (string * sort * wf_st) n)
         (i : Fin.t n),

    let b := Vector.nth v i in

    let '(lbl, sr, T) :=
      pure_branch_erase b
    in

    let '(lbl', sr') :=
      pure_branch_key b
    in

    lbl = lbl' /\
    sr = sr' /\
    proj1_sig
      (let '(_, _, X) := b in X)
    = T.
Proof.
  intros n v i.

  destruct (Vector.nth v i)
    as [[lbl sr] X].

  simpl.
  repeat split; reflexivity.
Qed.

Definition pure_branch_observe
  (bs : list (string * sort * wf_st))
  (i : branch_pos (shape_of_branches bs))
  : string * sort * wf_st :=
  fin_nth bs
    (eq_rect
       (List.length (branch_keys bs))
       Fin.t i
       (List.length bs)
       (branch_keys_length bs)).

Lemma pure_branch_next_observe :
  forall bs i,
    pure_branch_next bs i =
    let '(_, _, X) :=
      pure_branch_observe bs i
    in X.
Proof.
  intros bs i.
  reflexivity.
Qed.

From Coq Require Import Program.Equality.

Lemma fin_transport_refl :
  forall (n m : nat)
         (H : n = m)
         (i : Fin.t n),
    match H in (_ = m0) return Fin.t m0 with
    | eq_refl => i
    end =
    eq_rect n Fin.t i m H.
Proof.
  intros n m H i.
  destruct H.
  reflexivity.
Qed.

Fixpoint map_length_eq
  {a b : Type}
  (f : a -> b)
  (xs : list a)
  : List.length xs = List.length (List.map f xs) :=
  match xs with
  | [] => eq_refl
  | _ :: xs' =>
      f_equal S (map_length_eq f xs')
  end.

Lemma fin_transport_F1 :
  forall (n m : nat) (H : n = m),
    eq_rect
      (S n) Fin.t (@Fin.F1 n)
      (S m) (f_equal S H)
    = @Fin.F1 m.
Proof.
  intros n m H.
  destruct H.
  reflexivity.
Qed.

Lemma fin_transport_FS :
  forall (n m : nat)
         (H : n = m)
         (i : Fin.t n),
    eq_rect
      (S n) Fin.t (@Fin.FS n i)
      (S m) (f_equal S H)
    =
    @Fin.FS m
      (eq_rect n Fin.t i m H).
Proof.
  intros n m H i.
  destruct H.
  reflexivity.
Qed.

Lemma fin_nth_map_erase :
  forall (bs : list (string * sort * wf_st))
         (k : Fin.t (List.length bs)),
    fin_nth (List.map erase_wf_branch bs)
      (eq_rect
         (List.length bs)
         Fin.t k
         (List.length (List.map erase_wf_branch bs))
         (map_length_eq erase_wf_branch bs))
    =
    erase_wf_branch (fin_nth bs k).
Proof.
  intro bs.
  induction bs as [| b bs IH].

  - intros k.
    dependent destruction k.

  - intros k.
    dependent destruction k.
    + (* F1 *)
      cbn.
rewrite fin_transport_F1.
cbn.
reflexivity.

    + (* FS *)
      cbn.
rewrite fin_transport_FS.
cbn.
apply IH.      
Qed.

Lemma fin_transport_compose :
  forall (n m k : nat)
         (H1 : n = m)
         (H2 : m = k)
         (i : Fin.t n),
    eq_rect m Fin.t
      (eq_rect n Fin.t i m H1)
      k H2
    =
    eq_rect n Fin.t i k (eq_trans H1 H2).
Proof.
  intros n m k H1 H2 i.
  destruct H1.
  destruct H2.
  reflexivity.
Qed.

(* Lemma fin_nth_erase_lookup :
  forall (bs : list (string * sort * wf_st))
         (zs : list (string * sort * st))
         (Herase : List.map erase_wf_branch bs = zs)
         (k : Fin.t (List.length bs)),
    exists j : Fin.t (List.length zs),
      fin_nth zs j =
      erase_wf_branch (fin_nth bs k).
Proof.
  intros bs zs Herase k.
  subst zs.

  exists
    (eq_rect
       (List.length bs)
       Fin.t k
       (List.length (List.map erase_wf_branch bs))
       (eq_sym (List.map_length erase_wf_branch bs))).

  unfold fin_nth.

revert k.

induction bs as [| b bs IH].

- (* Empty list *)
  intro k.
  dependent destruction k.

- (* Nonempty list *)
  intro k.
  dependent destruction k.

  + (* First position *)
    cbn.
    reflexivity.

  + (* Remaining positions *)
    cbn.
    apply IH.


  (* Relate Vector.of_list (List.map ...) to Vector.map. *)
  rewrite <- VectorSpec.of_list_map.

  erewrite VectorSpec.nth_map.
  - reflexivity.
  - reflexivity.
Qed. *)
(*
Lemma pure_branch_source_lookup :
  forall zs Hmembers
         (i : branch_pos
           (shape_of_branches
             (lift_wf_branches zs Hmembers))),

    let bs := lift_wf_branches zs Hmembers in

    let b := pure_branch_observe bs i in

    exists j : Fin.t (List.length zs),
      fin_nth zs j = pure_branch_erase b.
 *)

Lemma fin_nth_transport_eq :
  forall (A : Type)
         (xs ys : list A)
         (H : xs = ys)
         (i : Fin.t (List.length xs)),
    fin_nth ys
      (eq_rect
         (List.length xs)
         Fin.t i
         (List.length ys)
         (f_equal (@List.length A) H))
    =
    fin_nth xs i.
Proof.
  intros A xs ys H i.
  destruct H.
  reflexivity.
Qed.

Lemma fin_nth_map_forward :
  forall (a b : Type)
         (f : a -> b)
         (xs : list a)
         (k : Fin.t (List.length xs)),
    fin_nth (List.map f xs)
      (eq_rect
         (List.length xs)
         Fin.t k
         (List.length (List.map f xs))
         (map_length_eq f xs))
    =
    f (fin_nth xs k).
Proof.
  intros a b f xs.
  induction xs as [| x xs IH].

  - intro k.
    dependent destruction k.

  - intro k.
    dependent destruction k.

    + cbn.
      rewrite fin_transport_F1.
      reflexivity.

    + cbn.
      rewrite fin_transport_FS.
      cbn.
      apply IH.
Qed.

From Coq Require Import Logic.Eqdep_dec.

Lemma fin_transport_roundtrip :
  forall (n m : nat)
         (H : n = m)
         (i : Fin.t n),
    eq_rect m Fin.t
      (eq_rect n Fin.t i m H)
      n (eq_sym H)
    = i.
Proof.
  intros n m H i.
  destruct H.
  reflexivity.
Qed.

Lemma fin_nth_map_backward :
  forall (a b : Type)
         (f : a -> b)
         (xs : list a)
         (i : Fin.t (List.length (List.map f xs))),
    fin_nth (List.map f xs) i =
    f
      (fin_nth xs
        (eq_rect
           (List.length (List.map f xs))
           Fin.t i
           (List.length xs)
           (List.map_length f xs))).
Proof.
  intros a b f xs i.

  remember
    (List.map_length f xs)
    as Hlen eqn:EH.
subst Hlen.
assert (Hp :
  length_map f xs = eq_sym (map_length_eq f xs)).
{
  apply UIP_dec.
  exact Nat.eq_dec.
}

rewrite Hp.

set (k :=
  eq_rect
    (List.length (List.map f xs))
    Fin.t i
    (List.length xs)
    (eq_sym (map_length_eq f xs))).

pose proof
  (@fin_nth_map_forward a b f xs k)
  as Hmap.

assert (Hround :
  eq_rect
    (List.length xs)
    Fin.t k
    (List.length (List.map f xs))
    (map_length_eq f xs)
  = i).
{
  unfold k.

pose proof
  (fin_transport_roundtrip
     (List.length (List.map f xs))
     (List.length xs)
     (eq_sym (map_length_eq f xs))
     i)
  as Hr.

rewrite eq_sym_involutive in Hr.
exact Hr.

}

rewrite Hround in Hmap.
easy.
Qed.

Lemma fin_nth_branch_keys :
  forall (bs : list (string * sort * wf_st))
         (i : Fin.t (List.length (branch_keys bs))),
    fin_nth (branch_keys bs) i =
    let '(l, s, _) :=
      fin_nth bs
        (eq_rect
           (List.length (branch_keys bs))
           Fin.t i
           (List.length bs)
           (branch_keys_length bs))
    in
    (l, s).
Proof.
  intros bs i.

  unfold branch_keys.

pose proof
  (@fin_nth_map_backward
     (string * sort * wf_st)
     (string * sort)
     (fun '(l, s, _) => (l, s))
     bs i)
  as Hmap.

assert (Hp :
  branch_keys_length bs =
  List.map_length
    (fun '(l, s, _) => (l, s)) bs).
{
  apply UIP_dec.
  exact Nat.eq_dec.
}
rewrite Hp.
exact Hmap.
Qed.

Lemma wf_st_to_stc_pure_correct :
  forall X : wf_st,
    st_stc_pure_equiv
      (proj1_sig X)
      (wf_st_to_stc_pure X).
Proof.
  pcofix CIH.
  intro X.
  pfold.

  destruct X as [T Hwf].
  destruct T as [| p xs | p xs].

  - (* end *)
    cbn [proj1_sig].
    unfold st_stc_pure_equivR.
    cbn [wf_st_to_stc_pure].
    easy.

  - (* receive *)
    cbn [proj1_sig].
    unfold st_stc_pure_equivR.
    cbn [wf_st_to_stc_pure].

    set (X :=
      exist (fun T => wf_branchingC T)
        (p & xs) Hwf).

    remember (observe_wf_st X) as L eqn:Hobs.

    unfold X in Hobs.
    unfold observe_wf_st in Hobs.
    cbn in Hobs.

    destruct L as [| q ys | q ys].

    destruct
      (constructive_indefinite_description
         (fun zs : list (string * sort * st) =>
            coseq_list_equiv xs zs)
         (wf_branching_has_finite_layer (p & xs) Hwf))
      as [zs Hequiv] eqn:Hchoice in Hobs.

    cbn in Hobs.
    discriminate Hobs.

    destruct
      (constructive_indefinite_description
         (fun zs : list (string * sort * st) =>
            coseq_list_equiv xs zs)
         (wf_branching_has_finite_layer (p & xs) Hwf))
      as [zs Hequiv] eqn:Hchoice in Hobs.

    cbn in Hobs.
    discriminate Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p & xs) Hwf))
  as [zs Hequiv] eqn:Hchoice
  in Hobs.
    injection Hobs as Hq Hys.
    subst q.
    subst ys.

    cbn [proj1_sig].

    split.
    + reflexivity.
exists zs.
split.
- exact Hequiv.
set (Hmembers :=
  fun lbl sr T Hin =>
    wf_branchingC_list_members_receive
      p xs zs Hwf Hequiv lbl sr T Hin).

set (bs := lift_wf_branches zs Hmembers).
assert (Hlen :
  List.length zs = List.length (branch_keys bs)).
{
  rewrite branch_keys_length.
  unfold bs.
  symmetry.
  apply lift_wf_branches_length.
}
exists Hlen.
intro i.
destruct
  (fin_nth zs
    (eq_rect
      (List.length (branch_keys bs))
      Fin.t i
      (List.length zs)
      (eq_sym Hlen)))
  as [[lbl sr] T] eqn:Hsource.

destruct
  (fin_nth (branch_keys bs) i)
  as [lbl' sr'] eqn:Hkey.

cbn [shape_of_branches branch_labels].
rewrite Hsource.
rewrite Hkey.
cbn.

pose (H1 := branch_keys_length bs).
pose (H2 := lift_wf_branches_length zs Hmembers).

pose (k :=
  eq_rect
    (List.length (branch_keys bs))
    Fin.t i
    (List.length bs)
    H1).

pose (j0 :=
  eq_rect
    (List.length bs)
    Fin.t k
    (List.length zs)
    H2).

assert (Heq :
  eq_sym Hlen = eq_trans H1 H2).
{
  apply UIP_dec.
  decide equality.
}

assert (Hj :
  eq_rect
    (List.length (branch_keys bs))
    Fin.t i
    (List.length zs)
    (eq_sym Hlen)
  = j0).
{
  rewrite Heq.
  unfold j0, k.
  symmetry.
  apply fin_transport_compose.
}

pose proof
  (lift_wf_branches_erase zs Hmembers)
  as Herase.

change (List.map erase_wf_branch bs = zs) in Herase.


assert (Hlookup :
  fin_nth zs j0 =
  erase_wf_branch (fin_nth bs k)).
{
  pose proof
    (fin_nth_map_erase bs k)
    as Hmap.

assert (Htransport :
  eq_rect
    (List.length (List.map erase_wf_branch bs))
    Fin.t
    (eq_rect
       (List.length bs)
       Fin.t k
       (List.length (List.map erase_wf_branch bs))
       (map_length_eq erase_wf_branch bs))
    (List.length zs)
    (f_equal
       (@List.length (string * sort * st))
       Herase)
  =
  j0).
{
  unfold j0.

  rewrite fin_transport_compose.

  assert (Hp :
    eq_trans
      (map_length_eq erase_wf_branch bs)
      (f_equal
         (@List.length (string * sort * st))
         Herase)
    = H2).
  {
    apply UIP_dec.
    exact Nat.eq_dec.
  }

  rewrite Hp.
  reflexivity.
}

pose proof
  (@fin_nth_transport_eq
     (string * sort * st)
     (List.map erase_wf_branch bs)
     zs
     Herase
     (eq_rect
        (List.length bs)
        Fin.t k
        (List.length (List.map erase_wf_branch bs))
        (map_length_eq erase_wf_branch bs)))
  as Htransport_lookup.

rewrite Htransport in Htransport_lookup.

etransitivity.
- exact Htransport_lookup.
- exact Hmap.
}

rewrite Hj in Hsource.
rewrite Hlookup in Hsource.

remember (fin_nth bs k) as b eqn:Hb.
destruct b as [[l s] Y].

cbn [erase_wf_branch] in Hsource.
injection Hsource as Hl Hs HT.

pose proof (fin_nth_branch_keys bs i) as Hkeys.

change (
  fin_nth (branch_keys bs) i =
  let '(a, b, _) := fin_nth bs k in
  (a, b)
) in Hkeys.

rewrite <- Hb in Hkeys.
cbn in Hkeys.

assert (Hnext : pure_branch_next bs i = Y).
{
  unfold pure_branch_next.
  fold k.
replace
  (eq_rect
     (List.length (branch_keys bs))
     Fin.t i
     (List.length bs)
     (branch_keys_length bs))
  with k
  by reflexivity.

destruct (fin_nth bs k) as [[a b] Z] eqn:E.


inversion Hb.
reflexivity.
}

repeat split.

- congruence.

- congruence.

- rewrite Hnext.
  rewrite <- HT.
  right.
  apply CIH.

cbn [proj1_sig].

unfold wf_st_to_stc_pure at 1.
cbn.

set (X :=
  exist (fun T => wf_branchingC T)
    (p ! xs) Hwf).

remember (observe_wf_st X) as L eqn:Hobs.

destruct L as [| q ys | q ys].

- unfold X in Hobs.
  unfold observe_wf_st in Hobs.
  cbn in Hobs.

  destruct
    (constructive_indefinite_description
       (fun zs : list (string * sort * st) =>
          coseq_list_equiv xs zs)
       (wf_branching_has_finite_layer (p ! xs) Hwf))
    as [zs Hequiv] eqn:Hchoice in Hobs.

  cbn in Hobs.
  discriminate Hobs.
  
- unfold X in Hobs.
  unfold observe_wf_st in Hobs.
  cbn in Hobs.

  destruct
    (constructive_indefinite_description
       (fun zs : list (string * sort * st) =>
          coseq_list_equiv xs zs)
       (wf_branching_has_finite_layer (p ! xs) Hwf))
    as [zs Hequiv] eqn:Hchoice in Hobs.

  cbn in Hobs.

  injection Hobs as Hq Hys.
  subst q.
  subst ys.

  rewrite Hchoice.
  cbn.

  split.
  + reflexivity.
  + unfold stc_pure_branches_equiv.

    exists zs.
    split.
    * exact Hequiv.

    * set (Hmembers :=
        fun lbl sr T Hin =>
          wf_branchingC_list_members_send
            p xs zs Hwf Hequiv lbl sr T Hin).

      set (bs := lift_wf_branches zs Hmembers).

      assert (Hlen :
        List.length zs = List.length (branch_keys bs)).
      {
        rewrite branch_keys_length.
        unfold bs.
        symmetry.
        apply lift_wf_branches_length.
      }

      exists Hlen.
      intro i.

cbn [shape_of_branches branch_labels].

destruct
  (fin_nth zs
    (eq_rect
      (List.length (branch_keys bs))
      Fin.t i
      (List.length zs)
      (eq_sym Hlen)))
  as [[lbl sr] T] eqn:Hsource.

destruct (fin_nth (branch_keys bs) i)
  as [lbl' sr'] eqn:Hkey.

cbn.

pose (H1 := branch_keys_length bs).
pose (H2 := lift_wf_branches_length zs Hmembers).

pose (k :=
  eq_rect
    (List.length (branch_keys bs))
    Fin.t i
    (List.length bs)
    H1).

pose (j0 :=
  eq_rect
    (List.length bs)
    Fin.t k
    (List.length zs)
    H2).

change (
  lbl = lbl' /\
  sr = sr' /\
  upaco2 st_stc_pure_equivR r T
    (wf_st_to_stc_pure (pure_branch_next bs i))
).

assert (Heq : eq_sym Hlen = eq_trans H1 H2).
{
  apply UIP_dec.
  exact Nat.eq_dec.
}

assert (Hj :
  eq_rect
    (List.length (branch_keys bs))
    Fin.t i
    (List.length zs)
    (eq_sym Hlen)
  = j0).
{
  rewrite Heq.
  unfold j0, k.
  symmetry.
  apply fin_transport_compose.
}

pose proof
  (lift_wf_branches_erase zs Hmembers)
  as Herase.

change (List.map erase_wf_branch bs = zs) in Herase.

assert (Hlookup :
  fin_nth zs j0 =
  erase_wf_branch (fin_nth bs k)).
{
  pose proof
    (fin_nth_map_erase bs k)
    as Hmap.

  assert (Htransport :
    eq_rect
      (List.length (List.map erase_wf_branch bs))
      Fin.t
      (eq_rect
         (List.length bs)
         Fin.t k
         (List.length (List.map erase_wf_branch bs))
         (map_length_eq erase_wf_branch bs))
      (List.length zs)
      (f_equal
         (@List.length (string * sort * st))
         Herase)
    =
    j0).
  {
    unfold j0.

    rewrite fin_transport_compose.

    assert (Hp :
      eq_trans
        (map_length_eq erase_wf_branch bs)
        (f_equal
           (@List.length (string * sort * st))
           Herase)
      = H2).
    {
      apply UIP_dec.
      exact Nat.eq_dec.
    }

    rewrite Hp.
    reflexivity.
  }

  pose proof
    (@fin_nth_transport_eq
       (string * sort * st)
       (List.map erase_wf_branch bs)
       zs
       Herase
       (eq_rect
          (List.length bs)
          Fin.t k
          (List.length (List.map erase_wf_branch bs))
          (map_length_eq erase_wf_branch bs)))
    as Htransport_lookup.

  rewrite Htransport in Htransport_lookup.

  etransitivity.
  - exact Htransport_lookup.
  - exact Hmap.
}

rewrite Hj in Hsource.
rewrite Hlookup in Hsource.

remember (fin_nth bs k) as b eqn:Hb.
destruct b as [[l s] Y].

cbn [erase_wf_branch] in Hsource.
injection Hsource as Hl Hs HT.

pose proof (fin_nth_branch_keys bs i) as Hkeys.

change (
  fin_nth (branch_keys bs) i =
  let '(a, b, _) := fin_nth bs k in
  (a, b)
) in Hkeys.

rewrite <- Hb in Hkeys.
cbn in Hkeys.

assert (Hnext : pure_branch_next bs i = Y).
{
  unfold pure_branch_next.
  unfold k in Hb.

  destruct
    (fin_nth bs
      (eq_rect
        (List.length (branch_keys bs))
        Fin.t i
        (List.length bs)
        (branch_keys_length bs)))
    as [[a b] Z] eqn:E.
unfold H1 in Hb.
rewrite E in Hb.
congruence.
}

repeat split.
- congruence.
- congruence.
- rewrite Hnext.
  rewrite <- HT.
  right.
  apply CIH.

unfold X in Hobs.
unfold observe_wf_st in Hobs.
cbn in Hobs.

destruct
  (constructive_indefinite_description
     (fun zs : list (string * sort * st) =>
        coseq_list_equiv xs zs)
     (wf_branching_has_finite_layer (p ! xs) Hwf))
  as [zs Hequiv] eqn:Hchoice in Hobs.

cbn in Hobs.
discriminate Hobs.
Qed.

Theorem wf_branching_st_to_stc_pure :
  forall T : st,
    wf_branchingC T ->
    exists U : stc_pure,
      st_stc_pure_equiv T U.
Proof.
  intros T Hwf.

  exists
    (wf_st_to_stc_pure
       (exist wf_branchingC T Hwf)).

  exact
    (wf_st_to_stc_pure_correct
       (exist wf_branchingC T Hwf)).
Qed.

Definition stc_pure_branches_bisim
  (R : stc_pure -> stc_pure -> Prop)
  (sh1 sh2 : branch_shape)
  (next1 : branch_pos sh1 -> stc_pure)
  (next2 : branch_pos sh2 -> stc_pure)
  : Prop :=

  exists Hlen :
    List.length (branch_labels sh1) =
    List.length (branch_labels sh2),

    forall i : branch_pos sh1,

      let j :=
        eq_rect
          (List.length (branch_labels sh1))
          Fin.t i
          (List.length (branch_labels sh2))
          Hlen
      in

      let '(lbl1, sr1) :=
        fin_nth (branch_labels sh1) i
      in

      let '(lbl2, sr2) :=
        fin_nth (branch_labels sh2) j
      in

      lbl1 = lbl2 /\
      sr1 = sr2 /\
      R (next1 i) (next2 j).

Definition stc_pure_equivR
  (R : stc_pure -> stc_pure -> Prop)
  (T U : stc_pure) : Prop :=
  match T, U with

  | stc_pure_end, stc_pure_end =>
      True

  | stc_pure_send p sh1 next1,
    stc_pure_send q sh2 next2 =>
      p = q /\
      stc_pure_branches_bisim
        R sh1 sh2 next1 next2

  | stc_pure_receive p sh1 next1,
    stc_pure_receive q sh2 next2 =>
      p = q /\
      stc_pure_branches_bisim
        R sh1 sh2 next1 next2

  | _, _ =>
      False
  end.

Definition stc_pure_equiv : stc_pure -> stc_pure -> Prop :=
  paco2 stc_pure_equivR bot2.

Lemma stc_pure_equivR_mon :
  monotone2 stc_pure_equivR.
Proof.
  unfold monotone2.
  intros T U R R' Hrel H.

  destruct T as [| p sh1 next1 | p sh1 next1];
  destruct U as [| q sh2 next2 | q sh2 next2];
  simpl in *;
  try contradiction;
  auto.
all: destruct Hrel as [Hp Hbranches].
all: split; [exact Hp |].

all: unfold stc_pure_branches_bisim in *.

all: destruct Hbranches as [Hlen Hnext].

all: exists Hlen.
all: intro i.

all: specialize (Hnext i).

all: destruct
  (fin_nth (branch_labels sh1) i)
  as [lbl1 sr1].

all: destruct
  (fin_nth
    (branch_labels sh2)
    (eq_rect
      (List.length (branch_labels sh1))
      Fin.t i
      (List.length (branch_labels sh2))
      Hlen))
  as [lbl2 sr2].

all: cbn in *.

all: destruct Hnext as [Hlbl [Hsort Hrec]].

all: repeat split; try assumption.

all: apply H.
all: exact Hrec.
Qed.

Lemma stc_pure_equiv_refl :
  forall U : stc_pure,
    stc_pure_equiv U U.
Proof.
  pcofix CIH.
  intro U.
  pfold.

  destruct U as
    [| p sh next
     | p sh next].

  - (* end *)
    simpl.
    easy.

  - (* send *)
    simpl.
    split.
    + reflexivity.
    + unfold stc_pure_branches_bisim.
      exists eq_refl.
      intro i.

      simpl.

      destruct (fin_nth (branch_labels sh) i)
        as [lbl sr].

      simpl.
      repeat split; try reflexivity.

      right.
      apply CIH.

  - (* receive *)
    simpl.
    split.
    + reflexivity.
    + unfold stc_pure_branches_bisim.
      exists eq_refl.
      intro i.

      simpl.

      destruct (fin_nth (branch_labels sh) i)
        as [lbl sr].

      simpl.
      repeat split; try reflexivity.

      right.
      apply CIH.
Qed.

Lemma wf_st_to_stc_pure_respects_equiv_eq :
  forall X Y : wf_st,
    st_equivC (proj1_sig X) (proj1_sig Y) ->
    wf_st_to_stc_pure X = wf_st_to_stc_pure Y.
Proof.
  intros [T HT] [U HU] Hequiv.

  simpl in Hequiv.

  apply stExt in Hequiv.
  subst U.

  assert (Heq : HT = HU).
  {
    apply proof_irrelevance.
  }

  subst HU.

  reflexivity.
Qed.


