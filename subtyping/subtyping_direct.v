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

Definition stc_pure_to_soR
  (R : stc_pure -> stc_pure -> Prop)
  (T U : stc_pure) : Prop :=
  match T, U with

  | stc_pure_end, stc_pure_end =>
      True

  | stc_pure_send p sh next,
    stc_pure_send q sh' next' =>
      p = q /\
      exists i : branch_pos sh,
        exists j : branch_pos sh',
          fin_nth (branch_labels sh) i =
          fin_nth (branch_labels sh') j /\
          List.length (branch_labels sh') = 1 /\
          R (next i) (next' j)

  | stc_pure_receive p sh next,
    stc_pure_receive q sh' next' =>
      p = q /\
      stc_pure_branches_bisim
        R sh sh' next next'

  | _, _ =>
      False
  end.

Definition stc_pure_to_so
  (T U : stc_pure) : Prop :=
  paco2 stc_pure_to_soR bot2 T U.

CoInductive productive_so : stc_pure -> Prop :=
| productive_so_end :
    productive_so stc_pure_end

| productive_so_send :
    forall p sh next,
      (exists i : branch_pos sh, True) ->
      (forall i, productive_so (next i)) ->
      productive_so (stc_pure_send p sh next)

| productive_so_receive :
    forall p sh next,
      (forall i, productive_so (next i)) ->
      productive_so (stc_pure_receive p sh next).

Definition choose_branch
  (sh : branch_shape)
  : option (branch_pos sh).
Proof.
  destruct sh as [labels].
  destruct labels as [| b bs].

  - exact None.

  - exact (Some (@Fin.F1 (List.length bs))).
Defined.

CoFixpoint make_so
  (T : stc_pure) : stc_pure :=
  match T with

  | stc_pure_end =>
      stc_pure_end

  | stc_pure_send p sh next =>
      match choose_branch sh with
      | Some i =>
          let '(lbl, sr) :=
            fin_nth (branch_labels sh) i
          in
          stc_pure_send p
            {| branch_labels := [(lbl, sr)] |}
            (fun _ => make_so (next i))

      | None =>
          stc_pure_end
      end

  | stc_pure_receive p sh next =>
      stc_pure_receive p sh
        (fun i => make_so (next i))
  end.

Definition stc_pure_to_siR
  (R : stc_pure -> stc_pure -> Prop)
  (T U : stc_pure) : Prop :=
  match T, U with

  | stc_pure_end, stc_pure_end =>
      True

  | stc_pure_send p sh next,
    stc_pure_send q sh' next' =>
      p = q /\
      stc_pure_branches_bisim
        R sh sh' next next'

  | stc_pure_receive p sh next,
    stc_pure_receive q sh' next' =>
      p = q /\
      exists i : branch_pos sh,
        exists j : branch_pos sh',
          fin_nth (branch_labels sh) i =
          fin_nth (branch_labels sh') j /\
          List.length (branch_labels sh') = 1 /\
          R (next i) (next' j)

  | _, _ =>
      False
  end.

Definition stc_pure_to_si
  (T U : stc_pure) : Prop :=
  paco2 stc_pure_to_siR bot2 T U.

Lemma stc_pure_to_siR_mon :
  monotone2 stc_pure_to_siR.
Proof.
  unfold monotone2.
  intros T U R R' Hrel H.

  destruct T as [| p sh1 next1 | p sh1 next1];
  destruct U as [| q sh2 next2 | q sh2 next2];
  simpl in *;
  try contradiction;
  auto.

  - (* Send: preserve all branches *)
    destruct Hrel as [Hp Hbranches].
    split.
    + exact Hp.
    + unfold stc_pure_branches_bisim in *.
      destruct Hbranches as [Hlen Hnext].
      exists Hlen.
      intro i.
      specialize (Hnext i).

      destruct (fin_nth (branch_labels sh1) i)
        as [lbl1 sr1].

      destruct
        (fin_nth (branch_labels sh2)
          (eq_rect
            (List.length (branch_labels sh1))
            Fin.t i
            (List.length (branch_labels sh2))
            Hlen))
        as [lbl2 sr2].

      cbn in *.
      destruct Hnext as [Hl [Hs Hr]].
      repeat split; try assumption.
      apply H.
      exact Hr.

  - (* Receive: select one branch *)
    destruct Hrel as [Hp [i [j [Hkey [Hlen Hr]]]]].
    split.
    + exact Hp.
    + exists i, j.
      repeat split; try assumption.
      apply H.
      exact Hr.
Qed.

Definition stc_pure_to_siso
  (T W : stc_pure) : Prop :=
  exists U : stc_pure,
    stc_pure_to_so T U /\
    stc_pure_to_si U W.

CoInductive nonempty_pure : stc_pure -> Prop :=
| nonempty_pure_end :
    nonempty_pure stc_pure_end

| nonempty_pure_send :
    forall p sh next,
      (exists i : branch_pos sh, True) ->
      (forall i, nonempty_pure (next i)) ->
      nonempty_pure (stc_pure_send p sh next)

| nonempty_pure_receive :
    forall p sh next,
      (exists i : branch_pos sh, True) ->
      (forall i, nonempty_pure (next i)) ->
      nonempty_pure (stc_pure_receive p sh next).

Definition nonempty_pure_send_next
  (p : string)
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure)
  (H : nonempty_pure (stc_pure_send p sh next))
  : forall i : branch_pos sh,
      nonempty_pure (next i) :=
  match H in nonempty_pure T
        return
          match T with
          | stc_pure_send _ sh' next' =>
              forall i : branch_pos sh',
                nonempty_pure (next' i)
          | _ => True
          end
  with
  | nonempty_pure_end =>
      Coq.Init.Logic.I
  | nonempty_pure_send _ _ _ _ Hnext =>
      Hnext
  | nonempty_pure_receive _ _ _ _ _ =>
      Coq.Init.Logic.I
  end.

(* Lemma nonempty_pure_send_next :
  forall (p : string)
         (sh : branch_shape)
         (next : branch_pos sh -> stc_pure),
    nonempty_pure (stc_pure_send p sh next) ->
    forall i : branch_pos sh,
      nonempty_pure (next i).
Proof.
  intros p sh next H.

  remember (stc_pure_send p sh next) as T eqn:HT.

  destruct H as
    [| p' sh' next' Hexists Hnext
     | p' sh' next' Hexists Hnext];
    try discriminate HT.

  inversion HT; subst.
  intro i.
  exact (Hnext i).
Qed. *)

Definition nonempty_pure_send_has_branch
  (p : string)
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure)
  (H : nonempty_pure (stc_pure_send p sh next))
  : exists i : branch_pos sh, True :=
  match H in nonempty_pure T
        return
          match T with
          | stc_pure_send _ sh' _ =>
              exists i : branch_pos sh', True
          | _ => True
          end
  with
  | nonempty_pure_end =>
      Coq.Init.Logic.I
  | nonempty_pure_send _ _ _ Hexists _ =>
      Hexists
  | nonempty_pure_receive _ _ _ _ _ =>
      Coq.Init.Logic.I
  end.

Definition nonempty_pure_receive_next
  (p : string)
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure)
  (H : nonempty_pure (stc_pure_receive p sh next))
  : forall i : branch_pos sh,
      nonempty_pure (next i) :=
  match H in nonempty_pure T
        return
          match T with
          | stc_pure_receive _ sh' next' =>
              forall i : branch_pos sh',
                nonempty_pure (next' i)
          | _ => True
          end
  with
  | nonempty_pure_end =>
      Coq.Init.Logic.I

  | nonempty_pure_send _ _ _ _ _ =>
      Coq.Init.Logic.I

  | nonempty_pure_receive _ _ _ _ Hnext =>
      Hnext
  end.

Lemma choose_branch_none :
  forall sh : branch_shape,
    choose_branch sh = None ->
    branch_pos sh -> False.
Proof.
  intros [labels] Hnone i.
  destruct labels as [| b bs].
  - inversion i.
  - simpl in Hnone.
    discriminate.
Qed.

Lemma make_so_correct :
  forall (T : stc_pure),
    nonempty_pure T ->
    stc_pure_to_so T (make_so T).
Proof.
  pcofix CIH.
  intros T H.
  pfold.
destruct T as
  [| p sh next
   | p sh next].
- cbn [make_so stc_pure_to_soR].
  easy.
-
destruct (choose_branch sh) as [i |] eqn:Hchoose.
destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hbranch.

cbn [stc_pure_to_soR].

unfold make_so at 1.
cbn beta iota zeta.
change (
  stc_pure_to_soR
    (upaco2 stc_pure_to_soR r)
    (stc_pure_send p sh next)
    (make_so (stc_pure_send p sh next))
).
cbn.
cbn beta iota zeta.
rewrite Hchoose.
rewrite Hbranch.
cbn beta iota zeta.

split.
- reflexivity.
- exists i.
  exists (@Fin.F1 0).
  repeat split.
  + exact Hbranch.
  + right.
    apply CIH.
exact (nonempty_pure_send_next p sh next H i).


exfalso.

assert (Hpos : exists i : branch_pos sh, True).
{
  exact (nonempty_pure_send_has_branch p sh next H).
}

destruct Hpos as [i _].

eapply choose_branch_none.
- exact Hchoose.
- exact i.

split.
- reflexivity.
- unfold stc_pure_branches_bisim.
  exists eq_refl.
  intro i.

destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hbranch.


  cbn.
rewrite Hbranch.
cbn.

repeat split; try reflexivity.

right.
apply CIH.

exact (nonempty_pure_receive_next p sh next H i).
Qed.

Theorem stc_pure_so_exists :
  forall T : stc_pure,
    nonempty_pure T ->
    exists U : stc_pure,
      stc_pure_to_so T U.
Proof.
  intros T H.
  exists (make_so T).
  apply make_so_correct.
  exact H.
Qed.

CoFixpoint make_si (T : stc_pure) : stc_pure :=
  match T with

  | stc_pure_end =>
      stc_pure_end

  | stc_pure_send p sh next =>
      stc_pure_send p sh
        (fun i => make_si (next i))

  | stc_pure_receive p sh next =>
      match choose_branch sh with

      | Some i =>
          let '(lbl, sr) :=
            fin_nth (branch_labels sh) i
          in
          stc_pure_receive p
            {| branch_labels := [(lbl, sr)] |}
            (fun _ => make_si (next i))

      | None =>
          stc_pure_end
      end
  end.

Definition nonempty_pure_receive_has_branch
  (p : string)
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure)
  (H : nonempty_pure (stc_pure_receive p sh next))
  : exists i : branch_pos sh, True :=
  match H in nonempty_pure T
        return
          match T with
          | stc_pure_receive _ sh' _ =>
              exists i : branch_pos sh', True
          | _ => True
          end
  with
  | nonempty_pure_end =>
      Coq.Init.Logic.I

  | nonempty_pure_send _ _ _ _ _ =>
      Coq.Init.Logic.I

  | nonempty_pure_receive _ _ _ Hexists _ =>
      Hexists
  end.

Lemma make_si_correct :
  forall T : stc_pure,
    nonempty_pure T ->
    stc_pure_to_si T (make_si T).
Proof.
  pcofix CIH.
  intros T H.
  pfold.

  destruct T as [| p sh next | p sh next].

  - (* End *)
    cbn [make_si stc_pure_to_siR].
    exact Coq.Init.Logic.I.

  - (* Send: preserve all branches *)
    cbn [make_si stc_pure_to_siR].

    split.
    + reflexivity.

    + unfold stc_pure_branches_bisim.
      exists eq_refl.
      intro i.

      destruct (fin_nth (branch_labels sh) i)
        as [lbl sr] eqn:Hbranch.
cbn.
      rewrite Hbranch.
      cbn.

      repeat split; try reflexivity.

      right.
      apply CIH.

      exact (nonempty_pure_send_next p sh next H i).

  - (* Receive: select one branch *)
    destruct (choose_branch sh)
      as [i |] eqn:Hchoose.

    + (* Some i *)
      destruct (fin_nth (branch_labels sh) i)
        as [lbl sr] eqn:Hbranch.

      cbn [make_si stc_pure_to_siR].

      rewrite Hchoose.
      rewrite Hbranch.
      cbn beta iota zeta.

      split.
      * reflexivity.

      * exists i.
        exists (@Fin.F1 0).

        repeat split.

        -- exact Hbranch.

        -- right.
           apply CIH.
           exact
             (nonempty_pure_receive_next
                p sh next H i).

    + (* None: impossible *)
      exfalso.

      destruct
        (nonempty_pure_receive_has_branch
           p sh next H)
        as [i _].

      eapply choose_branch_none.
      * exact Hchoose.
      * exact i.
Qed.

Theorem stc_pure_si_exists :
  forall T : stc_pure,
    nonempty_pure T ->
    exists V : stc_pure,
      stc_pure_to_si T V.
Proof.
  intros T H.
  exists (make_si T).
  apply make_si_correct.
  exact H.
Qed.

Lemma stc_pure_to_soR_mon :
  monotone2 stc_pure_to_soR.
Proof.
  unfold monotone2.
  intros T U R R' Hrel H.

  destruct T as [| p sh1 next1 | p sh1 next1];
  destruct U as [| q sh2 next2 | q sh2 next2];
  simpl in *;
  try contradiction;
  auto.

  - (* Send: select one output branch *)
    destruct Hrel as
      [Hp [i [j [Hkey [Hlen Hrec]]]]].

    split.
    + exact Hp.
    + exists i, j.
      repeat split; try assumption.
      apply H.
      exact Hrec.

  - (* Receive: preserve all input branches *)
    destruct Hrel as [Hp Hbranches].

    split.
    + exact Hp.
    + unfold stc_pure_branches_bisim in *.

      destruct Hbranches as [Hlen Hnext].

      exists Hlen.
      intro i.

      specialize (Hnext i).

      destruct (fin_nth (branch_labels sh1) i)
        as [lbl1 sr1].

      destruct
        (fin_nth
          (branch_labels sh2)
          (eq_rect
            (List.length (branch_labels sh1))
            Fin.t i
            (List.length (branch_labels sh2))
            Hlen))
        as [lbl2 sr2].

      cbn in *.

      destruct Hnext as [Hl [Hs Hrec]].

      repeat split; try assumption.

      apply H.
      exact Hrec.
Qed.

Lemma so_si_send_match :
  forall p sh next shu nextu shv nextv,

    stc_pure_to_so
      (stc_pure_send p sh next)
      (stc_pure_send p shu nextu) ->

    stc_pure_to_si
      (stc_pure_send p sh next)
      (stc_pure_send p shv nextv) ->

    exists (i : branch_pos sh)
           (j : branch_pos shu)
           (k : branch_pos shv),

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shu) j /\

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shv) k.
Proof.
  intros p sh next shu nextu shv nextv Hso Hsi.

  punfold Hso.
  punfold Hsi.

  cbn [stc_pure_to_soR] in Hso.
  cbn [stc_pure_to_siR] in Hsi.

  destruct Hso as
    [_ [i [j [Hkey [_ Hrec]]]]].

  destruct Hsi as [_ Hbranches].

  unfold stc_pure_branches_bisim in Hbranches.

  destruct Hbranches as [Hlen Hnext].

  exists i, j.

  exists
    (eq_rect
       (List.length (branch_labels sh))
       Fin.t i
       (List.length (branch_labels shv))
       Hlen).

  split.
  - exact Hkey.

  - specialize (Hnext i).

    destruct (fin_nth (branch_labels sh) i)
      as [lbl sr] eqn:Hi.

    destruct
      (fin_nth
        (branch_labels shv)
        (eq_rect
           (List.length (branch_labels sh))
           Fin.t i
           (List.length (branch_labels shv))
           Hlen))
      as [lbl' sr'] eqn:Hk.

    cbn in Hnext.

    destruct Hnext as [Hl [Hs Hr]].
    subst. easy.
    apply stc_pure_to_siR_mon.
    apply stc_pure_to_soR_mon.
Qed.

Lemma so_si_send_match_strong :
  forall p sh next shu nextu shv nextv,

    stc_pure_to_so
      (stc_pure_send p sh next)
      (stc_pure_send p shu nextu) ->

    stc_pure_to_si
      (stc_pure_send p sh next)
      (stc_pure_send p shv nextv) ->

    exists (i : branch_pos sh)
           (j : branch_pos shu)
           (k : branch_pos shv),

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shu) j /\

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shv) k /\

      stc_pure_to_so (next i) (nextu j) /\

      stc_pure_to_si (next i) (nextv k).
Proof.
  intros p sh next shu nextu shv nextv Hso Hsi.

  punfold Hso.
  punfold Hsi.

  cbn [stc_pure_to_soR] in Hso.
  cbn [stc_pure_to_siR] in Hsi.

  destruct Hso as
    [_ [i [j [Hkey [Hsingleton HrecSO]]]]].

  destruct Hsi as [_ Hbranches].

  unfold stc_pure_branches_bisim in Hbranches.

  destruct Hbranches as [Hlen Hnext].

  set (k :=
    eq_rect
      (List.length (branch_labels sh))
      Fin.t i
      (List.length (branch_labels shv))
      Hlen).

  specialize (Hnext i).

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hi.

  destruct (fin_nth (branch_labels shv) k)
    as [lbl' sr'] eqn:Hk.

  cbn in Hnext.

change (
  let '(a, b) := fin_nth (branch_labels shv) k in
  lbl = a /\
  sr = b /\
  upaco2 stc_pure_to_siR bot2
    (next i) (nextv k)
) in Hnext.

rewrite Hk in Hnext.
cbn in Hnext.

destruct Hnext as [Hl [Hs HrecSI]].

  exists i, j, k.

  split.

  - rewrite Hi. subst.
    exact Hkey.

split.
- rewrite Hi.
  rewrite Hk.
  now rewrite Hl, Hs.

- split.
  + (* Recursive SO *)
    unfold stc_pure_to_so.
    destruct HrecSO as [Hso | Hbot].
    * exact Hso.
    * contradiction.

  + (* Recursive SI *)
    unfold stc_pure_to_si.
    destruct HrecSI as [Hsi | Hbot].
    * exact Hsi.
    * contradiction.
    apply stc_pure_to_siR_mon.
    apply stc_pure_to_soR_mon.
Qed.

Lemma so_si_receive_match :
  forall p sh next shu nextu shv nextv,

    stc_pure_to_so
      (stc_pure_receive p sh next)
      (stc_pure_receive p shu nextu) ->

    stc_pure_to_si
      (stc_pure_receive p sh next)
      (stc_pure_receive p shv nextv) ->

    exists (i : branch_pos sh)
           (j : branch_pos shu)
           (k : branch_pos shv),

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shu) j /\

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shv) k.
Proof.
  intros p sh next shu nextu shv nextv Hso Hsi.

  punfold Hso.
  punfold Hsi.

  cbn [stc_pure_to_soR] in Hso.
  cbn [stc_pure_to_siR] in Hsi.

  (* SO preserves all receive branches. *)
  destruct Hso as [_ Hbranches].

  (* SI selects one receive branch. *)
  destruct Hsi as
    [_ [i [k [Hkey [_ Hrec]]]]].

  unfold stc_pure_branches_bisim in Hbranches.

  destruct Hbranches as [Hlen Hnext].

  set (j :=
    eq_rect
      (List.length (branch_labels sh))
      Fin.t i
      (List.length (branch_labels shu))
      Hlen).

  specialize (Hnext i).

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hi.

  destruct (fin_nth (branch_labels shu) j)
    as [lbl' sr'] eqn:Hj.

  change (
    let '(a, b) := fin_nth (branch_labels shu) j in
    lbl = a /\
    sr = b /\
    upaco2 stc_pure_to_soR bot2
      (next i) (nextu j)
  ) in Hnext.

  rewrite Hj in Hnext.
  cbn in Hnext.

  destruct Hnext as [Hl [Hs HrecSO]].

  exists i, j, k.

  split.
  - rewrite Hi.
    rewrite Hj.
    now rewrite Hl, Hs.

rewrite Hi.
exact Hkey.

  apply stc_pure_to_siR_mon.
  apply stc_pure_to_soR_mon.
Qed.

Lemma so_si_receive_match_strong :
  forall p sh next shu nextu shv nextv,

    stc_pure_to_so
      (stc_pure_receive p sh next)
      (stc_pure_receive p shu nextu) ->

    stc_pure_to_si
      (stc_pure_receive p sh next)
      (stc_pure_receive p shv nextv) ->

    exists (i : branch_pos sh)
           (j : branch_pos shu)
           (k : branch_pos shv),

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shu) j /\

      fin_nth (branch_labels sh) i =
      fin_nth (branch_labels shv) k /\

      stc_pure_to_so (next i) (nextu j) /\

      stc_pure_to_si (next i) (nextv k).
Proof.
  intros p sh next shu nextu shv nextv Hso Hsi.

  punfold Hso.
  punfold Hsi.

  cbn [stc_pure_to_soR] in Hso.
  cbn [stc_pure_to_siR] in Hsi.

  (* SO preserves all receive branches. *)
  destruct Hso as [_ Hbranches].

  (* SI selects exactly one receive branch. *)
  destruct Hsi as
    [_ [i [k [Hkey [Hsingleton HrecSI]]]]].

  unfold stc_pure_branches_bisim in Hbranches.

  destruct Hbranches as [Hlen Hnext].

  set (j :=
    eq_rect
      (List.length (branch_labels sh))
      Fin.t i
      (List.length (branch_labels shu))
      Hlen).

  specialize (Hnext i).

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hi.

  destruct (fin_nth (branch_labels shu) j)
    as [lbl' sr'] eqn:Hj.

  change (
    let '(a, b) := fin_nth (branch_labels shu) j in
    lbl = a /\
    sr = b /\
    upaco2 stc_pure_to_soR bot2
      (next i) (nextu j)
  ) in Hnext.

  rewrite Hj in Hnext.
  cbn in Hnext.

  destruct Hnext as [Hl [Hs HrecSO]].

  exists i, j, k.

  split.
  - (* Source branch matches SO branch *)
    rewrite Hi.
    rewrite Hj.
    now rewrite Hl, Hs.

  - split.
    + (* Source branch matches SI branch *)
rewrite Hi.
exact Hkey.

    + split.
      * (* Recursive SO decomposition *)
        unfold stc_pure_to_so.
        destruct HrecSO as [Hso' | Hbot].
        -- exact Hso'.
        -- contradiction.

      * (* Recursive SI decomposition *)
        unfold stc_pure_to_si.
        destruct HrecSI as [Hsi' | Hbot].
        -- exact Hsi'.
        -- contradiction.

  apply stc_pure_to_siR_mon.
  apply stc_pure_to_soR_mon.
Qed.

Record intersection_state : Type := {
  int_T : stc_pure;
  int_U : stc_pure;
  int_V : stc_pure;

  int_so :
    stc_pure_to_so int_T int_U;

  int_si :
    stc_pure_to_si int_T int_V
}.

Definition make_intersection_state
  (T U V : stc_pure)
  (Hso : stc_pure_to_so T U)
  (Hsi : stc_pure_to_si T V)
  : intersection_state :=
  {|
    int_T := T;
    int_U := U;
    int_V := V;
    int_so := Hso;
    int_si := Hsi
  |}.

Inductive intersection_layer : Type :=
| int_end :
    intersection_layer

| int_send :
    forall (p : string)
           (lbl : string)
           (sr : sort),
      intersection_state ->
      intersection_layer

| int_receive :
    forall (p : string)
           (lbl : string)
           (sr : sort),
      intersection_state ->
      intersection_layer.

Definition valid_intersection_layer
  (S : intersection_state)
  (L : intersection_layer) : Prop :=

  match L with

  | int_end =>
      int_T S = stc_pure_end /\
      int_U S = stc_pure_end /\
      int_V S = stc_pure_end

  | int_send p lbl sr S' =>
      exists sh next shu nextu shv nextv,

        int_T S = stc_pure_send p sh next /\

        int_U S = stc_pure_send p shu nextu /\

        int_V S = stc_pure_send p shv nextv /\

        exists (i : branch_pos sh)
               (j : branch_pos shu)
               (k : branch_pos shv),

          fin_nth (branch_labels sh) i = (lbl, sr) /\

          fin_nth (branch_labels shu) j = (lbl, sr) /\

          fin_nth (branch_labels shv) k = (lbl, sr) /\

          List.length (branch_labels shu) = 1 /\

          int_T S' = next i /\
          int_U S' = nextu j /\
          int_V S' = nextv k

  | int_receive p lbl sr S' =>
      exists sh next shu nextu shv nextv,

        int_T S = stc_pure_receive p sh next /\

        int_U S = stc_pure_receive p shu nextu /\

        int_V S = stc_pure_receive p shv nextv /\

        exists (i : branch_pos sh)
               (j : branch_pos shu)
               (k : branch_pos shv),

          fin_nth (branch_labels sh) i = (lbl, sr) /\

          fin_nth (branch_labels shu) j = (lbl, sr) /\

          fin_nth (branch_labels shv) k = (lbl, sr) /\

          List.length (branch_labels shv) = 1 /\

          int_T S' = next i /\
          int_U S' = nextu j /\
          int_V S' = nextv k

  end.

Lemma intersection_layer_exists :
  forall S : intersection_state,
    exists L : intersection_layer,
      valid_intersection_layer S L.
Proof.
  intros [T U V Hso Hsi].
  simpl.

  destruct T as
    [| p sh next
     | p sh next].

- (* End case *)
  assert (HU : U = stc_pure_end).
  {
    pose proof Hso as Hso'.
    punfold Hso'.

    destruct U as
      [| p sh next
       | p sh next].

    - reflexivity.
    - cbn [stc_pure_to_soR] in Hso'.
      contradiction.
    - cbn [stc_pure_to_soR] in Hso'.
      contradiction.

    apply stc_pure_to_soR_mon.
  }

  assert (HV : V = stc_pure_end).
  {
    pose proof Hsi as Hsi'.
    punfold Hsi'.

    destruct V as
      [| p sh next
       | p sh next].

    - reflexivity.
    - cbn [stc_pure_to_siR] in Hsi'.
      contradiction.
    - cbn [stc_pure_to_siR] in Hsi'.
      contradiction.

    apply stc_pure_to_siR_mon.
  }

  subst U V.

  exists int_end.
  unfold valid_intersection_layer.
  simpl.
  repeat split; reflexivity.


assert (HU :
  exists q shu nextu,
    U = stc_pure_send q shu nextu).
{
  pose proof Hso as Hso'.
  punfold Hso'.
  destruct U as [| q shu nextu | q shu nextu];
    cbn [stc_pure_to_soR] in Hso';
    try contradiction.
  eexists _, _, _.
  reflexivity.
  apply stc_pure_to_soR_mon.
}

assert (HV :
  exists q shv nextv,
    V = stc_pure_send q shv nextv).
{
  pose proof Hsi as Hsi'.
  punfold Hsi'.
  destruct V as [| q shv nextv | q shv nextv];
    cbn [stc_pure_to_siR] in Hsi';
    try contradiction.
  eexists _, _, _.
  reflexivity.
  apply stc_pure_to_siR_mon.
}

destruct HU as [q [shu [nextu HU]]].
destruct HV as [q' [shv [nextv HV]]].

subst U V.
pose proof Hso as Hso'.
pose proof Hsi as Hsi'.

punfold Hso'.
punfold Hsi'.

cbn [stc_pure_to_soR] in Hso'.
cbn [stc_pure_to_siR] in Hsi'.

destruct Hso' as [Hp _].
destruct Hsi' as [Hp' _].

subst q q'.
destruct
  (so_si_send_match_strong
     p sh next shu nextu shv nextv Hso Hsi)
  as [i [j [k
       [HkeyU [HkeyV [Hso_next Hsi_next]]]]]].
destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hi.

assert (Hsingleton : List.length (branch_labels shu) = 1).
{
  pose proof Hso as Hso'.
  punfold Hso'.
  cbn [stc_pure_to_soR] in Hso'.

  destruct Hso' as [_ [i0 [j0 [_ [Hlen _]]]]].
  exact Hlen.

  apply stc_pure_to_soR_mon.
}

set (S' :=
  {|
    int_T := next i;
    int_U := nextu j;
    int_V := nextv k;
    int_so := Hso_next;
    int_si := Hsi_next
  |} : intersection_state).

exists (int_send p lbl sr S').

unfold valid_intersection_layer.
cbn.

exists sh, next, shu, nextu, shv, nextv.
repeat split; try reflexivity.

exists i, j, k.

repeat split.
- exact Hi.
- symmetry. exact HkeyU.
- symmetry. exact HkeyV.
- exact Hsingleton.
apply stc_pure_to_siR_mon.
apply stc_pure_to_soR_mon.

assert (HU :
  exists q shu nextu,
    U = stc_pure_receive q shu nextu).
{
  pose proof Hso as Hso'.
  punfold Hso'.

  destruct U as [| q shu nextu | q shu nextu];
    cbn [stc_pure_to_soR] in Hso';
    try contradiction.

  eexists _, _, _.
  reflexivity.

  apply stc_pure_to_soR_mon.
}

assert (HV :
  exists q shv nextv,
    V = stc_pure_receive q shv nextv).
{
  pose proof Hsi as Hsi'.
  punfold Hsi'.

  destruct V as [| q shv nextv | q shv nextv];
    cbn [stc_pure_to_siR] in Hsi';
    try contradiction.

  eexists _, _, _.
  reflexivity.

  apply stc_pure_to_siR_mon.
}

destruct HU as [q [shu [nextu HU]]].
destruct HV as [q' [shv [nextv HV]]].

subst U V.

pose proof Hso as Hso'.
pose proof Hsi as Hsi'.

punfold Hso'.
punfold Hsi'.

cbn [stc_pure_to_soR] in Hso'.
cbn [stc_pure_to_siR] in Hsi'.

destruct Hso' as [Hp _].
destruct Hsi' as [Hp' _].

subst q q'.

destruct
  (so_si_receive_match_strong
     p sh next shu nextu shv nextv Hso Hsi)
  as [i [j [k
       [HkeyU [HkeyV [Hso_next Hsi_next]]]]]].

assert (Hsingleton :
  List.length (branch_labels shv) = 1).
{
  pose proof Hsi as Hsi'.
  punfold Hsi'.
  cbn [stc_pure_to_siR] in Hsi'.

  destruct Hsi' as
    [_ [i0 [k0 [_ [Hlen _]]]]].

  exact Hlen.

  apply stc_pure_to_siR_mon.
}

destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hi.

set (S' :=
  {|
    int_T := next i;
    int_U := nextu j;
    int_V := nextv k;
    int_so := Hso_next;
    int_si := Hsi_next
  |} : intersection_state).

exists (int_receive p lbl sr S').

unfold valid_intersection_layer.
cbn.

exists sh, next, shu, nextu, shv, nextv.

repeat split; try reflexivity.

exists i, j, k.

repeat split.
- exact Hi.
- symmetry. exact HkeyU.
- symmetry. exact HkeyV.
- exact Hsingleton.
apply stc_pure_to_siR_mon.
apply stc_pure_to_soR_mon.
Qed.


Definition observe_intersection
  (S : intersection_state)
  : intersection_layer :=
  proj1_sig
    (constructive_indefinite_description
       (fun L : intersection_layer =>
          valid_intersection_layer S L)
       (intersection_layer_exists S)).

Lemma observe_intersection_correct :
  forall S : intersection_state,
    valid_intersection_layer
      S (observe_intersection S).
Proof.
  intro S.
  unfold observe_intersection.
  destruct
    (constructive_indefinite_description
       (fun L : intersection_layer =>
          valid_intersection_layer S L)
       (intersection_layer_exists S))
    as [L HL].
  simpl.
  exact HL.
Qed.

CoFixpoint make_intersection
  (S : intersection_state) : stc_pure :=
  match observe_intersection S with

  | int_end =>
      stc_pure_end

  | int_send p lbl sr S' =>
      stc_pure_send p
        {| branch_labels := [(lbl, sr)] |}
        (fun _ => make_intersection S')

  | int_receive p lbl sr S' =>
      stc_pure_receive p
        {| branch_labels := [(lbl, sr)] |}
        (fun _ => make_intersection S')

  end.

Lemma fin_unique_one :
  forall i j : Fin.t 1,
    i = j.
Proof.
  intros i j.
  dependent destruction i.
  dependent destruction j.
  reflexivity.
  inversion j.
  inversion i.
Qed.

Lemma fin_unique_length_one :
  forall (sh : branch_shape)
         (Hlen : List.length (branch_labels sh) = 1)
         (i j : branch_pos sh),
    i = j.
Proof.
  intros sh Hlen i j.
  unfold branch_pos in *.
  subst.
  revert i j.
  rewrite Hlen.
  intros.

  apply fin_unique_one.
Qed.

Lemma fin_nth_singleton_any :
  forall (A : Type) (x : A) (j : Fin.t 1),
    fin_nth [x] j = x.
Proof.
  intros A x j.
  assert (Hj : j = @Fin.F1 0).
  {
    apply fin_unique_one.
  }
  subst j.
  reflexivity.
Qed.

Lemma make_intersection_left_correct :
  forall S : intersection_state,
    stc_pure_to_si
      (int_U S)
      (make_intersection S).
Proof.
  pcofix CIH.
  intro S.
  pfold.

pose proof (observe_intersection_correct S) as Hvalid.
destruct (observe_intersection S)
  as [| p lbl sr S' | p lbl sr S']
  eqn:Hobs.
- (* End *)
  cbn [valid_intersection_layer] in Hvalid.

  destruct Hvalid as [_ [HU _]].

  rewrite HU.

  cbn [make_intersection stc_pure_to_siR].
  rewrite Hobs.
  simpl.

  exact Coq.Init.Logic.I.

- (* Send *)
  cbn [valid_intersection_layer] in Hvalid.

  destruct Hvalid as
    [sh [next
    [shu [nextu
    [shv [nextv
    [HT [HU [HV Hmatch]]]]]]]]].

  destruct Hmatch as
    [i [j [k
      [Hi [Hj [Hk
        [Hsingleton
          [HT' [HU' HV']]]]]]]]].
  rewrite HU.
  cbn [make_intersection stc_pure_to_siR].
  rewrite Hobs.
  cbn.
split.
- reflexivity.
- unfold stc_pure_branches_bisim.
  exists Hsingleton.
  intro i0.

assert (Heq : i0 = j).
{
  apply fin_unique_length_one.
  exact Hsingleton.
}
subst i0.
rewrite Hj.
cbn [branch_labels].

rewrite fin_nth_singleton_any.
cbn.

repeat split; try reflexivity.


rewrite <- HU'.
right.
apply CIH.


cbn [valid_intersection_layer] in Hvalid.

destruct Hvalid as
  [sh [next
  [shu [nextu
  [shv [nextv
  [HT [HU [HV Hmatch]]]]]]]]].

destruct Hmatch as
  [i [j [k
    [Hi [Hj [Hk
      [Hsingleton
        [HT' [HU' HV']]]]]]]]].

rewrite HU.

cbn [make_intersection stc_pure_to_siR].
rewrite Hobs.
cbn.

split.
- reflexivity.

- exists j.
  exists (@Fin.F1 0).

  repeat split.
  + rewrite Hj.
    reflexivity.

  + right.
    rewrite <- HU'.
    apply CIH.
Qed.

Lemma make_intersection_right_correct :
  forall S : intersection_state,
    stc_pure_to_so
      (int_V S)
      (make_intersection S).
Proof.
  pcofix CIH.
  intro S.
  pfold.

  pose proof
    (observe_intersection_correct S)
    as Hvalid.

  destruct (observe_intersection S)
    as [| p lbl sr S' | p lbl sr S']
    eqn:Hobs.

cbn [valid_intersection_layer] in Hvalid.
destruct Hvalid as [_ [_ HV]].

rewrite HV.

cbn [make_intersection stc_pure_to_soR].
rewrite Hobs.
cbn.

exact Coq.Init.Logic.I.

cbn [valid_intersection_layer] in Hvalid.

destruct Hvalid as
  [sh [next
  [shu [nextu
  [shv [nextv
  [HT [HU [HV Hmatch]]]]]]]]].

destruct Hmatch as
  [i [j [k
    [Hi [Hj [Hk
      [Hsingleton
        [HT' [HU' HV']]]]]]]]].

rewrite HV.

cbn [make_intersection stc_pure_to_soR].
rewrite Hobs.
cbn.

split.
- reflexivity.

- exists k.
  exists (@Fin.F1 0).

  repeat split.

  + rewrite Hk.
    reflexivity.

  + right.
    rewrite <- HV'.
    apply CIH.

cbn [valid_intersection_layer] in Hvalid.

destruct Hvalid as
  [sh [next
  [shu [nextu
  [shv [nextv
  [HT [HU [HV Hmatch]]]]]]]]].

destruct Hmatch as
  [i [j [k
    [Hi [Hj [Hk
      [Hsingleton
        [HT' [HU' HV']]]]]]]]].

rewrite HV.

cbn [make_intersection stc_pure_to_soR].
rewrite Hobs.
cbn.

split.
- reflexivity.

- unfold stc_pure_branches_bisim.

  exists Hsingleton.
  intro i0.

  assert (Heq : i0 = k).
  {
    apply fin_unique_length_one.
    exact Hsingleton.
  }

  subst i0.

cbn [branch_labels].
rewrite fin_nth_singleton_any.
cbn.

    rewrite Hk.
    cbn.

    repeat split; try reflexivity.

    right.
    rewrite <- HV'.
    apply CIH.
Qed.

Theorem stc_pure_decomposition_intersection :
  forall T U V : stc_pure,
    stc_pure_to_so T U ->
    stc_pure_to_si T V ->
    exists W : stc_pure,
      stc_pure_to_si U W /\
      stc_pure_to_so V W.
Proof.
  intros T U V Hso Hsi.

  set (S :=
    {|
      int_T := T;
      int_U := U;
      int_V := V;
      int_so := Hso;
      int_si := Hsi
    |} : intersection_state).

  exists (make_intersection S).

  split.
  - change (stc_pure_to_si (int_U S) (make_intersection S)).
    exact (make_intersection_left_correct S).

  - change (stc_pure_to_so (int_V S) (make_intersection S)).
    exact (make_intersection_right_correct S).
Qed.

(*uniformisation -- 3.15*)

Record uniformisation_state : Type := {
  uni_T : stc_pure;

  uni_Y : stc_pure -> Prop;

  uni_nonempty : nonempty_pure uni_T;

  uni_H :
    forall V,
      stc_pure_to_si uni_T V ->
      exists W,
        stc_pure_to_so V W /\
        uni_Y W
}.

Inductive uniformisation_layer : Type :=
| uni_end :
    uniformisation_layer

| uni_send :
    string -> string -> sort ->
    uniformisation_state ->
    uniformisation_layer

| uni_receive :
    forall (p : string) (sh : branch_shape),
      (branch_pos sh -> uniformisation_state) ->
      uniformisation_layer.

From Coq Require Import Logic.ClassicalEpsilon.

Lemma finite_uniform_choice :
  forall (n : nat)
         (A : Fin.t n -> Type)
         (P : forall i : Fin.t n, A i -> Prop),

    (forall i, inhabited (A i)) ->

    (forall f : forall i, A i,
       exists i, P i (f i)) ->

    exists i,
      forall x : A i, P i x.
Proof.
  intros n A P Hinh Hall.

  apply NNPP.
  intro Hnone.

  assert (Hbad :
    forall i : Fin.t n,
      exists x : A i, ~ P i x).
  {
    intro i.

    apply NNPP.
    intro Hno.

    apply Hnone.
    exists i.

    intro x.
    apply NNPP.
    intro Hnot.
    apply Hno.
    exists x.
    exact Hnot.
  }

pose (f := fun i : Fin.t n =>
  proj1_sig
    (constructive_indefinite_description
       (fun x : A i => ~ P i x)
       (Hbad i))).

assert (Hf : forall i, ~ P i (f i)).
{
  intro i.
  unfold f.
  exact
    (proj2_sig
       (constructive_indefinite_description
          (fun x : A i => ~ P i x)
          (Hbad i))).
}

destruct (Hall f) as [i Hi].
exact (Hf i Hi).
Qed.

Definition send_residual
  (Y : stc_pure -> Prop)
  (p lbl : string)
  (sr : sort)
  : stc_pure -> Prop :=
  fun W =>
    Y
      (stc_pure_send p
        {| branch_labels := [(lbl, sr)] |}
        (fun _ => W)).

Definition receive_residual
  (Y : stc_pure -> Prop)
  (p : string)
  (lbl : string)
  (sr : sort)
  : stc_pure -> Prop :=
  fun W =>
    Y
      (stc_pure_receive p
        {| branch_labels := [(lbl, sr)] |}
        (fun _ => W)).

Definition receive_residual_exists
  (Y : stc_pure -> Prop)
  (p lbl : string)
  (sr : sort)
  (W : stc_pure) : Prop :=
  exists (sh : branch_shape)
         (next : branch_pos sh -> stc_pure)
         (j : branch_pos sh),
    List.length (branch_labels sh) = 1 /\
    fin_nth (branch_labels sh) j = (lbl, sr) /\
    next j = W /\
    Y (stc_pure_receive p sh next).

Definition send_residual_exists
  (Y : stc_pure -> Prop)
  (p lbl : string)
  (sr : sort)
  (W : stc_pure) : Prop :=
  exists (sh : branch_shape)
         (next : branch_pos sh -> stc_pure)
         (j : branch_pos sh),
    List.length (branch_labels sh) = 1 /\
    fin_nth (branch_labels sh) j = (lbl, sr) /\
    next j = W /\
    Y (stc_pure_send p sh next).

Definition valid_uniformisation_layer
  (S : uniformisation_state)
  (L : uniformisation_layer) : Prop :=
  match L with

  | uni_end =>
      uni_T S = stc_pure_end /\
      uni_Y S stc_pure_end

  | uni_send p lbl sr S' =>
      exists (sh : branch_shape)
             (next : branch_pos sh -> stc_pure)
             (i : branch_pos sh),

        uni_T S = stc_pure_send p sh next /\

        fin_nth (branch_labels sh) i = (lbl, sr) /\

        uni_T S' = next i /\

        (forall W : stc_pure,
           uni_Y S' W <->
           send_residual_exists
             (uni_Y S) p lbl sr W)

  | uni_receive p sh children =>
      exists (next : branch_pos sh -> stc_pure),

        uni_T S = stc_pure_receive p sh next /\

        (forall i : branch_pos sh,
           uni_T (children i) = next i) /\

        (forall i : branch_pos sh,
           let '(lbl, sr) :=
             fin_nth (branch_labels sh) i
           in
           forall W : stc_pure,
             uni_Y (children i) W <->
             receive_residual_exists
               (uni_Y S) p lbl sr W)

  end.

Lemma so_end_inv :
  forall U : stc_pure,
    stc_pure_to_so stc_pure_end U ->
    U = stc_pure_end.
Proof.
  intros U Hso.

  punfold Hso.

  destruct U as
    [| p sh next
     | p sh next];
    cbn [stc_pure_to_soR] in Hso.

  - reflexivity.
  - contradiction.
  - contradiction.

  apply stc_pure_to_soR_mon.
Qed.

Lemma si_send_congruence :
  forall (p : string)
         (sh : branch_shape)
         (next next' : branch_pos sh -> stc_pure),

    (forall i : branch_pos sh,
       stc_pure_to_si (next i) (next' i)) ->

    stc_pure_to_si
      (stc_pure_send p sh next)
      (stc_pure_send p sh next').
Proof.
  intros p sh next next' Hnext.

  unfold stc_pure_to_si.
  pfold.

  cbn [stc_pure_to_siR].

  split.
  - reflexivity.

  - unfold stc_pure_branches_bisim.

    exists eq_refl.
    intro i.

    destruct (fin_nth (branch_labels sh) i)
      as [lbl sr] eqn:Hkey.

    cbn.
    repeat split; try reflexivity.

rewrite Hkey.
cbn.

repeat split; try reflexivity.

left.
apply Hnext.
Qed.

Lemma so_send_singleton_inv :
  forall p sh next W,
    stc_pure_to_so
      (stc_pure_send p sh next) W ->
    exists (sh' : branch_shape)
           (next' : branch_pos sh' -> stc_pure)
           (i : branch_pos sh)
           (j : branch_pos sh'),
      W = stc_pure_send p sh' next' /\
      List.length (branch_labels sh') = 1 /\
      fin_nth (branch_labels sh) i =
        fin_nth (branch_labels sh') j /\
      stc_pure_to_so (next i) (next' j).
Proof.
  intros p sh next W Hso.

  pose proof Hso as Hso'.
  punfold Hso'.

  destruct W as
    [| q sh' next'
     | q sh' next'];
    cbn [stc_pure_to_soR] in Hso';
    try contradiction.

  destruct Hso' as
    [Hp [i [j [Hkey [Hsingleton Hrec]]]]].

  subst q.

  exists sh', next', i, j.

  split; try reflexivity.
  split. easy. split. easy.
  unfold stc_pure_to_so.
  destruct Hrec as [Hrec | Hbot].
    + exact Hrec.
    + contradiction.

  apply stc_pure_to_soR_mon.
Qed.

Definition si_witness
  (T : stc_pure) : Type :=
  { V : stc_pure |
      stc_pure_to_si T V }.

Lemma si_witness_inhabited :
  forall T,
    nonempty_pure T ->
    inhabited (si_witness T).
Proof.
  intros T HT.

  destruct (stc_pure_si_exists T HT)
    as [V HV].

  constructor.
  exists V.
  exact HV.
Qed.

Definition send_branch_success
  (p : string)
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure)
  (Y : stc_pure -> Prop)
  (i : branch_pos sh)
  (X : si_witness (next i)) : Prop :=

  let '(lbl, sr) :=
    fin_nth (branch_labels sh) i
  in

  exists W,
    stc_pure_to_so (proj1_sig X) W /\
    send_residual_exists Y p lbl sr W.

Lemma uniformisation_send_family :
  forall p sh next Y,

    (forall V,
       stc_pure_to_si
         (stc_pure_send p sh next) V ->
       exists W,
         stc_pure_to_so V W /\
         Y W) ->

    forall f :
      forall i : branch_pos sh,
        si_witness (next i),

    exists i : branch_pos sh,
      send_branch_success
        p sh next Y i (f i).
Proof.
  intros p sh next Y HY f.

  set (nextV :=
    fun i : branch_pos sh =>
      proj1_sig (f i)).

  assert (Hsi :
    stc_pure_to_si
      (stc_pure_send p sh next)
      (stc_pure_send p sh nextV)).
  {
    apply si_send_congruence.
    intro i.
    exact (proj2_sig (f i)).
  }

  destruct
    (HY (stc_pure_send p sh nextV) Hsi)
    as [Wfull [Hsofull HYfull]].

  destruct
    (so_send_singleton_inv
       p sh nextV Wfull Hsofull)
    as [sh' [next'
        [i [j
          [HWfull
            [Hsingleton
              [Hkey Hrec]]]]]]].

  exists i.

  unfold send_branch_success.
  unfold send_residual_exists.

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hi.

  simpl.

  exists (next' j).

  split.
  - exact Hrec.

  - exists sh', next', j.

    repeat split.
    + exact Hsingleton.
    + rewrite <- Hkey. easy.
    + rewrite HWfull in HYfull.
      exact HYfull.
Qed.

Lemma uniformisation_send_choice_exists :
  forall p sh next Y,

    nonempty_pure (stc_pure_send p sh next) ->

    (forall V,
       stc_pure_to_si
         (stc_pure_send p sh next) V ->
       exists W,
         stc_pure_to_so V W /\ Y W) ->

    exists i : branch_pos sh,
      let '(lbl, sr) :=
        fin_nth (branch_labels sh) i
      in
      forall V,
        stc_pure_to_si (next i) V ->
        exists W,
          stc_pure_to_so V W /\
          send_residual_exists Y p lbl sr W.
Proof.
  intros p sh next Y Hnonempty HY.

  (* Apply the finite uniform-choice principle. *)
  assert (Hchoice :
    exists i : branch_pos sh,
      forall X : si_witness (next i),
        send_branch_success
          p sh next Y i X).
  {
    apply finite_uniform_choice.

    - (* Every continuation has an SI decomposition. *)
      intro i.

      apply si_witness_inhabited.

      exact
        (nonempty_pure_send_next
           p sh next Hnonempty i).

    - (* Every family has a successful branch. *)
      intro f.

      eapply uniformisation_send_family.
      + exact HY.
  }

  destruct Hchoice as [i Hi].

  exists i.

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hkey.

  cbn.

  intros V Hsi.

specialize
  (Hi (exist
         (fun V0 : stc_pure =>
            stc_pure_to_si (next i) V0)
         V Hsi)).

unfold send_branch_success in Hi.

rewrite Hkey in Hi.
cbn in Hi.

exact Hi.
Qed.

Definition singleton_receive
  (p lbl : string)
  (sr : sort)
  (V : stc_pure) : stc_pure :=
  stc_pure_receive p
    {| branch_labels := [(lbl, sr)] |}
    (fun _ => V).

Lemma si_receive_singleton :
  forall (p : string)
         (sh : branch_shape)
         (next : branch_pos sh -> stc_pure)
         (i : branch_pos sh)
         (V : stc_pure),

    stc_pure_to_si (next i) V ->

    let '(lbl, sr) :=
      fin_nth (branch_labels sh) i
    in
    stc_pure_to_si
      (stc_pure_receive p sh next)
      (singleton_receive p lbl sr V).
Proof.
  intros p sh next i V Hsi.

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hkey.

  cbn.

  unfold stc_pure_to_si.
  pfold.

  cbn [stc_pure_to_siR].

  split.
  - reflexivity.

  - exists i.
    exists (@Fin.F1 0).

    repeat split.
    + rewrite Hkey.
      reflexivity.
    + left.
      exact Hsi.
Qed.

Lemma so_singleton_receive_inv :
  forall p lbl sr V Wfull,

    stc_pure_to_so
      (singleton_receive p lbl sr V)
      Wfull ->

    exists Wnext,
      stc_pure_to_so V Wnext /\
      receive_residual_exists
        (fun X => X = Wfull)
        p lbl sr Wnext.
Proof.
  intros p lbl sr V Wfull Hso.

  pose proof Hso as Hso'.
  punfold Hso'.

  destruct Wfull as
    [| q sh' next'
     | q sh' next'];
    cbn [singleton_receive stc_pure_to_soR] in Hso';
    try contradiction.

  destruct Hso' as [Hp Hbranches].
  subst q.

  unfold stc_pure_branches_bisim in Hbranches.

  destruct Hbranches as [Hlen Hnext].

  set (j :=
    eq_rect
      1
      Fin.t
      (@Fin.F1 0)
      (List.length (branch_labels sh'))
      Hlen).

  specialize (Hnext (@Fin.F1 0)).

  cbn in Hnext.

  destruct (fin_nth (branch_labels sh') j)
    as [lbl' sr'] eqn:Hkey.

unfold j in Hkey.
rewrite Hkey in Hnext.
cbn in Hnext.

destruct Hnext as [Hl [Hs Hrec]].

exists (next' j).

split.


- (* Recursive SO decomposition *)
  unfold stc_pure_to_so.
  destruct Hrec as [Hrec | Hbot].
  + exact Hrec.
  + contradiction.

- (* Receive residual *)
  unfold receive_residual_exists.

  exists sh', next', j.

  repeat split.
  + symmetry.
    exact Hlen.
unfold j.
rewrite Hkey.
rewrite Hl, Hs.
reflexivity.

  apply stc_pure_to_soR_mon.
Qed.


Lemma uniformisation_receive_choice_exists :
  forall p sh next Y,

    (forall V,
       stc_pure_to_si
         (stc_pure_receive p sh next) V ->
       exists W,
         stc_pure_to_so V W /\
         Y W) ->

    forall i : branch_pos sh,

      let '(lbl, sr) :=
        fin_nth (branch_labels sh) i
      in

      forall V,
        stc_pure_to_si (next i) V ->

        exists W,
          stc_pure_to_so V W /\
          receive_residual_exists
            Y p lbl sr W.
Proof.
  intros p sh next Y HY i.

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hkey.

  cbn.

  intros V Hsi.

  assert (Hfull :
    stc_pure_to_si
      (stc_pure_receive p sh next)
      (singleton_receive p lbl sr V)).
  {
    pose proof
      (si_receive_singleton p sh next i V Hsi)
      as H.

    rewrite Hkey in H.
    cbn in H.
    exact H.
  }

  destruct (HY _ Hfull)
    as [Wfull [Hsofull HYfull]].

  destruct
    (so_singleton_receive_inv
       p lbl sr V Wfull Hsofull)
    as [Wnext [Hso_next Hres]].

  exists Wnext.

  split.
  - exact Hso_next.

  - unfold receive_residual_exists in *.

    destruct Hres as
      [sh' [next' [j
        [Hlen [Hkey' [Hnext' HWfull]]]]]].

    exists sh', next', j.

    repeat split; try assumption.

    rewrite HWfull.
    exact HYfull.
Qed.

Definition make_receive_child
  (p : string)
  (sh : branch_shape)
  (next : branch_pos sh -> stc_pure)
  (Y : stc_pure -> Prop)
  (Hnonempty : nonempty_pure (stc_pure_receive p sh next))
  (HY :
    forall V,
      stc_pure_to_si
        (stc_pure_receive p sh next) V ->
      exists W,
        stc_pure_to_so V W /\ Y W)
  (i : branch_pos sh)
  : uniformisation_state.
Proof.
  refine
    {|
      uni_T := next i;

      uni_Y :=
        let '(lbl, sr) :=
          fin_nth (branch_labels sh) i
        in receive_residual_exists Y p lbl sr;

      uni_nonempty :=
        nonempty_pure_receive_next
          p sh next Hnonempty i;

      uni_H := _
    |}.

intros V Hsi.

pose proof
  (uniformisation_receive_choice_exists
     p sh next Y HY i)
  as Hchoice.

destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hkey
  in Hchoice |- *.

cbn in Hchoice |- *.

exact (Hchoice V Hsi).

Defined.

Lemma make_receive_child_T :
  forall p sh next Y
         (Hnonempty :
            nonempty_pure (stc_pure_receive p sh next))
         (HY :
            forall V,
              stc_pure_to_si
                (stc_pure_receive p sh next) V ->
              exists W,
                stc_pure_to_so V W /\ Y W)
         (i : branch_pos sh),
    uni_T
      (make_receive_child
         p sh next Y Hnonempty HY i)
    = next i.
Proof.
  intros.
  unfold make_receive_child.
  cbn.
  reflexivity.
Qed.

Lemma uniformisation_layer_exists :
  forall S : uniformisation_state,
    exists L : uniformisation_layer,
      valid_uniformisation_layer S L.
Proof.
  intros [T Y Hnonempty HY].
  simpl in *.

  destruct T as [| p sh next | p sh next].

  - (* End *)
    assert (Hsi :
      stc_pure_to_si stc_pure_end stc_pure_end).
    {
      unfold stc_pure_to_si.
      pfold.
      simpl.
      exact Coq.Init.Logic.I.
    }

    destruct (HY stc_pure_end Hsi)
      as [W [Hso HW]].

    apply so_end_inv in Hso.
    subst W.

    exists uni_end.
    simpl.
    split; [reflexivity | exact HW].

  - (* Send *)
    destruct
      (uniformisation_send_choice_exists
         p sh next Y Hnonempty HY)
      as [i Hchoice].

    destruct (fin_nth (branch_labels sh) i)
      as [lbl sr] eqn:Hkey.
set (S' :=
  {|
    uni_T := next i;
    uni_Y := send_residual_exists Y p lbl sr;
    uni_nonempty :=
      nonempty_pure_send_next
        p sh next Hnonempty i;
    uni_H := Hchoice
  |} : uniformisation_state).

exists (uni_send p lbl sr S').

unfold valid_uniformisation_layer.
cbn.

exists sh, next, i.

repeat split.
- exact Hkey.
easy. easy.

set (children :=
  fun i : branch_pos sh =>
    make_receive_child p sh next Y Hnonempty HY i).

exists (uni_receive p sh children).

unfold valid_uniformisation_layer.
cbn.

exists next. split. easy.

split.
- (* The child has the correct source continuation. *)
  intro i.
  unfold children.
  unfold make_receive_child.
  cbn.
destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hkey.
  easy.

- (* The child carries the correct residual predicate. *)
  intro i.

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hkey.

  intro W.

  unfold children.
  unfold make_receive_child. easy.
Qed.

From Coq Require Import Logic.ClassicalEpsilon.

Definition observe_uniformisation
  (S : uniformisation_state)
  : uniformisation_layer :=
  proj1_sig
    (constructive_indefinite_description
       (fun L : uniformisation_layer =>
          valid_uniformisation_layer S L)
       (uniformisation_layer_exists S)).

Lemma observe_uniformisation_correct :
  forall S : uniformisation_state,
    valid_uniformisation_layer
      S (observe_uniformisation S).
Proof.
  intro S.
  unfold observe_uniformisation.

  destruct
    (constructive_indefinite_description
       (fun L : uniformisation_layer =>
          valid_uniformisation_layer S L)
       (uniformisation_layer_exists S))
    as [L HL].

  simpl.
  exact HL.
Qed.

CoFixpoint make_uniform_so
  (S : uniformisation_state) : stc_pure :=
  match observe_uniformisation S with
  | uni_end =>
      stc_pure_end
  | uni_send p lbl sr S' =>
      stc_pure_send p
        {| branch_labels := [(lbl, sr)] |}
        (fun _ => make_uniform_so S')
  | uni_receive p sh children =>
      stc_pure_receive p sh
        (fun i => make_uniform_so (children i))
  end.

Definition uniformisation_candidate
  (S : uniformisation_state)
  (U : stc_pure) : Prop :=
  stc_pure_to_so (uni_T S) U /\
  forall W,
    stc_pure_to_si U W ->
    uni_Y S W.

Definition uniformisable
  (T : stc_pure)
  (Y : stc_pure -> Prop) : Prop :=
  (forall V,
     stc_pure_to_si T V ->
     exists W,
       stc_pure_to_so V W /\ Y W) ->
  exists U,
    stc_pure_to_so T U /\
    forall W,
      stc_pure_to_si U W ->
      Y W.

Lemma make_uniform_so_correct :
  forall S : uniformisation_state,
    stc_pure_to_so
      (uni_T S)
      (make_uniform_so S).
Proof.
  pcofix CIH.
  intro S.
  pfold.

  pose proof
    (observe_uniformisation_correct S)
    as Hvalid.

  destruct (observe_uniformisation S)
    as [| p lbl sr S' | p sh children]
    eqn:Hobs.

- (* End case *)
  cbn [valid_uniformisation_layer] in Hvalid.

  destruct Hvalid as [HT HY].

  rewrite HT.

  cbn [make_uniform_so stc_pure_to_soR].
  rewrite Hobs.
  cbn.

  exact Coq.Init.Logic.I.

cbn [valid_uniformisation_layer] in Hvalid.

destruct Hvalid as
  [sh [next [i [HT [Hkey [HT' Hres]]]]]].
rewrite HT.

cbn [make_uniform_so stc_pure_to_soR].
rewrite Hobs.
cbn.
split.
- reflexivity.

- exists i.
  exists (@Fin.F1 0).

  repeat split.

  + (* Branch labels match *)
    rewrite Hkey.
    reflexivity.
  + (* Recursive SO decomposition *)
    right.
    rewrite <- HT'.
    apply CIH.

- (* Receive *)
  cbn [valid_uniformisation_layer] in Hvalid.

  destruct Hvalid as
    [next [HT [Hchildren Hres]]].

  rewrite HT.

  cbn [make_uniform_so stc_pure_to_soR].
  rewrite Hobs.
  cbn.

  split.
  + reflexivity.

  + unfold stc_pure_branches_bisim.

    exists eq_refl.
    intro i.

    destruct (fin_nth (branch_labels sh) i)
      as [lbl sr] eqn:Hkey.

cbn.
rewrite Hkey.
cbn.

repeat split; try reflexivity.

right.
rewrite <- (Hchildren i).
apply CIH.
Qed.

Lemma si_end_inv :
  forall W : stc_pure,
    stc_pure_to_si stc_pure_end W ->
    W = stc_pure_end.
Proof.
  intros W Hsi.
  punfold Hsi.

  destruct W as
    [| p sh next
     | p sh next];
    cbn [stc_pure_to_siR] in Hsi;
    try contradiction;
    reflexivity.

  apply stc_pure_to_siR_mon.
Qed.

Definition observe_pure (T : stc_pure) : stc_pure :=
  match T with
  | stc_pure_end =>
      stc_pure_end
  | stc_pure_send p sh next =>
      stc_pure_send p sh next
  | stc_pure_receive p sh next =>
      stc_pure_receive p sh next
  end.

Lemma observe_pure_eq :
  forall T : stc_pure,
    T = observe_pure T.
Proof.
  intro T.
  destruct T; reflexivity.
Qed.

Lemma make_uniform_so_unfold :
  forall S : uniformisation_state,
    make_uniform_so S =
      match observe_uniformisation S with
      | uni_end =>
          stc_pure_end
      | uni_send p lbl sr S' =>
          stc_pure_send p
            {| branch_labels := [(lbl, sr)] |}
            (fun _ => make_uniform_so S')
      | uni_receive p sh children =>
          stc_pure_receive p sh
            (fun i => make_uniform_so (children i))
      end.
Proof.
  intro S.

  rewrite (observe_pure_eq (make_uniform_so S)) at 1.
  cbn.
  unfold observe_pure.
  cbn [make_uniform_so].
destruct (observe_uniformisation S)
  as [| p lbl sr S' | p sh children];
  reflexivity.
Qed.

Fixpoint stc_pure_eq_depth
  (n : nat)
  (T U : stc_pure) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      match T, U with
      | stc_pure_end, stc_pure_end =>
          True

      | stc_pure_send p sh next,
        stc_pure_send q sh' next' =>
          p = q /\
          exists H : sh = sh',
            forall i : branch_pos sh,
              stc_pure_eq_depth n'
                (next i)
                (next' (eq_rect sh branch_pos i sh' H))

      | stc_pure_receive p sh next,
        stc_pure_receive q sh' next' =>
          p = q /\
          exists H : sh = sh',
            forall i : branch_pos sh,
              stc_pure_eq_depth n'
                (next i)
                (next' (eq_rect sh branch_pos i sh' H))

      | _, _ => False
      end
  end.

Definition prefix_closed
  (Y : stc_pure -> Prop) : Prop :=
  forall W,
    (forall n,
       exists Wn,
         Y Wn /\
         stc_pure_eq_depth n W Wn) ->
    Y W.

Lemma fin_nth_length_one :
  forall (A : Type)
         (xs : list A)
         (i : Fin.t (List.length xs)),
    List.length xs = 1 ->
    xs = [fin_nth xs i].
Proof.
  intros A xs i Hlen.

  destruct xs as [| x xs].
  - discriminate Hlen.

  destruct xs as [| y xs].
  - simpl.
    assert (Hi : i = Fin.F1).
    {
dependent destruction i.
- reflexivity.
- inversion i.
    }
    subst i.
    reflexivity.

  - simpl in Hlen.
    discriminate Hlen.
Qed.

Lemma singleton_shapes_equal :
  forall (sh1 sh2 : branch_shape)
         (i : branch_pos sh1)
         (j : branch_pos sh2),

    List.length (branch_labels sh1) = 1 ->

    List.length (branch_labels sh2) = 1 ->

    fin_nth (branch_labels sh1) i =
    fin_nth (branch_labels sh2) j ->

    sh1 = sh2.
Proof.
  intros [xs] [ys] i j Hlen1 Hlen2 Hkey.
  simpl in *.

  assert (Hxs : xs = [fin_nth xs i]).
  {
    apply fin_nth_length_one.
    exact Hlen1.
  }

  assert (Hys : ys = [fin_nth ys j]).
  {
    apply fin_nth_length_one.
    exact Hlen2.
  }

  rewrite Hxs.
  rewrite Hys.
  rewrite Hkey.

  reflexivity.
Qed.

Lemma make_uniform_so_approximates_Y :
  forall S W,
    stc_pure_to_si (make_uniform_so S) W ->
    forall n,
      exists Wn,
        uni_Y S Wn /\
        stc_pure_eq_depth n W Wn.
Proof.
  intros S W Hsi n.
  revert S W Hsi.
  induction n as [| n IH].

  - (* Base case *)
    intros S W Hsi.

    destruct
      (stc_pure_si_exists
         (uni_T S)
         (uni_nonempty S))
      as [V HV].

    destruct (uni_H S V HV)
      as [Wn [Hso HY]].

    exists Wn.
    split.
    + exact HY.
    + easy.

  - (* Inductive case *)
    intros S W Hsi.

    pose proof
      (observe_uniformisation_correct S)
      as Hvalid.

    destruct (observe_uniformisation S)
      as [| p lbl sr S' | p sh children]
      eqn:Hobs.

destruct
  (stc_pure_si_exists
     (uni_T S)
     (uni_nonempty S))
  as [V HV].

destruct (uni_H S V HV)
  as [Wn [Hso HY]].

exists Wn.
split.
- exact HY.
cbn [valid_uniformisation_layer] in Hvalid.
destruct Hvalid as [HT Hend].

(* The constructed tree is end. *)
rewrite make_uniform_so_unfold in Hsi.
rewrite Hobs in Hsi.
cbn in Hsi.

apply si_end_inv in Hsi.
subst W.

(* The source tree is also end. *)
rewrite HT in HV.
apply si_end_inv in HV.
subst V.

(* Every SO decomposition of end is end. *)
apply so_end_inv in Hso.
subst Wn.

simpl.
easy.

cbn [valid_uniformisation_layer] in Hvalid.

destruct Hvalid as
  [sh [next [i [HT [Hkey [HT' Hres]]]]]].
rewrite make_uniform_so_unfold in Hsi.
rewrite Hobs in Hsi.
cbn in Hsi.
pose proof Hsi as Hsi'.
punfold Hsi'.

destruct W as
  [| q shw nextw
   | q shw nextw];
  cbn [stc_pure_to_siR] in Hsi';
  try contradiction.
destruct Hsi' as [Hp Hbranches].
subst q.

unfold stc_pure_branches_bisim in Hbranches.
destruct Hbranches as [Hlen Hnext].
specialize (Hnext (@Fin.F1 0)).

set (j :=
  eq_rect
    1 Fin.t (@Fin.F1 0)
    (List.length (branch_labels shw))
    Hlen).

cbn [branch_labels fin_nth] in Hnext.

change (
  let '(lbl2, sr2) :=
    fin_nth (branch_labels shw) j
  in
    lbl = lbl2 /\
    sr = sr2 /\
    upaco2 stc_pure_to_siR bot2
      (make_uniform_so S')
      (nextw j)
) in Hnext.
destruct (fin_nth (branch_labels shw) j)
  as [lbl' sr'] eqn:Hj.

unfold j in Hj.
destruct Hnext as [Hl [Hs Hrec]].
assert (Hsi_next :
  stc_pure_to_si (make_uniform_so S') (nextw j)).
{
  unfold stc_pure_to_si.
  destruct Hrec as [Hr | Hbot].
  - exact Hr.
  - contradiction.
}

destruct (IH S' (nextw j) Hsi_next)
  as [Wnext [HYnext Heqnext]].
pose proof
  (proj1 (Hres Wnext) HYnext)
  as Hresidual.

unfold send_residual_exists in Hresidual.

destruct Hresidual as
  [sh' [next' [j'
    [Hsingleton [Hlabel [Hcontinuation HYfull]]]]]].
exists (stc_pure_send p sh' next').

split.
- exact HYfull.
-
assert (Hkey_equal :
  fin_nth (branch_labels shw) j =
  fin_nth (branch_labels sh') j').
{
  unfold j.
  rewrite Hj.
  rewrite Hlabel.
  now rewrite Hl, Hs.
}

assert (Hshape : shw = sh').
{
  apply (singleton_shapes_equal shw sh' j j').
  - simpl in Hlen.
    symmetry.
    exact Hlen.
  - exact Hsingleton.
  - exact Hkey_equal.
}
subst.

cbn [stc_pure_eq_depth].

split.
- reflexivity.

- exists eq_refl.
  intro k.

  assert (Hkj : k = j).
  {
    eapply fin_unique_length_one.
    exact Hsingleton.
  }

  assert (Hjj' : j = j').
  {
    eapply fin_unique_length_one.
    exact Hsingleton.
  }

  subst k.
  subst j'.

  cbn.
  exact Heqnext.
  apply stc_pure_to_siR_mon.

cbn [valid_uniformisation_layer] in Hvalid.

destruct Hvalid as [next [HT [Hchildren Hres]]].
rewrite make_uniform_so_unfold in Hsi.
rewrite Hobs in Hsi.
cbn in Hsi.

pose proof Hsi as Hsi'.
punfold Hsi'.

destruct W as
  [| q shw nextw
   | q shw nextw];
  cbn [stc_pure_to_siR] in Hsi';
  try contradiction.

destruct Hsi' as
  [Hp [i [j [Hkey [Hsingleton Hrec]]]]].

subst q.

assert (Hsi_next :
  stc_pure_to_si
    (make_uniform_so (children i))
    (nextw j)).
{
  unfold stc_pure_to_si.
  destruct Hrec as [Hr | Hbot].
  - exact Hr.
  - contradiction.
}
destruct (IH (children i) (nextw j) Hsi_next)
  as [Wnext [HYnext Heqnext]].

destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hi.

specialize (Hres i).

rewrite Hi in Hres.
cbn in Hres.

pose proof
  (proj1 (Hres Wnext) HYnext)
  as Hresidual.

unfold receive_residual_exists in Hresidual.

destruct Hresidual as
  [shr [nextr [jr
    [Hlenr [Hkeyr [Hcontinuation HYfull]]]]]].

exists (stc_pure_receive p shr nextr).

split.
- exact HYfull.
- subst.
assert (Hkey_equal :
  fin_nth (branch_labels shw) j =
  fin_nth (branch_labels shr) jr).
{
  rewrite <- Hkey.
  symmetry.
  exact Hkeyr.
}
assert (Hshape : shw = shr).
{
  eapply singleton_shapes_equal.
  - exact Hsingleton.
  - exact Hlenr.
  - exact Hkey_equal.
}

subst shr.

cbn [stc_pure_eq_depth].

split.
- reflexivity.
- exists eq_refl.
  intro k.
assert (Hkj : k = j).
{
  eapply fin_unique_length_one.
  exact Hsingleton.
}

assert (Hjjr : j = jr).
{
  eapply fin_unique_length_one.
  exact Hsingleton.
}
subst k.
subst jr.

cbn.
exact Heqnext.
apply stc_pure_to_siR_mon.
Qed.

Lemma make_uniform_so_global_correct_closed :
  forall S : uniformisation_state,
    prefix_closed (uni_Y S) ->
    forall W,
      stc_pure_to_si (make_uniform_so S) W ->
      uni_Y S W.
Proof.
  intros S Hclosed W Hsi.
  apply Hclosed.
  intro n.
  exact (make_uniform_so_approximates_Y S W Hsi n).
Qed.

Theorem decomposition_uniformisation_closed :
  forall (T : stc_pure)
         (Y : stc_pure -> Prop),

    nonempty_pure T ->

    prefix_closed Y ->

    (forall V,
       stc_pure_to_si T V ->
       exists W,
         stc_pure_to_so V W /\
         Y W) ->

    exists U,
      stc_pure_to_so T U /\
      forall W,
        stc_pure_to_si U W ->
        Y W.
Proof.
  intros T Y Hnonempty Hclosed HY.

  set (S :=
    {|
      uni_T := T;
      uni_Y := Y;
      uni_nonempty := Hnonempty;
      uni_H := HY
    |} : uniformisation_state).

  exists (make_uniform_so S).

  split.
  - exact (make_uniform_so_correct S).

  - intros W Hsi.
    apply (make_uniform_so_global_correct_closed S).
    + exact Hclosed.
    + exact Hsi.
Qed.


(* ============================================================ *)
(* SISO REFINEMENT FOR stc_pure                                  *)
(* ============================================================ *)

From Coq Require Import String List.
From Paco Require Import paco.

Import ListNotations.


(* ============================================================ *)
(* 1. Canonical singleton constructors                           *)
(* ============================================================ *)

Definition singleton_send
  (p lbl : string)
  (sr : sort)
  (T : stc_pure) : stc_pure :=
  stc_pure_send p
    {| branch_labels := [(lbl, sr)] |}
    (fun _ => T).

(* singleton_receive is already defined in our development. *)


(* ============================================================ *)
(* 2. Actions                                                    *)
(* ============================================================ *)

Inductive pure_action : Type :=
| pure_input :
    string -> string -> sort -> pure_action

| pure_output :
    string -> string -> sort -> pure_action.


(* ============================================================ *)
(* 3. Permitted anticipation actions                             *)
(* ============================================================ *)

Definition allowed_A
  (p : string)
  (a : pure_action) : Prop :=
  match a with
  | pure_input q _ _ =>
      q <> p

  | pure_output _ _ _ =>
      False
  end.

Definition allowed_B
  (p : string)
  (a : pure_action) : Prop :=
  match a with
  | pure_input _ _ _ =>
      True

  | pure_output q _ _ =>
      q <> p
  end.


(* ============================================================ *)
(* 4. Finite anticipation prefixes                               *)
(* ============================================================ *)

Definition pure_prefix := list pure_action.

(* Empty prefixes are allowed.
   They represent direct matching without anticipation. *)

Definition A_prefix
  (p : string)
  (xs : pure_prefix) : Prop :=
  List.Forall (allowed_A p) xs.

Definition B_prefix
  (p : string)
  (xs : pure_prefix) : Prop :=
  List.Forall (allowed_B p) xs.


(* ============================================================ *)
(* 5. Prepending finite prefixes                                 *)
(* ============================================================ *)

Fixpoint prepend_pure
  (xs : pure_prefix)
  (T : stc_pure) : stc_pure :=
  match xs with

  | [] =>
      T

  | pure_input p lbl sr :: xs' =>
      singleton_receive p lbl sr
        (prepend_pure xs' T)

  | pure_output p lbl sr :: xs' =>
      singleton_send p lbl sr
        (prepend_pure xs' T)

  end.


(* ============================================================ *)
(* 6. Action keys                                                *)
(* ============================================================ *)

Inductive pure_action_key : Type :=
| key_input :
    string -> pure_action_key

| key_output :
    string -> pure_action_key.


Definition action_key
  (a : pure_action) : pure_action_key :=
  match a with

  | pure_input p _ _ =>
      key_input p

  | pure_output p _ _ =>
      key_output p

  end.


(* ============================================================ *)
(* 7. Action occurrence                                          *)
(* ============================================================ *)

Inductive pure_has_action
  (a : pure_action_key)
  : stc_pure -> Prop :=

| has_send_here :
    forall p sh next,
      a = key_output p ->
      pure_has_action a
        (stc_pure_send p sh next)

| has_receive_here :
    forall p sh next,
      a = key_input p ->
      pure_has_action a
        (stc_pure_receive p sh next)

| has_send_later :
    forall p sh next
           (i : branch_pos sh),
      pure_has_action a (next i) ->
      pure_has_action a
        (stc_pure_send p sh next)

| has_receive_later :
    forall p sh next
           (i : branch_pos sh),
      pure_has_action a (next i) ->
      pure_has_action a
        (stc_pure_receive p sh next).


(* ============================================================ *)
(* 8. Equality of action sets                                    *)
(* ============================================================ *)

Definition pure_act_eq
  (T U : stc_pure) : Prop :=
  forall a : pure_action_key,
    pure_has_action a T <->
    pure_has_action a U.


Lemma pure_act_eq_refl :
  forall T,
    pure_act_eq T T.
Proof.
  intros T a.
  reflexivity.
Qed.


Lemma pure_act_eq_sym :
  forall T U,
    pure_act_eq T U ->
    pure_act_eq U T.
Proof.
  intros T U H a.
  symmetry.
  apply H.
Qed.


Lemma pure_act_eq_trans :
  forall T U V,
    pure_act_eq T U ->
    pure_act_eq U V ->
    pure_act_eq T V.
Proof.
  intros T U V HTU HUV a.
  transitivity (pure_has_action a U).
  - apply HTU.
  - apply HUV.
Qed.


(* ============================================================ *)
(* 9. Prefix conditions                                          *)
(* ============================================================ *)

(* For empty prefixes, no action-equality condition is needed.

   For nonempty prefixes, action equality is required.

   This combines the paper's direct matching rules
   with genuine asynchronous anticipation. *)

Definition A_prefix_condition
  (p : string)
  (xs : pure_prefix)
  (T U : stc_pure) : Prop :=
  A_prefix p xs /\
  (xs = [] \/
   pure_act_eq T (prepend_pure xs U)).


Definition B_prefix_condition
  (p : string)
  (xs : pure_prefix)
  (T U : stc_pure) : Prop :=
  B_prefix p xs /\
  (xs = [] \/
   pure_act_eq T (prepend_pure xs U)).


(* ============================================================ *)
(* 10. SISO refinement functional                                *)
(* ============================================================ *)

Inductive stc_pure_refinementR
  (r : stc_pure -> stc_pure -> Prop)
  : stc_pure -> stc_pure -> Prop :=

(* ------------------------------------------------------------ *)
(* Termination                                                   *)
(* ------------------------------------------------------------ *)

| pure_ref_end :
    stc_pure_refinementR r
      stc_pure_end
      stc_pure_end


(* ------------------------------------------------------------ *)
(* Input matching / R1 anticipation                              *)
(* ------------------------------------------------------------ *)

| pure_ref_input :
    forall p lbl s s' T U xs,

      (* Contravariant input sorts *)
      subsort s' s ->

      (* Empty prefix = direct input matching.
         Nonempty prefix = R1 anticipation. *)
      A_prefix_condition p xs T U ->

      (* Recursive refinement *)
      r T (prepend_pure xs U) ->

      stc_pure_refinementR r
        (singleton_receive p lbl s T)
        (prepend_pure xs
          (singleton_receive p lbl s' U))


(* ------------------------------------------------------------ *)
(* Output matching / R2 anticipation                             *)
(* ------------------------------------------------------------ *)

| pure_ref_output :
    forall p lbl s s' T U xs,

      (* Covariant output sorts *)
      subsort s s' ->

      (* Empty prefix = direct output matching.
         Nonempty prefix = R2 anticipation. *)
      B_prefix_condition p xs T U ->

      (* Recursive refinement *)
      r T (prepend_pure xs U) ->

      stc_pure_refinementR r
        (singleton_send p lbl s T)
        (prepend_pure xs
          (singleton_send p lbl s' U)).


(* ============================================================ *)
(* 11. Paco refinement                                           *)
(* ============================================================ *)

Definition stc_pure_refinement :
  stc_pure -> stc_pure -> Prop :=
  paco2 stc_pure_refinementR bot2.


(* ============================================================ *)
(* 12. Monotonicity                                              *)
(* ============================================================ *)

Lemma stc_pure_refinementR_mon :
  monotone2 stc_pure_refinementR.
Proof.
  unfold monotone2.
  intros T U r r' H LE.

  induction H.

  - (* End *)
    constructor.

  - (* Input / R1 *)
    eapply pure_ref_input.
    + eassumption.
    + eassumption.
    + apply LE.
      eassumption.

  - (* Output / R2 *)
    eapply pure_ref_output.
    + eassumption.
    + eassumption.
    + apply LE.
      eassumption.
Qed.

Hint Resolve stc_pure_refinementR_mon : paco.

Definition subtype_pure
  (T T' : stc_pure) : Prop :=
  forall U V,
    stc_pure_to_so T U ->
    stc_pure_to_si T' V ->
    exists W W',
      stc_pure_to_si U W /\
      stc_pure_to_so V W' /\
      stc_pure_refinement W W'.

Lemma refinement_end :
  stc_pure_refinement
    stc_pure_end stc_pure_end.
Proof.
  pfold.
  constructor.
Qed.

Lemma singleton_send_canonical :
  forall p sh next
         (i : branch_pos sh)
         lbl sr,
    List.length (branch_labels sh) = 1 ->
    fin_nth (branch_labels sh) i = (lbl, sr) ->
    stc_pure_send p sh next =
      singleton_send p lbl sr (next i).
Proof.
  intros p sh next i lbl sr Hlen Hkey.

  assert (Hshape :
    sh = {| branch_labels := [(lbl, sr)] |}).
  {
    eapply singleton_shapes_equal
      with (i := i) (j := Fin.F1).

    - exact Hlen.
    - reflexivity.
    - rewrite Hkey.
      reflexivity.
  }

  subst sh.

  unfold singleton_send.

  f_equal.

  apply functional_extensionality.
  intro j.

  assert (Hji : j = i).
  {
    eapply fin_unique_length_one.
    reflexivity.
  }

  subst j.
  reflexivity.
Qed.

Lemma singleton_receive_canonical :
  forall p sh next
         (i : branch_pos sh)
         lbl sr,
    List.length (branch_labels sh) = 1 ->
    fin_nth (branch_labels sh) i = (lbl, sr) ->
    stc_pure_receive p sh next =
      singleton_receive p lbl sr (next i).
Proof.
  intros p sh next i lbl sr Hlen Hkey.

  assert (Hshape :
    sh = {| branch_labels := [(lbl, sr)] |}).
  {
    eapply singleton_shapes_equal
      with (i := i) (j := Fin.F1).

    - exact Hlen.
    - reflexivity.
    - rewrite Hkey.
      reflexivity.
  }

  subst sh.

  unfold singleton_receive.

  f_equal.

  apply functional_extensionality.
  intro j.

  assert (Hji : j = i).
  {
    eapply fin_unique_length_one.
    reflexivity.
  }

  subst j.
  reflexivity.
Qed.


CoFixpoint repeat_receive_pure
  (q lbl : string)
  (sr : sort) : stc_pure :=
  singleton_receive q lbl sr
    (repeat_receive_pure q lbl sr).

Fixpoint repeat_input_prefix
  (n : nat)
  (q lbl : string)
  (sr : sort) : pure_prefix :=
  match n with
  | 0 => []
  | S n' =>
      pure_input q lbl sr ::
        repeat_input_prefix n' q lbl sr
  end.

Definition counter_L
  (p q lp lq : string)
  (sr : sort) : stc_pure :=
  singleton_send p lp sr
    (repeat_receive_pure q lq sr).

Definition counter_R
  (n : nat)
  (p q lp lq : string)
  (sr : sort) : stc_pure :=
  prepend_pure
    (repeat_input_prefix n q lq sr)
    (counter_L p q lp lq sr).

Definition counter_R_infinity
  (q lq : string)
  (sr : sort) : stc_pure :=
  repeat_receive_pure q lq sr.

Lemma repeat_receive_pure_unfold :
  forall q lbl sr,
    repeat_receive_pure q lbl sr =
    singleton_receive q lbl sr
      (repeat_receive_pure q lbl sr).
Proof.
  intros q lbl sr.

  rewrite
    (observe_pure_eq
       (repeat_receive_pure q lbl sr))
    at 1.

  unfold observe_pure.
  cbn [repeat_receive_pure].

  reflexivity.
Qed.

Lemma counter_R_approximates_infinity :
  forall n p q lp lq sr,
    stc_pure_eq_depth n
      (counter_R_infinity q lq sr)
      (counter_R n p q lp lq sr).
Proof.
  induction n as [| n IH].

  - (* Depth zero *)
    intros.
    simpl.
    easy.

  - (* Successor depth *)
    intros p q lp lq sr.

    unfold counter_R_infinity.
    unfold counter_R.

    rewrite repeat_receive_pure_unfold.

    cbn [repeat_input_prefix prepend_pure].

    unfold singleton_receive.

    cbn [stc_pure_eq_depth].

    split.
    + reflexivity.

    + exists eq_refl.
      intro i.

      cbn.

      (* Both continuations agree up to depth n. *)
      change
        (stc_pure_eq_depth n
          (counter_R_infinity q lq sr)
          (counter_R n p q lp lq sr)).

      apply IH.
Qed.

Lemma repeat_receive_has_action :
  forall q lq sr a,
    pure_has_action a (repeat_receive_pure q lq sr) <->
    a = key_input q.
Proof.
  intros q lq sr a.
  split.
  - intro H.
    remember (repeat_receive_pure q lq sr) as T eqn:HT.
    revert q lq sr HT.

    induction H; intros q0 lq0 sr0 HT;
      rewrite repeat_receive_pure_unfold in HT;
      unfold singleton_receive in HT;
      inversion HT; subst; clear HT.

    + easy. (* Send at root: impossible *)

    + (* Receive continuation *)
apply Eqdep.EqdepTheory.inj_pair2 in H3.

assert (Hnext :
  next i = repeat_receive_pure q0 lq0 sr0).
{
  exact (f_equal (fun f => f i) H3).
}

rewrite (IHpure_has_action q0 lq0 sr0 Hnext). easy.

  - intro Ha.
    subst a.
    rewrite repeat_receive_pure_unfold.
    unfold singleton_receive.
    apply has_receive_here.
    reflexivity.
Qed.

Lemma pure_act_eq_receive_prefix :
  forall q lbl sr T,
    pure_has_action (key_input q) T ->
    pure_act_eq
      T
      (singleton_receive q lbl sr T).
Proof.
  intros q lbl sr T Hq a.
  unfold pure_act_eq.
  split.

  - (* Every action in T occurs in the prefixed tree. *)
    intro Ha.

    unfold singleton_receive.

    eapply has_receive_later
      with (i := Fin.F1).

    exact Ha.

  - (* Every action in the prefixed tree occurs in T. *)
    intro Ha.

    unfold singleton_receive in Ha.

    inversion Ha; subst; clear Ha.

    + (* New receive action at the root. *)
      exact Hq.

    + (* Action occurs in the continuation. *)
apply Eqdep.EqdepTheory.inj_pair2 in H2.

assert (Hnext : next0 i = T).
{
  exact (f_equal (fun f => f i) H2).
}

rewrite Hnext in H0.
exact H0.
Qed.

Lemma repeat_receive_prefix_act_eq :
  forall n q lq sr,
    pure_act_eq
      (repeat_receive_pure q lq sr)
      (prepend_pure
        (repeat_input_prefix n q lq sr)
        (repeat_receive_pure q lq sr)).
Proof.
  induction n as [| n IH].
  - intros q lq sr.
    simpl.
    apply pure_act_eq_refl.

  - intros q lq sr.
    simpl [repeat_input_prefix prepend_pure].

    eapply pure_act_eq_trans.
    + apply IH.
    + apply pure_act_eq_receive_prefix.

      destruct n as [| n'].
      * simpl.
        apply
          (proj2
            (repeat_receive_has_action
               q lq sr (key_input q))).
        reflexivity.

      * simpl [repeat_input_prefix prepend_pure].
        unfold singleton_receive.
        apply has_receive_here.
        reflexivity.
Qed.


Definition repeat_receive_prefix_rel
  (q lq : string)
  (sr : sort)
  : stc_pure -> stc_pure -> Prop :=
  fun T U =>
    exists n,
      T = repeat_receive_pure q lq sr /\
      U =
        prepend_pure
          (repeat_input_prefix n q lq sr)
          (repeat_receive_pure q lq sr).

Lemma repeat_receive_prefix_rel_step :
  forall q lq sr T U,
    repeat_receive_prefix_rel q lq sr T U ->
    stc_pure_refinementR
      (upaco2 stc_pure_refinementR
         (repeat_receive_prefix_rel q lq sr))
      T U.
Proof.
  intros q lq sr T U Hrel.

  destruct Hrel as [n [HT HU]].
  subst T U.

  rewrite repeat_receive_pure_unfold.

  destruct n as [| n].

  - (* Zero prefix *)
    cbn [repeat_input_prefix prepend_pure].

    rewrite repeat_receive_pure_unfold.

    eapply pure_ref_input
      with (xs := []).

    + apply srefl.

    + unfold A_prefix_condition, A_prefix.
      split.
      * constructor.
      * left. reflexivity.

    + right.
unfold repeat_receive_prefix_rel.

exists 0.
split.
- symmetry.
  apply repeat_receive_pure_unfold.

- cbn [repeat_input_prefix prepend_pure].
  symmetry.
  apply repeat_receive_pure_unfold.


  - (* Positive prefix *)
    cbn [repeat_input_prefix prepend_pure].

    eapply pure_ref_input
      with (xs := []).

    + apply srefl.

    + unfold A_prefix_condition, A_prefix.
      split.
      * constructor.
      * left. reflexivity.

    + right.
      exists n.
split.
- reflexivity.
- cbn [prepend_pure].
  replace
    (singleton_receive q lq sr
       (repeat_receive_pure q lq sr))
    with
    (repeat_receive_pure q lq sr).
  + reflexivity.
  + apply repeat_receive_pure_unfold.
Qed.

Lemma repeat_receive_prefix_refinement :
  forall n q lq sr,
    stc_pure_refinement
      (repeat_receive_pure q lq sr)
      (prepend_pure
        (repeat_input_prefix n q lq sr)
        (repeat_receive_pure q lq sr)).
Proof.
  intros n q lq sr.

  eapply paco2_acc
    with (l := repeat_receive_prefix_rel q lq sr)
         (r := bot2).

  - intros rr INCr INCl x y Hxy.

    pfold.

    eapply stc_pure_refinementR_mon.

    + apply repeat_receive_prefix_rel_step.
      exact Hxy.

    + intros x' y' Hrel.
      destruct Hrel as [Hpaco | Hrr].

      * left.
eapply paco2_mon.
- exact Hpaco.
- intros a b Hab.
  apply INCl.
  exact Hab.

      * right.
        apply INCl.
        exact Hrr.

  - exists n.
    split; reflexivity.
Qed.

Lemma counter_R_finite_refinement :
  forall n p q lp lq sr,
    stc_pure_refinement
      (counter_L p q lp lq sr)
      (counter_R n p q lp lq sr).
Proof.
  intros n p q lp lq sr.

  unfold counter_L, counter_R.

  pfold.

  eapply pure_ref_output
    with
      (xs := repeat_input_prefix n q lq sr)
      (U := repeat_receive_pure q lq sr).

  - (* Sort covariance *)
    apply srefl.

  - (* B-prefix condition *)
    unfold B_prefix_condition.
    split.

    + (* All prefix actions are permitted. *)
      induction n as [| n IH].
      * constructor.
      * simpl.
        constructor.
        -- easy.
        -- exact IH.

    + (* Empty prefix or action equality *)
      destruct n as [| n].
      * left.
        reflexivity.
      * right.
        apply repeat_receive_prefix_act_eq.

  - (* Recursive refinement *)
left.
apply repeat_receive_prefix_refinement.
Qed.

Lemma repeat_receive_not_prefixed_send :
  forall q lq sr xs p lp sp U,
    repeat_receive_pure q lq sr <>
    prepend_pure xs (singleton_send p lp sp U).
Proof.
  intros q lq sr xs.
  induction xs as [| a xs IH];
    intros p lp sp U Heq.

  - (* Empty prefix *)
    cbn [prepend_pure] in Heq.

    rewrite repeat_receive_pure_unfold in Heq.
    unfold singleton_receive, singleton_send in Heq.

    discriminate Heq.

  - (* Nonempty prefix *)
    destruct a as
      [r lbl s | r lbl s].

    + (* Input prefix *)
      cbn [prepend_pure] in Heq.

      rewrite repeat_receive_pure_unfold in Heq.
      unfold singleton_receive in Heq.

      inversion Heq; subst.
    + (* Output prefix *)
      cbn [prepend_pure] in Heq.

      rewrite repeat_receive_pure_unfold in Heq.
      unfold singleton_receive, singleton_send in Heq.

apply Eqdep.EqdepTheory.inj_pair2 in H3.

pose proof
  (f_equal (fun f => f Fin.F1) H3)
  as Hcont.

cbn in Hcont.

apply (IH p lp sp U).
exact Hcont.

cbn [prepend_pure] in Heq.
rewrite repeat_receive_pure_unfold in Heq.
unfold singleton_receive, singleton_send in Heq.
discriminate Heq.
Qed.

Lemma counter_R_infinite_not_refinement :
  forall p q lp lq sr,
    ~ stc_pure_refinement
        (counter_L p q lp lq sr)
        (counter_R_infinity q lq sr).
Proof.
  intros p q lp lq sr Href.

  unfold stc_pure_refinement in Href.
  punfold Href.

  unfold counter_L, counter_R_infinity in Href.

  inversion Href; subst; clear Href.
eapply repeat_receive_not_prefixed_send.
symmetry.
exact H4.
Qed.

Theorem refinement_not_prefix_closed :
  forall p q lp lq sr,
    ~ prefix_closed
        (fun W =>
           stc_pure_refinement
             (counter_L p q lp lq sr) W).
Proof.
  intros p q lp lq sr Hclosed.

  apply (counter_R_infinite_not_refinement
           p q lp lq sr).

  apply Hclosed.
  intro n.

  exists (counter_R n p q lp lq sr).

  split.
  - apply counter_R_finite_refinement.
  - apply counter_R_approximates_infinity.
Qed.

Definition refinement_preimage
  (U1 : stc_pure)
  (W2 : stc_pure) : Prop :=
  exists W1,
    stc_pure_to_si U1 W1 /\
    stc_pure_refinement W1 W2.

Definition repeat_receive_si_rel
  (T U : stc_pure) : Prop :=
  exists q lq sr,
    T = repeat_receive_pure q lq sr /\
    U = repeat_receive_pure q lq sr.

Lemma repeat_receive_si_rel_step :
  forall T U,
    repeat_receive_si_rel T U ->
    stc_pure_to_siR
      (upaco2 stc_pure_to_siR repeat_receive_si_rel)
      T U.
Proof.
  intros T U Hrel.
  destruct Hrel as [q [lq [sr [HT HU]]]].
  subst T U.

  rewrite repeat_receive_pure_unfold.
  unfold singleton_receive.

  cbn [stc_pure_to_siR].

  (* Both trees have the same receive participant. *)
  split.
  - reflexivity.

  (* The target has exactly one receive branch. *)
  - exists Fin.F1, Fin.F1.

    repeat split; try reflexivity.

    right.
    exists q, lq, sr.
    split; reflexivity.
Qed.

Lemma repeat_receive_pure_si_self :
  forall q lq sr,
    stc_pure_to_si
      (repeat_receive_pure q lq sr)
      (repeat_receive_pure q lq sr).
Proof.
  intros q lq sr.

  unfold stc_pure_to_si.

  eapply paco2_acc
    with (l := repeat_receive_si_rel)
         (r := bot2).

  - intros rr INCr INCl x y Hxy.

    pfold.

    eapply stc_pure_to_siR_mon.

    + apply repeat_receive_si_rel_step.
      exact Hxy.

    + intros x' y' Hrel.
      destruct Hrel as [Hpaco | Hinv].

      * left.
        eapply paco2_mon.
        -- exact Hpaco.
        -- intros a b Hab.
           apply INCl.
           exact Hab.

      * right.
        apply INCl.
        exact Hinv.

  - exists q, lq, sr.
    split; reflexivity.
Qed.


Lemma counter_L_si_self :
  forall p q lp lq sr,
    stc_pure_to_si
      (counter_L p q lp lq sr)
      (counter_L p q lp lq sr).
Proof.
  intros p q lp lq sr.

  unfold counter_L, singleton_send.

  pfold.
  cbn [stc_pure_to_siR].

  split.
  - reflexivity.
unfold stc_pure_branches_bisim.

exists eq_refl.
intro i.

cbn.

destruct (fin_nth (branch_labels
  {| branch_labels := [(lp, sr)] |}) i)
  as [lbl sri] eqn:Hkey.

assert (Hi : i = Fin.F1).
{
  eapply fin_unique_length_one.
  reflexivity.
}

subst i.
cbn.

repeat split; try reflexivity.

left.
apply repeat_receive_pure_si_self.
Qed.

Lemma counter_L_si_not_refine_infinity :
  forall p q lp lq sr W,
    stc_pure_to_si
      (counter_L p q lp lq sr) W ->
    ~ stc_pure_refinement
        W
        (counter_R_infinity q lq sr).
Proof.
  intros p q lp lq sr W Hsi Href.

  (* Expose the SI decomposition. *)
  unfold counter_L in Hsi.
  punfold Hsi.

  (* SI preserves the initial send constructor. *)
  destruct W as
    [| pw shw nextw
     | pw shw nextw];
    cbn [stc_pure_to_siR] in Hsi;
    try contradiction.

  (* Only the send case survives. *)
  destruct Hsi as [Hp Hbranches].
  subst pw.

  (* Expose the refinement relation. *)
  unfold stc_pure_refinement in Href.
  punfold Href.

  (* Only pure_ref_output can have a send on the left. *)
  inversion Href; subst; clear Href.

  (* The right-hand tree must contain a send
     after some finite anticipation prefix. *)
  eapply repeat_receive_not_prefixed_send.

  symmetry.
  eassumption.
  apply stc_pure_to_siR_mon.
Qed.

Theorem refinement_preimage_not_prefix_closed :
  forall p q lp lq sr,
    ~ prefix_closed
        (refinement_preimage
           (counter_L p q lp lq sr)).
Proof.
  intros p q lp lq sr Hclosed.

  assert (Hlimit :
    refinement_preimage
      (counter_L p q lp lq sr)
      (counter_R_infinity q lq sr)).
  {
    apply Hclosed.
    intro n.

    exists (counter_R n p q lp lq sr).
    split.
    - exists (counter_L p q lp lq sr).
      split.
      + apply counter_L_si_self.
      + apply counter_R_finite_refinement.
    - apply counter_R_approximates_infinity.
  }

  destruct Hlimit as [W1 [Hsi Href]].

  eapply counter_L_si_not_refine_infinity.
  - exact Hsi.
  - exact Href.
Qed.

Lemma refinement_uniformisation_approx :
  forall T U1,
    nonempty_pure T ->
    (forall V,
       stc_pure_to_si T V ->
       exists W,
         stc_pure_to_so V W /\
         refinement_preimage U1 W) ->
    exists U,
      stc_pure_to_so T U /\
      forall W,
        stc_pure_to_si U W ->
        forall n,
          exists Wn,
            refinement_preimage U1 Wn /\
            stc_pure_eq_depth n W Wn.
Proof.
  intros T U1 Hnonempty H.

  set (S :=
    {|
      uni_T := T;
      uni_Y := refinement_preimage U1;
      uni_nonempty := Hnonempty;
      uni_H := H
    |} : uniformisation_state).

  exists (make_uniform_so S).

  split.
  - exact (make_uniform_so_correct S).

  - intros W Hsi n.
    exact (make_uniform_so_approximates_Y S W Hsi n).
Qed.

Lemma refinement_send_choice_exists :
  forall p sh next U1,
    nonempty_pure (stc_pure_send p sh next) ->

    (forall V,
       stc_pure_to_si
         (stc_pure_send p sh next) V ->
       exists W,
         stc_pure_to_so V W /\
         refinement_preimage U1 W) ->

    exists (i : branch_pos sh)
           (lbl : string)
           (sr : sort),

      fin_nth (branch_labels sh) i = (lbl, sr) /\

      forall V,
        stc_pure_to_si (next i) V ->
        exists W,
          stc_pure_to_so V W /\
          send_residual_exists
            (refinement_preimage U1)
            p lbl sr W.
Proof.
  intros p sh next U1 Hnonempty HY.

  destruct
    (uniformisation_send_choice_exists
       p sh next
       (refinement_preimage U1)
       Hnonempty HY)
    as [i Hchoice].

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hkey.

  exists i, lbl, sr.

  split.
  - exact Hkey.
  - exact Hchoice.
Qed.

Lemma refinementR_right_send_inv :
  forall r W1 p lbl sr W2,
    stc_pure_refinementR r
      W1
      (singleton_send p lbl sr W2) ->
    (exists q l s T,
       W1 = singleton_receive q l s T) \/
    (exists q l s T,
       W1 = singleton_send q l s T).
Proof.
  intros r W1 p lbl sr W2 Href.
  inversion Href; subst.
  - (* Input *)
    left.
    eexists _, _, _, _.
    reflexivity.
  - (* Output *)
    right.
    eexists _, _, _, _.
    reflexivity.
Qed.

Lemma refinementR_inv :
  forall r T U,
    stc_pure_refinementR r T U ->
    (T = stc_pure_end /\
     U = stc_pure_end) \/

    (exists p lbl s s' T' U' xs,
       T = singleton_receive p lbl s T' /\
       U = prepend_pure xs
             (singleton_receive p lbl s' U') /\
       subsort s' s /\
       A_prefix_condition p xs T' U' /\
       r T' (prepend_pure xs U')) \/

    (exists p lbl s s' T' U' xs,
       T = singleton_send p lbl s T' /\
       U = prepend_pure xs
             (singleton_send p lbl s' U') /\
       subsort s s' /\
       B_prefix_condition p xs T' U' /\
       r T' (prepend_pure xs U')).
Proof.
  intros r T U Href.
  destruct Href.

  - (* End *)
    left.
    split; reflexivity.

  - (* Input / R1 *)
    right.
    left.
    repeat eexists; eauto.
destruct H0 as [HA Hact].
- exact HA.
destruct H0 as [_ Hact].
exact Hact.


  - (* Output / R2 *)
    right.
    right.
    repeat eexists; eauto.
all: unfold B_prefix_condition in H0.
all: destruct H0 as [HB Hact].
- exact HB.
- exact Hact.
Qed.

Lemma A_prefix_prepend_not_send :
  forall p xs q lbl sr T lbl' sr' U,
    A_prefix p xs ->
    prepend_pure xs (singleton_receive p lbl sr T) <>
    singleton_send q lbl' sr' U.
Proof.
  intros p xs.
  induction xs as [| a xs IH];
    intros q lbl sr T lbl' sr' U HA Heq.

  - (* Empty prefix *)
    cbn [prepend_pure] in Heq.
    unfold singleton_receive, singleton_send in Heq.
    discriminate Heq.

  - (* Nonempty prefix *)
    inversion HA as [| a' xs' Ha Htail]; subst.
    destruct a as [r l s | r l s].

    + (* Input prefix *)
      cbn [prepend_pure] in Heq.
      unfold singleton_receive, singleton_send in Heq.
      discriminate Heq.

    + (* Output prefix: forbidden by A_prefix *)
      simpl in Ha.
      contradiction.
Qed.

Lemma refinement_right_send_left_send :
  forall W1 p lbl sr W2,
    stc_pure_refinement
      W1
      (singleton_send p lbl sr W2) ->
    exists q l s T,
      W1 = singleton_send q l s T.
Proof.
  intros W1 p lbl sr W2 Href.

  unfold stc_pure_refinement in Href.
  punfold Href.

  destruct (refinementR_inv _ _ _ Href)
    as [[HT HU] | [Hin | Hout]].

  - (* End case: impossible *)
    subst W1.
    unfold singleton_send in HU.
    discriminate HU.

  - (* Input / R1 case *)
    destruct Hin as
      [q [l [s [s' [T [U [xs
        [HT [HU [Hsort [HA Hr]]]]]]]]]]].

    exfalso.

    apply
      (A_prefix_prepend_not_send
         q xs p l s' U lbl sr W2).

    + exact (proj1 HA).
symmetry.
exact HU.

  - (* Output / R2 case *)
    destruct Hout as
      [q [l [s [s' [T [U [xs
        [HT [HU [Hsort [HB Hr]]]]]]]]]]].

    exists q, l, s, T.
    exact HT.
Qed.

Lemma refinement_right_send_inv :
  forall W1 p lbl sr W2,
    stc_pure_refinement
      W1
      (singleton_send p lbl sr W2) ->

    exists q l s s' T U xs,

      W1 = singleton_send q l s T /\

      singleton_send p lbl sr W2 =
        prepend_pure xs
          (singleton_send q l s' U) /\

      subsort s s' /\

      B_prefix_condition q xs T U /\

      upaco2 stc_pure_refinementR bot2
        T (prepend_pure xs U).
Proof.
  intros W1 p lbl sr W2 Href.

  unfold stc_pure_refinement in Href.
  punfold Href.

  destruct (refinementR_inv _ _ _ Href)
    as [[HT HU] | [Hin | Hout]].

  - (* End: impossible *)
    unfold singleton_send in HU.
    discriminate HU.

  - (* Input: impossible *)
    destruct Hin as
      [q [l [s [s' [T [U [xs
        [HT [HU [Hsort [HA Hr]]]]]]]]]]].

    exfalso.

    eapply A_prefix_prepend_not_send.
    + exact (proj1 HA).
    + symmetry.
      exact HU.

  - (* Output *)
    destruct Hout as
      [q [l [s [s' [T [U [xs
        [HT [HU [Hsort [HB Hr]]]]]]]]]]].

    exists q, l, s, s', T, U, xs.

    split; try easy.
Qed.

Lemma prepend_pure_send_inv :
  forall xs T p lbl sr W,
    prepend_pure xs T = singleton_send p lbl sr W ->
    (xs = [] /\ T = singleton_send p lbl sr W) \/
    (exists xs',
       xs = pure_output p lbl sr :: xs' /\
       W = prepend_pure xs' T).
Proof.
  intros xs T p lbl sr W H.
  destruct xs as [| a xs'].

  - left.
    split.
    + reflexivity.
    + exact H.

  - right.
    destruct a as [q l s | q l s].

    + (* Input cannot produce a send root. *)
      cbn [prepend_pure] in H.
      unfold singleton_receive, singleton_send in H.
      discriminate H.

    + (* Output prefix *)
      cbn [prepend_pure] in H.

      assert (Hq : q = p).
      {
        unfold singleton_send in H.
        inversion H.
        reflexivity.
      }

      subst q.
unfold singleton_send in H.
inversion H; subst.

apply Eqdep.EqdepTheory.inj_pair2 in H3.

exists xs'.
split.
- reflexivity.
- pose proof
    (f_equal (fun f => f Fin.F1) H3)
    as Hcont.
  cbn in Hcont.
  symmetry.
  exact Hcont.
Qed.

Lemma refinement_right_send_cases :
  forall W1 p lbl sr W2,
    stc_pure_refinement
      W1
      (singleton_send p lbl sr W2) ->

    (exists s T,
       W1 = singleton_send p lbl s T /\
       subsort s sr /\
       upaco2 stc_pure_refinementR bot2 T W2)

    \/

    (exists q l s s' T U xs,
       q <> p /\
       W1 = singleton_send q l s T /\
       W2 =
         prepend_pure xs
           (singleton_send q l s' U) /\
       subsort s s' /\
       B_prefix_condition q
         (pure_output p lbl sr :: xs) T U /\
       upaco2 stc_pure_refinementR bot2
         T
         (prepend_pure
           (pure_output p lbl sr :: xs) U)).
Proof.
  intros W1 p lbl sr W2 Href.

  destruct
    (refinement_right_send_inv
       W1 p lbl sr W2 Href)
    as [q [l [s [s' [T [U [xs
      [HT [HU [Hsort [HB Hr]]]]]]]]]]].

destruct
  (prepend_pure_send_inv
     xs (singleton_send q l s' U)
     p lbl sr W2 (eq_sym HU))
  as [[Hnil Hdirect] | [xs' [Hxs HW2]]].

  - (* Direct matching *)
    subst xs.
    cbn [prepend_pure] in *.

    unfold singleton_send in Hdirect.
    inversion Hdirect; subst.

    (* Extract continuation equality if needed. *)
    left.
    exists s, T.
    repeat split; try assumption.
apply Eqdep.EqdepTheory.inj_pair2 in H3.

pose proof
  (f_equal (fun f => f Fin.F1) H3)
  as Hcont.

cbn in Hcont. subst. easy. 

  - (* R2 anticipation *)
    subst xs.

    destruct HB as [HBprefix HBact].

    inversion HBprefix as
      [| a rest Hallowed Htail];
      subst.

    cbn [allowed_B] in Hallowed.

    right.
    exists q, l, s, s', T, U, xs'.

    repeat split; try assumption.
    easy.
Qed.

Definition refinement_send_residual
  (U1 : stc_pure)
  (p lbl : string)
  (sr : sort)
  (W : stc_pure) : Prop :=
  exists W1,
    stc_pure_to_si U1 W1 /\
    stc_pure_refinement
      W1
      (singleton_send p lbl sr W).

Lemma refinement_send_residual_equiv :
  forall U1 p lbl sr W,
    send_residual_exists
      (refinement_preimage U1)
      p lbl sr W
    <->
    refinement_send_residual U1 p lbl sr W.
Proof.
  intros U1 p lbl sr W.
  split.

  - (* Forward *)
    intros Hres.

    unfold send_residual_exists in Hres.

    destruct Hres as
      [sh [next [i
        [Hlen [Hkey [Hnext HY]]]]]].

    unfold refinement_preimage in HY.

    destruct HY as [W1 [Hsi Href]].

    assert (Hcanonical :
      stc_pure_send p sh next =
      singleton_send p lbl sr W).
    {
      rewrite
        (singleton_send_canonical
           p sh next i lbl sr Hlen Hkey).

      rewrite Hnext.
      reflexivity.
    }

    unfold refinement_send_residual.

    exists W1.
    split.
    + exact Hsi.
    + rewrite <- Hcanonical.
      exact Href.

  - (* Reverse *)
    intros Hres.

    unfold refinement_send_residual in Hres.

    destruct Hres as [W1 [Hsi Href]].

    unfold send_residual_exists.

    exists {| branch_labels := [(lbl, sr)] |}.

    exists
      (fun _ : branch_pos
        {| branch_labels := [(lbl, sr)] |} => W).

    exists Fin.F1.

    repeat split.

    + unfold refinement_preimage.
      exists W1.
      split.
      * exact Hsi.
      * exact Href.
Qed.

Definition refinement_send_direct_residual
  (U1 : stc_pure)
  (p lbl : string)
  (sr : sort)
  (W : stc_pure) : Prop :=
  exists s T,
    subsort s sr /\
    stc_pure_to_si U1
      (singleton_send p lbl s T) /\
    stc_pure_refinement T W.

Lemma refinement_send_direct_residual_sound :
  forall U1 p lbl sr W,
    refinement_send_direct_residual U1 p lbl sr W ->
    refinement_send_residual U1 p lbl sr W.
Proof.
  intros U1 p lbl sr W H.

  unfold refinement_send_direct_residual in H.
  destruct H as [s [T [Hsort [Hsi Href]]]].

  unfold refinement_send_residual.

  exists (singleton_send p lbl s T).
  split.
  - exact Hsi.

  - unfold stc_pure_refinement in *.

    pfold.

    eapply pure_ref_output
      with (xs := []).

    + exact Hsort.

    + unfold B_prefix_condition, B_prefix.
      split.
      * constructor.
      * left.
        reflexivity.

    + left.
      exact Href.
Qed.

Definition refinement_send_anticipation_residual
  (U1 : stc_pure)
  (p lbl : string)
  (sr : sort)
  (W : stc_pure) : Prop :=
  exists q l s s' T U xs,

    q <> p /\

    stc_pure_to_si U1
      (singleton_send q l s T) /\

    W =
      prepend_pure xs
        (singleton_send q l s' U) /\

    subsort s s' /\

    B_prefix_condition q
      (pure_output p lbl sr :: xs) T U /\

    stc_pure_refinement
      T
      (prepend_pure
        (pure_output p lbl sr :: xs) U).

Lemma refinement_send_residual_cases :
  forall U1 p lbl sr W,
    refinement_send_residual U1 p lbl sr W ->
    refinement_send_direct_residual U1 p lbl sr W \/
    refinement_send_anticipation_residual U1 p lbl sr W.
Proof.
  intros U1 p lbl sr W Hres.

  unfold refinement_send_residual in Hres.
  destruct Hres as [W1 [Hsi Href]].

  destruct
    (refinement_right_send_cases
       W1 p lbl sr W Href)
    as [Hdirect | Hanticipation].

  - (* Direct matching *)
    destruct Hdirect as
      [s [T [HW1 [Hsort Hr]]]].

    left.
    unfold refinement_send_direct_residual.

    exists s, T.
    split. easy.
    + split. rewrite <- HW1.
      exact Hsi.
    + destruct Hr as [Hr | Hbot].
      * exact Hr.
      * contradiction.

  - (* R2 anticipation *)
    destruct Hanticipation as
      [q [l [s [s' [T [U [xs
        [Hneq [HW1 [HW [Hsort [HB Hr]]]]]]]]]]]].

    right.
    unfold refinement_send_anticipation_residual.

    exists q, l, s, s', T, U, xs.

    split. easy.
    + split. rewrite <- HW1.
      exact Hsi.
    + split. exact HW.
    + split. exact Hsort.
    + split. exact HB.
    + destruct Hr as [Hr | Hbot].
      * exact Hr.
      * contradiction.
Qed.

Inductive finite_pure : stc_pure -> Prop :=
| finite_pure_end :
    finite_pure stc_pure_end

| finite_pure_send :
    forall p sh next,
      (forall i : branch_pos sh,
         finite_pure (next i)) ->
      finite_pure (stc_pure_send p sh next)

| finite_pure_receive :
    forall p sh next,
      (forall i : branch_pos sh,
         finite_pure (next i)) ->
      finite_pure (stc_pure_receive p sh next).

Lemma stc_pure_refinement_trans :
  forall T U V : stc_pure,
    stc_pure_refinement T U ->
    stc_pure_refinement U V ->
    stc_pure_refinement T V.
Admitted.

Theorem subtype_pure_trans_closed :
  forall T1 T2 T3,
    nonempty_pure T2 ->
    (forall U1,
       stc_pure_to_so T1 U1 ->
       prefix_closed (refinement_preimage U1)) ->
    subtype_pure T1 T2 ->
    subtype_pure T2 T3 ->
    subtype_pure T1 T3.
Proof.
  intros T1 T2 T3 Hnonempty Hclosed H12 H23.

  unfold subtype_pure.
  intros U1 V3 Hso1 Hsi3.

  assert (HY :
    forall V2,
      stc_pure_to_si T2 V2 ->
      exists W2,
        stc_pure_to_so V2 W2 /\
        refinement_preimage U1 W2).
  {
    intros V2 Hsi2.

    destruct (H12 U1 V2 Hso1 Hsi2)
      as [W1 [W2 [Hsi1 [Hso2 Href12]]]].

    exists W2.
    split.
    - exact Hso2.
    - exists W1.
      split; assumption.
  }

  destruct
    (decomposition_uniformisation_closed
       T2
       (refinement_preimage U1)
       Hnonempty
       (Hclosed U1 Hso1)
       HY)
    as [U2 [Hso2 Hunif]].

  destruct (H23 U2 V3 Hso2 Hsi3)
    as [W2 [W3 [Hsi2 [Hso3 Href23]]]].

  destruct (Hunif W2 Hsi2)
    as [W1 [Hsi1 Href12]].

  exists W1, W3.

  split.
  - exact Hsi1.
  - split. exact Hso3.
  - eapply stc_pure_refinement_trans.
    + exact Href12.
    + exact Href23.
Qed.

Definition finitely_compatible_with
  (Y : stc_pure -> Prop)
  (W : stc_pure) : Prop :=
  forall n,
    exists W',
      Y W' /\
      stc_pure_eq_depth n W W'.

Definition observationally_complete
  (Y : stc_pure -> Prop) : Prop :=
  forall W,
    finitely_compatible_with Y W ->
    Y W.

Lemma prefix_closed_iff_observationally_complete :
  forall Y,
    prefix_closed Y <->
    observationally_complete Y.
Proof.
  intro Y.
  unfold prefix_closed,
         observationally_complete,
         finitely_compatible_with.
  tauto.
Qed.

Definition observational_closure
  (Y : stc_pure -> Prop)
  (W : stc_pure) : Prop :=
  forall n,
    exists Wn,
      Y Wn /\
      stc_pure_eq_depth n W Wn.

Lemma stc_pure_eq_depth_refl :
  forall n (T : stc_pure),
    stc_pure_eq_depth n T T.
Proof.
  induction n as [| n IH].
  - intros T.
    simpl.
    easy.

  - intros T.
    destruct T as
      [| p sh next
       | p sh next];
      simpl.

    + (* End *)
      easy.

    + (* Send *)
      split.
      * reflexivity.
      * exists eq_refl.
        intro i.
        simpl.
        apply IH.

    + (* Receive *)
      split.
      * reflexivity.
      * exists eq_refl.
        intro i.
        simpl.
        apply IH.
Qed.

Lemma prefix_closed_iff_observational_fixed_point :
  forall Y,
    prefix_closed Y <->
    forall W,
      Y W <-> observational_closure Y W.
Proof.
  intros Y.
  split.

  - intros Hclosed W.
    split.

    + intros HY n.
      exists W.
      split.
      * exact HY.
      * apply stc_pure_eq_depth_refl.

    + apply Hclosed.

  - intros Hfixed W Happrox.
    apply (proj2 (Hfixed W)).
    exact Happrox.
Qed.

Definition finitely_separated
  (Y : stc_pure -> Prop) : Prop :=
  forall W,
    ~ Y W ->
    exists n,
      forall W',
        Y W' ->
        ~ stc_pure_eq_depth n W W'.

From Coq Require Import Logic.Classical.

From Coq Require Import Logic.Classical.

Lemma prefix_closed_iff_finitely_separated :
  forall Y,
    prefix_closed Y <-> finitely_separated Y.
Proof.
  intro Y.
  unfold prefix_closed, finitely_separated.
  split.

  - (* Prefix closed -> finite separation *)
    intros Hclosed W Hnot.

    assert (Hnoapprox :
      ~ (forall n,
          exists W',
            Y W' /\
            stc_pure_eq_depth n W W')).
    {
      intro Happrox.
      apply Hnot.
      apply Hclosed.
      exact Happrox.
    }

    apply not_all_ex_not in Hnoapprox.

    destruct Hnoapprox as [n Hn].

    exists n.
    intros W' HY Heq.

    apply Hn.
    exists W'.
    split; assumption.

  - (* Finite separation -> prefix closed *)
    intros Hsep W Happrox.

    apply NNPP.
    intro Hnot.

    destruct (Hsep W Hnot) as [n Hn].

    destruct (Happrox n) as [Wn [HY Heq]].

    exact (Hn Wn HY Heq).
Qed.

Theorem subtype_pure_trans_finitely_separated :
  forall T1 T2 T3,
    nonempty_pure T2 ->

    (forall U1,
       stc_pure_to_so T1 U1 ->
       finitely_separated (refinement_preimage U1)) ->

    subtype_pure T1 T2 ->
    subtype_pure T2 T3 ->
    subtype_pure T1 T3.
Proof.
  intros T1 T2 T3 Hnonempty Hsep H12 H23.

  eapply subtype_pure_trans_closed.
  - exact Hnonempty.
  - intros U1 Hso.
    apply (proj2
      (prefix_closed_iff_finitely_separated
         (refinement_preimage U1))).
    apply Hsep.
    exact Hso.
  - exact H12.
  - exact H23.
Qed.

(***)

Inductive branch_uniformisation
  (R : stc_pure -> (stc_pure -> Prop) -> stc_pure -> Prop)
  (p : string)
  (sh : branch_shape)
  (next children : branch_pos sh -> stc_pure)
  (Y : stc_pure -> Prop) : Prop :=
| branch_uniformisation_intro :
    (forall i,
       let '(lbl, sr) := fin_nth (branch_labels sh) i in
       R (next i)
         (receive_residual_exists Y p lbl sr)
         (children i)) ->
    branch_uniformisation R p sh next children Y.

Inductive uniformises_step
  (r : stc_pure ->
       (stc_pure -> Prop) ->
       stc_pure -> Prop)
  : stc_pure ->
    (stc_pure -> Prop) ->
    stc_pure -> Prop :=

| uniformises_step_end :
    forall Y,
      Y stc_pure_end ->
      uniformises_step r
        stc_pure_end Y stc_pure_end

| uniformises_step_send :
    forall p sh next Y
           (i : branch_pos sh)
           lbl sr U,

      fin_nth (branch_labels sh) i = (lbl, sr) ->

      r
        (next i)
        (send_residual_exists Y p lbl sr)
        U ->

      uniformises_step r
        (stc_pure_send p sh next)
        Y
        (singleton_send p lbl sr U)

| uniformises_step_receive :
    forall p sh next Y
           (children : branch_pos sh -> stc_pure),

      (forall i : branch_pos sh,
         let '(lbl, sr) := fin_nth (branch_labels sh) i in
         r
           (next i)
           (receive_residual_exists Y p lbl sr)
           (children i)) ->

      uniformises_step r
        (stc_pure_receive p sh next)
        Y
        (stc_pure_receive p sh children).

Definition uniformises :=
  paco3 uniformises_step bot3.

Lemma uniformises_step_mon :
  monotone3 uniformises_step.
Proof.
  unfold monotone3.
  intros T Y U r r' LE H.
  destruct LE.

  - (* End *)
    constructor.
    assumption.

  - (* Send *)
    eapply uniformises_step_send.
    + eassumption.
    + apply H.
      eassumption.

  - (* Receive *)
    eapply uniformises_step_receive.
    intro i.
destruct (fin_nth (branch_labels sh) i)
  as [lbl sr] eqn:Hkey.

specialize (H0 i).
rewrite Hkey in H0.
simpl in H0.

apply H.
exact H0.
Qed.


Definition infinite_receive_uniform_rel
  : stc_pure ->
    (stc_pure -> Prop) ->
    stc_pure ->
    Prop :=
  fun T Y U =>
    exists q lbl sr,
      T = repeat_receive_pure q lbl sr /\
      U = repeat_receive_pure q lbl sr.


Lemma infinite_receive_uniform_rel_step :
  forall T Y U,
    infinite_receive_uniform_rel T Y U ->
    uniformises_step
      (upaco3 uniformises_step infinite_receive_uniform_rel)
      T Y U.
Proof.
  intros T Y U Hrel.

  destruct Hrel as
    [q [lbl [sr [HT HU]]]].

  subst T U.

  rewrite repeat_receive_pure_unfold.
  unfold singleton_receive.

  eapply uniformises_step_receive.

  intro i.

  destruct (fin_nth
    (branch_labels {| branch_labels := [(lbl, sr)] |}) i)
    as [lbl' sr'] eqn:Hkey.

  right.

  exists q, lbl, sr.
  split; reflexivity.
Qed.

Lemma uniformises_empty_infinite_receive :
  forall q lbl sr,
    uniformises
      (repeat_receive_pure q lbl sr)
      (fun _ => False)
      (repeat_receive_pure q lbl sr).
Proof.
  intros q lbl sr.

  unfold uniformises.

  eapply paco3_acc
    with (l := infinite_receive_uniform_rel)
         (r := bot3).

  - intros rr INCr INCl T Y U Hrel.

    pfold.

    eapply uniformises_step_mon.

    + apply infinite_receive_uniform_rel_step.
      exact Hrel.

    + intros T' Y' U' Hstep.

      destruct Hstep as [Hpaco | Hinv].

      * left.
        eapply paco3_mon.
        -- exact Hpaco.
        -- intros a b c Hab.
           apply INCl.
           exact Hab.

      * right.
        apply INCl.
        exact Hinv.

  - exists q, lbl, sr.
    split; reflexivity.
Qed.

Lemma uniformises_Y_correct_false :
  forall (q lbl : string) (sr : sort),
    ~ (forall T Y U,
         uniformises T Y U ->
         forall W,
           stc_pure_to_si U W ->
           Y W).
Proof.
  intros q lbl sr Hsound.

  pose proof
    (uniformises_empty_infinite_receive q lbl sr)
    as Huni.

  pose proof
    (repeat_receive_pure_si_self q lbl sr)
    as Hsi.

  exact
    (Hsound
       (repeat_receive_pure q lbl sr)
       (fun _ => False)
       (repeat_receive_pure q lbl sr)
       Huni
       (repeat_receive_pure q lbl sr)
       Hsi).
Qed.

Definition SO_wins
  (T : stc_pure)
  (Y : stc_pure -> Prop) : Prop :=
  exists U,
    stc_pure_to_so T U /\
    forall W,
      stc_pure_to_si U W ->
      Y W.

Definition SI_wins
  (T : stc_pure)
  (Y : stc_pure -> Prop) : Prop :=
  exists V,
    stc_pure_to_si T V /\
    forall W,
      stc_pure_to_so V W ->
      ~ Y W.

Definition decomposition_determined
  (T : stc_pure)
  (Y : stc_pure -> Prop) : Prop :=
  SO_wins T Y \/ SI_wins T Y.

Theorem decomposition_uniformisation_determined :
  forall (T : stc_pure)
         (Y : stc_pure -> Prop),

    decomposition_determined T Y ->

    (forall V,
       stc_pure_to_si T V ->
       exists W,
         stc_pure_to_so V W /\
         Y W) ->

    exists U,
      stc_pure_to_so T U /\
      forall W,
        stc_pure_to_si U W ->
        Y W.
Proof.
  intros T Y Hdet HY.

  unfold decomposition_determined in Hdet.
  destruct Hdet as [HSO | HSI].

  - (* SO has a winning strategy *)
    exact HSO.

  - (* SI has a winning strategy: contradiction *)
    destruct HSI as [V [Hsi Hbad]].

    destruct (HY V Hsi) as [W [Hso HYw]].

    exfalso.
    apply (Hbad W Hso).
    exact HYw.
Qed.

From Coq Require Import Logic.Classical.

Lemma no_SO_win_iff :
  forall T Y,
    ~ SO_wins T Y <->
    (forall U,
       stc_pure_to_so T U ->
       exists W,
         stc_pure_to_si U W /\
         ~ Y W).
Proof.
  intros T Y.
  unfold SO_wins.
  split.

  - intros Hnot U Hso.

    apply NNPP.
    intro Hnone.

    apply Hnot.
    exists U.
    split.
    + exact Hso.
    + intros W Hsi.
      apply NNPP.
      intro Hbad.
      apply Hnone.
      exists W.
      split; assumption.

  - intros Hfail [U [Hso Hall]].

    destruct (Hfail U Hso)
      as [W [Hsi Hnot]].

    apply Hnot.
    apply Hall.
    exact Hsi.
Qed.

Definition finitely_decidable_property
  (Y : stc_pure -> Prop) : Prop :=
  forall W,
    exists n,
      forall W',
        stc_pure_eq_depth n W W' ->
        (Y W <-> Y W').

Lemma finitely_decidable_prefix_closed :
  forall Y,
    finitely_decidable_property Y ->
    prefix_closed Y.
Proof.
  intros Y Hdec W Happrox.

  destruct (Hdec W) as [n Hn].
  destruct (Happrox n) as [Wn [HY Heq]].

  apply (proj2 (Hn Wn Heq)).
  exact HY.
Qed.

From Coq Require Import Logic.Classical.

Lemma decomposition_determined_finitely_decidable :
  forall T Y,
    nonempty_pure T ->
    finitely_decidable_property Y ->
    decomposition_determined T Y.
Proof.
  intros T Y Hnonempty Hdec.

  unfold decomposition_determined.

  destruct
    (classic
       (forall V,
          stc_pure_to_si T V ->
          exists W,
            stc_pure_to_so V W /\ Y W))
    as [HY | HnotHY].

  - (* SO wins *)
    left.
    unfold SO_wins.

    eapply decomposition_uniformisation_closed.
    + exact Hnonempty.
    + apply finitely_decidable_prefix_closed.
      exact Hdec.
    + exact HY.

- (* SI wins *)
  right.
  unfold SI_wins.

  apply not_all_ex_not in HnotHY.
  destruct HnotHY as [V HV].

  assert (Hsi : stc_pure_to_si T V).
  {
    apply NNPP.
    intro HnotSI.
    apply HV.
    intro H.
    contradiction.
  }

  exists V.
  split.
  + exact Hsi.
  + intros W Hso HYw.
    apply HV.
    intro.
    exists W.
    split; assumption.
Qed.

Lemma refinement_uniformisation_determined :
  forall T U1,
    nonempty_pure T ->
    decomposition_determined
      T (refinement_preimage U1) ->
    (forall V,
       stc_pure_to_si T V ->
       exists W,
         stc_pure_to_so V W /\
         refinement_preimage U1 W) ->
    exists U,
      stc_pure_to_so T U /\
      forall W,
        stc_pure_to_si U W ->
        refinement_preimage U1 W.
Proof.
  intros T U1 Hnonempty Hdet HY.

  eapply decomposition_uniformisation_determined.
  - exact Hdet.
  - exact HY.
Qed.

Theorem subtype_pure_trans_determined :
  forall T1 T2 T3,
    nonempty_pure T2 ->

    (forall U1,
       stc_pure_to_so T1 U1 ->
       decomposition_determined
         T2 (refinement_preimage U1)) ->

    subtype_pure T1 T2 ->
    subtype_pure T2 T3 ->
    subtype_pure T1 T3.
Proof.
  intros T1 T2 T3 Hnonempty Hdet H12 H23.

  unfold subtype_pure.
  intros U1 V3 Hso1 Hsi3.

  assert (HY :
    forall V2,
      stc_pure_to_si T2 V2 ->
      exists W2,
        stc_pure_to_so V2 W2 /\
        refinement_preimage U1 W2).
  {
    intros V2 Hsi2.

    destruct (H12 U1 V2 Hso1 Hsi2)
      as [W1 [W2 [Hsi1 [Hso2 Href12]]]].

    exists W2.
    split.
    - exact Hso2.
    - exists W1.
      split; assumption.
  }

  destruct
    (refinement_uniformisation_determined
       T2 U1
       Hnonempty
       (Hdet U1 Hso1)
       HY)
    as [U2 [Hso2 Hunif]].

  destruct (H23 U2 V3 Hso2 Hsi3)
    as [W2 [W3 [Hsi2 [Hso3 Href23]]]].

  destruct (Hunif W2 Hsi2)
    as [W1 [Hsi1 Href12]].

  exists W1, W3.
  split.
  - exact Hsi1.
  - split. exact Hso3.
  - eapply stc_pure_refinement_trans.
    + exact Href12.
    + exact Href23.
Qed.

Lemma uniformisation_send_choice_with_witness :
  forall p sh next Y,
    nonempty_pure (stc_pure_send p sh next) ->
    (forall V,
       stc_pure_to_si
         (stc_pure_send p sh next) V ->
       exists W,
         stc_pure_to_so V W /\
         Y W) ->
    exists i,
      let '(lbl, sr) :=
        fin_nth (branch_labels sh) i in
      forall V,
        stc_pure_to_si (next i) V ->
        exists W Wparent,
          stc_pure_to_so V W /\
          Y Wparent /\
          (exists sh' next' (j : branch_pos sh'),
             length (branch_labels sh') = 1 /\
             fin_nth (branch_labels sh') j = (lbl, sr) /\
             next' j = W /\
             Wparent = stc_pure_send p sh' next').
Proof.
  intros p sh next Y Hnonempty HY.

  destruct
    (uniformisation_send_choice_exists
       p sh next Y Hnonempty HY)
    as [i Hi].

  exists i.

  destruct (fin_nth (branch_labels sh) i)
    as [lbl sr] eqn:Hkey.

  intros V Hsi.

  destruct (Hi V Hsi)
    as [W [Hso Hres]].

  destruct Hres as
    [sh' [next' [j
      [Hlen [Hkey' [Hnext HYparent]]]]]].

  exists W, (stc_pure_send p sh' next').

  split.
  - exact Hso.
  - split.
    + exact HYparent.
    + exists sh', next', j.
      repeat split; assumption.
Qed.

Lemma send_residual_exists_two_steps :
  forall Y p lp sp q lq sq W,
    send_residual_exists
      (send_residual_exists Y p lp sp)
      q lq sq W ->
    exists Wmid Wroot,
      send_residual_exists Y p lp sp Wmid /\
      Y Wroot /\
      (exists sh2 next2 (j2 : branch_pos sh2),
         length (branch_labels sh2) = 1 /\
         fin_nth (branch_labels sh2) j2 = (lq, sq) /\
         next2 j2 = W /\
         Wmid = stc_pure_send q sh2 next2) /\
      (exists sh1 next1 (j1 : branch_pos sh1),
         length (branch_labels sh1) = 1 /\
         fin_nth (branch_labels sh1) j1 = (lp, sp) /\
         next1 j1 = Wmid /\
         Wroot = stc_pure_send p sh1 next1).
Proof.
  intros Y p lp sp q lq sq W Hres.

  unfold send_residual_exists in Hres.

  destruct Hres as
    [sh2 [next2 [j2
      [Hlen2 [Hkey2 [Hnext2 Hmid]]]]]].

  unfold send_residual_exists in Hmid.

  destruct Hmid as
    [sh1 [next1 [j1
      [Hlen1 [Hkey1 [Hnext1 Hroot]]]]]].

  exists (stc_pure_send q sh2 next2).
  exists (stc_pure_send p sh1 next1).

  repeat split.
  - exists sh1, next1, j1.
    repeat split; assumption.

  - exact Hroot.

  - exists sh2, next2, j2.
    repeat split; try easy.

  - exists sh1, next1, j1.
    repeat split; try assumption.

Qed.

CoFixpoint test_T
  (p : string) (sr : sort) : stc_pure :=
  stc_pure_send p
    {| branch_labels := [("a"%string, sr); ("b"%string, sr)] |}
    (fun _ => test_T p sr).

CoFixpoint test_A
  (p : string) (sr : sort) : stc_pure :=
  singleton_send p "a" sr (test_A p sr).

Fixpoint test_W
  (n : nat)
  (p : string)
  (sr : sort) : stc_pure :=
  match n with
  | 0 =>
      singleton_send p "b" sr (test_A p sr)
  | S k =>
      singleton_send p "a" sr (test_W k p sr)
  end.

Definition test_Y
  (p : string)
  (sr : sort)
  (W : stc_pure) : Prop :=
  exists n,
    W = test_W n p sr.

Lemma test_W_in_Y :
  forall n p sr,
    test_Y p sr (test_W n p sr).
Proof.
  intros n p sr.
  exists n.
  reflexivity.
Qed.

Lemma test_A_differs_from_W :
  forall n p sr,
    ~ stc_pure_eq_depth (S n)
        (test_A p sr)
        (test_W n p sr).
Proof.
  induction n as [| n IH]; intros p sr Hdepth.

- (* Base case: a versus b *)
  simpl in Hdepth.
  destruct Hdepth as [_ Hbranches].
  destruct Hbranches as [Hlen Hlabels].
  discriminate Hlen.
  - (* Step: both begin with a *)
    simpl in Hdepth.
    destruct Hdepth as [_ Hchildren].
    destruct Hchildren as [Hlen Hnext].

    specialize (Hnext Fin.F1).
    simpl in Hnext.

    apply (IH p sr).
    exact Hnext.
Qed.

Lemma test_A_not_in_Y :
  forall p sr,
    ~ test_Y p sr (test_A p sr).
Proof.
  intros p sr [n Heq].
  apply (test_A_differs_from_W n p sr).
  rewrite <- Heq.
  apply stc_pure_eq_depth_refl.
Qed.

Lemma test_A_approximated :
  forall n p sr,
    stc_pure_eq_depth n
      (test_A p sr)
      (test_W n p sr).
Proof.
  induction n as [| n IH]; intros p sr.

  - (* Depth 0 *)
    simpl.
    easy.

  - (* Depth S n: both begin with output "a" *)
    simpl.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * intro i.
        apply IH.
Qed.

Lemma test_Y_not_prefix_closed :
  forall p sr,
    ~ prefix_closed (test_Y p sr).
Proof.
  intros p sr Hclosed.

  apply (test_A_not_in_Y p sr).

  apply Hclosed.
  intro n.

  exists (test_W n p sr).
  split.
  - apply test_W_in_Y.
  - apply test_A_approximated.
Qed.

Lemma test_Y_send_residual_a :
  forall n p sr,
    send_residual_exists
      (test_Y p sr)
      p "a" sr
      (test_W n p sr).
Proof.
  intros n p sr.

  unfold send_residual_exists.

  exists {| branch_labels := [("a"%string, sr)] |}.
  exists (fun _ => test_W n p sr).
  exists Fin.F1.

  split.
  - reflexivity.
  - split. reflexivity.
  - split. reflexivity.
  - unfold test_Y.
    exists (S n).
    reflexivity.
Qed.















