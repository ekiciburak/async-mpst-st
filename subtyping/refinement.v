Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Definition act_eq (w w': st) := forall a, coseqIn a (act w) <-> coseqIn a (act w').

Definition act_neq (w w': st) := (exists a, coseqIn a (act w) /\ (coseqIn a (act w') -> False) \/ coseqIn a (act w') /\ (coseqIn a (act w) -> False)).

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | ref_a  : forall w w' p l s s' a n, subsort s' s ->
                                       seq w (merge_ap_contn p a w' n)  ->
                                       ( exists L1, exists L2,
                                         coseqInLC (act w) L1 /\
                                         coseqInLC (act (merge_ap_contn p a w' n)) L2 /\
                                         coseqInR L1 (act w) /\
                                         coseqInR L2 (act (merge_ap_contn p a w' n)) /\
                                         (forall x, List.In x L1 <-> List.In x L2)
                                        ) ->
                                       refinementR seq (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | ref_b  : forall w w' p l s s' b n, subsort s s' ->
                                       seq w (merge_bp_contn p b w' n) ->
                                       ( exists L1, exists L2,
                                         coseqInLC (act w) L1 /\
                                         coseqInLC (act (merge_bp_contn p b w' n)) L2 /\
                                         coseqInR L1 (act w) /\
                                         coseqInR L2 (act (merge_bp_contn p b w' n)) /\
                                         (forall x, List.In x L1 <-> List.In x L2)
                                       ) ->
                                       refinementR seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | ref_end: refinementR seq st_end st_end.

Definition refinement: st -> st -> Prop := fun s1 s2 => paco2 refinementR bot2 s1 s2.

Notation "x '~<' y" := (refinement x y) (at level 50, left associativity).

Lemma refinementR_mon: monotone2 refinementR.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
(*     - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0. *)
       - specialize(ref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(ref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.

Lemma coseqInRInv: forall l w, coseqInR l (act w) -> 
                              (l = [] \/ (forall x, List.In x l -> coseqIn x (act w))).
Proof. intros.
       induction H. left. easy.
       destruct IHcoseqInR. subst.
       right. intros a Ha.
       inversion Ha. subst. easy. easy.
       right. intros a Ha.
       inversion Ha. subst. easy.
       apply H1. easy.
Qed.

Lemma coseqInRInv2: forall l w,
  (l = [] \/ (forall x, List.In x l -> coseqIn x (act w))) -> coseqInR l (act w).
Proof. intros.
       destruct H. subst. constructor.
       induction l; intros.
       - constructor.
       - constructor. apply H. simpl. left. easy.
         apply IHl. intros. apply H.
         simpl. right. easy.
Qed.

Axiom ext0: forall w l, coseqInLC (act w) l -> coseqInLI (act w) l.

Lemma liftExt: forall w l, coseqInLI (act w) l -> (forall a, coseqIn a (act w) -> List.In a l).
Proof. intros.
       induction H.
       inversion H0. subst. easy. subst. easy.
       inversion H0. subst. simpl in H2. inversion H2. subst. easy.
       subst. simpl in H2. inversion H2. subst. apply IHcoseqInLI. easy.
Qed.

Lemma ext1: forall w l, coseqInLC (act w) l -> (forall a, coseqIn a (act w) -> List.In a l).
Proof. intros.
       apply liftExt with (w := w).
       apply ext0. easy. easy.
Qed.

Lemma coseqInLCInv: forall l w, coseqInLC (act w) l -> 
                                ((act w) = Delay conil \/ (forall x, coseqIn x (act w) -> List.In x l)).
Proof. intros.
       specialize(ext1 w l H); intro Hax.
       destruct (act w), force.
       - left. easy.
       - right. intros a Ha.
         punfold H.
         apply coseqInLC_mon.
Qed.

Lemma cind_ext: forall w1 w2,
( exists L1, exists L2,
  coseqInLC (act w1) L1 /\
  coseqInLC (act w2) L2 /\
  coseqInR L1 (act w1) /\
  coseqInR L2 (act w2) /\
  (forall x, List.In x L1 <-> List.In x L2)
) -> act_eq w1 w2.
Proof. intros w1 w2 (l1,(l2,(Ha,(Hb,(Hc,(Hd,He)))))).
       unfold act_eq. intro a.
       split. intro Hf.
       apply coseqInRInv in Hc, Hd.
       apply coseqInLCInv in Ha, Hb.
       destruct Ha as [Ha | Ha].
       rewrite Ha in Hf.
       inversion Hf. subst. easy. subst. easy.
       specialize(Ha a Hf).
       apply He in Ha.
       destruct Hd as [Hd | Hd]. subst. easy.
       apply Hd. easy.

       intro Hf.
       apply coseqInRInv in Hc, Hd.
       apply coseqInLCInv in Ha, Hb.
       destruct Hb as [Hb | Hb].
       rewrite Hb in Hf.
       inversion Hf. subst. easy. subst. easy.
       specialize(Hb a Hf).
       apply He in Hb.
       destruct Hc as [Hc | Hc]. subst. easy.
       apply Hc. easy.
Qed.

Axiom finiteST:
forall w1 w2,
act_eq w1 w2 ->
( exists L1, exists L2,
  coseqInLC (act w1) L1 /\
  coseqInLC (act w2) L2 /\
  coseqInR L1 (act w1) /\
  coseqInR L2 (act w2) /\
  (forall x, List.In x L1 <-> List.In x L2)
).

Lemma mem_ext: forall w1 w2,
( exists L1, exists L2,
  coseqInLC (act w1) L1 /\
  coseqInLC (act w2) L2 /\
  coseqInR L1 (act w1) /\
  coseqInR L2 (act w2) /\
  (forall x, List.In x L1 <-> List.In x L2)
) <-> act_eq w1 w2.
Proof. split.
       apply cind_ext.
       apply finiteST.
Qed.

Lemma act_eq_neq: forall w w', (act_eq w w' -> False) -> act_neq w w'.
Proof. intros.
       unfold act_eq, act_neq in *.
       apply not_all_ex_not in H.
       destruct H as (a, H).
       exists a.
       unfold iff in H.
       apply not_and_or in H.
       destruct H as [H | H].
       apply imply_to_and in H.
       left. easy.
       apply imply_to_and in H.
       right. easy.
Qed.

Lemma listEq: forall {A: Type} (l1 l2: list A), l1 = l2 -> (forall x, List.In x l1 <-> List.In x l2).
Proof. intros. subst. easy. Qed.

