Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Definition act_eq (w w': st) := forall a, coseqIn a (act w) <-> coseqIn a (act w').

Definition act_neq (w w': st) := (exists a, coseqIn a (act w) /\ (coseqIn a (act w') -> False) \/ coseqIn a (act w') /\ (coseqIn a (act w) -> False)).

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | _sref_a  : forall w w' p l s s' a n,   subsort s' s ->
                                           seq w (merge_ap_contn p a w' n)  ->
                                           ( exists L,
                                             coseqInLC (act w) L /\
                                             coseqInLC (act (merge_ap_contn p a w' n)) L /\
                                             coseqInR L (act w) /\
                                             coseqInR L (act (merge_ap_contn p a w' n))
                                           ) ->
                                           refinementR seq (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | _sref_b  : forall w w' p l s s' b n,   subsort s s' ->
                                           seq w (merge_bp_contn p b w' n) ->
                                           ( exists L,
                                             coseqInLC (act w) L /\
                                             coseqInLC (act (merge_bp_contn p b w' n)) L /\
                                             coseqInR L (act w) /\
                                             coseqInR L (act (merge_bp_contn p b w' n))
                                           ) ->
                                           refinementR seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | _sref_end: refinementR seq st_end st_end.

Definition refinement: st -> st -> Prop := fun s1 s2 => paco2 refinementR bot2 s1 s2.

Notation "x '~<' y" := (refinement x y) (at level 50, left associativity).

Lemma refinementR_mon: monotone2 refinementR.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
(*     - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0. *)
       - specialize(_sref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.

(* coinductive extensionality axiom *)
Axiom mem_ext: forall w1 w2,
( exists L,
  coseqInLC (act w1) L /\
  coseqInLC (act w2) L /\
  coseqInR L (act w1) /\
  coseqInR L (act w2)
) <-> act_eq w1 w2.

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



