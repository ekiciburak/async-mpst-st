Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

Definition act_eq (w w': st) := forall a, CoInR a (act w) <-> CoInR a (act w').

Definition act_neq (w w': st) := (exists a, CoInR a (act w) /\ (CoInR a (act w') -> False) \/ CoInR a (act w') /\ (CoInR a (act w) -> False)).

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | _sref_a  : forall w w' p l s s' a n,
                      subsort s s' ->
                      seq w (merge_ap_contn p a w' n)  ->
                      act_eq w (merge_ap_contn p a w' n) ->
                      refinementR seq (st_receive p [(l,s',w)]) (merge_ap_contn p a (st_receive p [(l,s,w')]) n)

  | _sref_b  : forall w w' p l s s' b n,
                      subsort s s' ->
                      seq w (merge_bp_contn p b w' n) ->
                      act_eq w (merge_bp_contn p b w' n) ->
                      refinementR seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | _sref_end: refinementR seq st_end st_end.

Definition refinement: st -> st -> Prop := fun s1 s2 => paco2 refinementR bot2 s1 s2.

Notation "x '~<' y" := (refinement x y) (at level 50, left associativity).

Lemma refinementR_mon: monotone2 refinementR.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - specialize(_sref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.
