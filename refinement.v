From ST Require Import stream st so si reordering siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.


Inductive cosetIncL (R: coseq (participant * string) -> list (participant * string) -> Prop):
                        coseq (participant * string) -> list (participant * string) -> Prop :=
  | c_nil : forall ys, cosetIncL R (Delay conil) ys
  | c_incl: forall x xs ys,
            List.In x ys ->
            R xs ys ->
            cosetIncL R (Delay (cocons x xs)) ys.

Definition cosetIncLC := fun s1 s2 => paco2 cosetIncL bot2 s1 s2.

Lemma cosetIncL_mon: monotone2 cosetIncL.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - specialize (c_incl r'); intro HS.
         apply HS.
         apply H.
         apply LE, H0.
Qed.

Inductive cosetIncR: list (participant * string) -> coseq (participant * string) -> Prop :=
  | l_nil : forall ys, cosetIncR nil ys
  | l_incl: forall x xs ys,
            CoInR x ys ->
            cosetIncR xs ys ->
            cosetIncR (x::xs) ys.

Definition act_eq (w w': st) := forall a, CoIn a (act w) <-> CoIn a (act w').
Definition act_eqA (w w': st) := forall a, CoInR a (act w) <-> CoInR a (act w').

Definition act_neq (w w': st) := (exists a, CoIn a (act w) -> CoNInR a (act w')) \/ (exists a, CoIn a (act w') -> CoNInR a (act w)).

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | _sref_in : forall w w' p l s s',
                      subsort s' s -> 
                      seq w w' ->
                      refinementR seq (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])

  | _sref_out: forall w w' p l s s',
                      subsort s s' ->
                      seq w w' ->
                      refinementR seq (st_send p [(l,s,w)]) (st_send p [(l,s',w')])

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
       - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0.
       - specialize(_sref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.
