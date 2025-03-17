Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | ref_a  : forall w w' p l s s' a n, subsort s' s ->
                                       seq w (merge_ap_contn p a w' n)  ->
                                       act_eq w (merge_ap_contn p a w' n) ->
                                       refinementR seq (st_receive p (cocons (l,s,w) conil)) (merge_ap_contn p a (st_receive p (cocons (l,s',w') conil)) n)
  | ref_b  : forall w w' p l s s' b n, subsort s s' ->
                                       seq w (merge_bp_contn p b w' n) ->
                                       act_eq w (merge_bp_contn p b w' n) ->
                                       refinementR seq (st_send p (cocons (l,s,w) conil)) (merge_bp_contn p b (st_send p (cocons (l,s',w') conil)) n)
  | ref_end: refinementR seq st_end st_end.

Definition refinement: st -> st -> Prop := fun s1 s2 => paco2 refinementR bot2 s1 s2.

Notation "x '~<' y" := (refinement x y) (at level 50, left associativity).

Lemma refinementR_mon: monotone2 refinementR.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - specialize(ref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(ref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.

