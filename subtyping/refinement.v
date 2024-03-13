Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

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

(* the second refinement *)

Inductive refinementR2 (seq: st -> st -> Prop): st -> st -> Prop :=
  | ref2_a  : forall w w' p l s s' a n, subsort s' s ->
                                        seq w (merge_ap_contn p a w' n)  ->
                                        act_eq w (merge_ap_contn p a w' n) ->
                                        refinementR2 seq (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | ref2_b  : forall w w' p l s s' b n, subsort s s' ->
                                        seq w (merge_bp_contn p b w' n) ->
                                        act_eq w (merge_bp_contn p b w' n) ->
                                        refinementR2 seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | ref2_end: refinementR2 seq st_end st_end.

Definition refinement2: st -> st -> Prop := fun s1 s2 => paco2 refinementR2 bot2 s1 s2.

Notation "x '~<' y" := (refinement2 x y) (at level 50, left associativity).

Lemma refinementR2_mon: monotone2 refinementR2.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - specialize(ref2_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(ref2_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.
