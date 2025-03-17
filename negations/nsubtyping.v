Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts 
               ST.subtyping.subtyping ST.negations.nrefinement.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Definition nsubtype (T T': st): Prop :=
  exists U,  (st2soC T U) ->
  exists V', (st2siC T' V') ->
  forall W,  (st2sisoC U (@und W)) ->
  forall W', (st2sisoC V' (@und W')) -> nRefinement W W'.

Lemma subNeqL: forall T T', (subtype T T' -> False) -> nsubtype T T'.
Proof. intros.
       unfold subtype, nsubtype in *.
       apply not_all_ex_not in H.
       destruct H as (U, H).
       exists U.
       intro Ha.
       apply not_and_or in H.
       destruct H as [H | H].
       easy.
       apply not_all_ex_not in H.
       destruct H as (V', H).
       exists V'. 
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hb.
       easy.
       intros Hb W.
       apply not_ex_all_not with (n := W) in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hc.
       easy.
       intros Hc W'.
       apply not_ex_all_not with (n := W') in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hd. easy.
       intro Hd.
       apply nRefL. easy.
Qed.

Lemma subNeqR: forall T T', nsubtype T T' -> (subtype T T' -> False).
Proof. intros.
       unfold subtype, nsubtype in *.
       rename H into Ha.
       rename H0 into H.
       rename Ha into H0.
       destruct H0 as (U, H0).
       specialize(H U).
       destruct H as (p, Ha).
       specialize(H0 p).
       destruct H0 as (V', H0).
       specialize(Ha V').
       destruct Ha as (q, Ha).
       specialize(H0 q).
       destruct Ha as (W, Ha).
       destruct Ha as (r, Ha).
       specialize(H0 W r).
       destruct Ha as (W', Ha).
       destruct Ha as (s, Ha).
       specialize(H0 W' s).
       apply (nRefR W W'); easy.
Qed.

