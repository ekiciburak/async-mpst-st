From ST Require Import stream st so si reordering siso refinement reorderingfacts subtyping nrefinement.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts.

Definition nsubtype (T T': st): Prop :=
  exists U,  st2soC T U /\
  exists V', st2siC T' V' /\
  forall W, st2sisoC U (@und W) /\ 
  forall W', st2sisoC V' (@und W') /\ nRefinementN W W'.

Lemma subneqL: forall T T', subtype T T' -> nsubtype T T' -> False.
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H0 as (U, (Ha, (V', (Hb, H0)))).
       specialize(H U).
       destruct H as (Ha1, H).
       destruct (H V') as (Hb1, (W, (Hc, (W', (Hd, He))))).
       specialize(H0 W).
       destruct H0 as (Hc1, H0).
       destruct (H0 W') as (Hd', He').
       apply refneqL in He. easy. easy.
Qed.
