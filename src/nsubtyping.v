Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.refinement ST.src.reorderingfacts ST.src.subtyping ST.src.nrefinement.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts.

Definition nsubtype (T T': st): Prop :=
  exists U,  (st2soC T U -> False) \/
  exists V', (st2siC T' V' -> False) \/
  forall W, (st2sisoC U (@und W) -> False) \/ 
  forall W', (st2sisoC V' (@und W') -> False) \/ nRefinementN W W'.