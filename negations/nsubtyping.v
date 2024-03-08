Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.subtyping.refinement ST.src.reorderingfacts 
               ST.subtyping.subtyping ST.negations.nrefinement.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Definition nsubtype (T T': st): Prop :=
  forall W,  (st2sisoC (@und W) T) ->
  forall W', (st2sisoC (@und W') T') -> nRefinement W W'.