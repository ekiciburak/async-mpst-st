Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.subtyping.refinement ST.src.reorderingfacts.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts.

Definition subtype (T T': st): Prop :=
  forall U, st2soC T U /\ 
  forall V', st2siC T' V' /\
  exists (W: siso), st2sisoC U  (@und W) /\
  exists (W':siso), st2sisoC V' (@und W') /\ (@und W) ~< (@und W').

Definition subtypeA (T T': st): Prop :=
  exists (W: siso), st2sisoCA (@und W) T /\
  exists (W':siso), st2sisoCA (@und W') T' /\ (@und W) ~< (@und W').