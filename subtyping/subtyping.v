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
  exists (W: siso), st2sisoC (@und W) T /\
  exists (W':siso), st2sisoC (@und W') T' /\ refinement (@und W) (@und W').

Definition subtype2 (T T': st): Prop :=
  exists (W: siso), st2sisoC (@und W) T /\
  exists (W':siso), st2sisoC (@und W') T' /\ (@und W) ~< (@und W').