Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.
Require Import ProofIrrelevance.

Definition subtype (T T': st): Prop :=
  forall U, st2soC T U /\ 
  forall V', st2siC T' V' /\
  exists (W: siso), st2sisoC U  (@und W) /\
  exists (W':siso), st2sisoC V' (@und W') /\ (@und W) ~< (@und W').

Definition subltype (T T': local) := subtype (lt2st T) (lt2st T').


