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

Inductive subtype: st -> st -> Prop :=
  | stc: forall T T', (forall U, st2soC U T -> forall V', st2siC V' T' -> (exists W W', st2sisoC (@und W) U -> st2sisoC (@und W') V' -> (@und W) ~< (@und W'))) ->
                      subtype T T'.

Definition subltype (T T': local) := subtype (lt2st T) (lt2st T').


