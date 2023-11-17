From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
From ST Require Import stream st.
Require Import String List.
Import ListNotations.
Local Open Scope string_scope.

From Paco Require Import paco.
Require Import Setoid.
Require Import Morphisms.

CoInductive so: Type :=
  | so_end    : so 
  | so_receive: participant -> list (label*sort*so) -> so 
  | so_send   : participant -> so -> so.

Inductive st2so (R: st -> st -> Prop): st -> st -> Prop :=
  | st2so_end: st2so R st_end st_end
  | st2so_snd: forall l s x t xs p,
               List.In (l,s,x) xs ->
               R (st_send p [(l,s,x)]) t ->
               st2so R (st_send p xs) t
  | st2so_rcv: forall p l s t xs ys,
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               R (st_receive p (zip (zip l s) ys)) t ->
               st2so R (st_receive p (zip (zip l s) xs)) t.

Definition st2soC s1 s2 := paco2 (st2so) bot2 s1 s2.

#[export]
Declare Instance Equivalence_st2so : Equivalence st2soC.