From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.
Require Import ST.processes.process ST.types.local ST.processes.unscoped.


(* session trees *)
CoInductive st: Type :=
  | st_end    : st
  | st_receive: participant -> list (label*sort*st) -> st
  | st_send   : participant -> list (label*sort*st) -> st.

Inductive st_equiv (R: st -> st -> Prop): st -> st -> Prop :=
  | eq_st_end: st_equiv R st_end st_end
  | eq_st_rcv: forall p l s xs ys,
                List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
                st_equiv R (st_receive p (zip (zip l s) xs)) (st_receive p (zip (zip l s) ys))
  | eq_st_snd: forall p l s xs ys,
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               st_equiv R (st_send p (zip (zip l s) xs)) (st_send p (zip (zip l s) ys)).

Definition st_equivC: st -> st -> Prop := fun s1 s2 => paco2 st_equiv bot2 s1 s2.

Notation "p '&' l" := (st_receive p l) (at level 50, left associativity).
Notation "p '!' l" := (st_send p l) (at level 50, left associativity).
Notation "'B'" :=  sbool (at level 50, left associativity).
Notation "'()'" :=  sunit (at level 50, left associativity).
Notation "'I'" :=  sint (at level 50, left associativity). 
Notation "'N'" :=  snat (at level 50, left associativity).
Notation "'end'" :=  st_end (at level 50, left associativity).

Definition st_id (s: st): st :=
  match s with
    | st_end         => st_end
    | st_receive p l => st_receive p l
    | st_send p l    => st_send p l
  end.

Lemma st_eq: forall s, s = st_id s.
Proof. intro s; destruct s; easy. Defined.

Inductive lt2st (R: local -> st -> Prop): local -> st -> Prop :=
  | lt2st_end: lt2st R lt_end st_end
  | lt2st_rcv: forall p l s xs ys,
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               lt2st R (lt_receive p (zip (zip l s) xs)) (st_receive p (zip (zip l s) ys))
  | lt2st_snd: forall p l s xs ys,
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               lt2st R (lt_send p (zip (zip l s) xs)) (st_send p (zip (zip l s) ys))
  | lt2st_mu : forall l t,
               lt2st R (l [lt_mu l .: lt_var]) t ->
               lt2st R (lt_mu l) t.

Definition lt2stC l t := paco2 lt2st bot2 l t.
