From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
From ST Require Import stream.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.

Notation label := string.
Notation participant := string.

Inductive sort: Type :=
  | sunit: sort
  | sbool: sort
  | sint : sort
  | snat : sort.

Inductive subsort: sort -> sort -> Prop :=
  | sni  : subsort snat sint
  | srefl: forall s, subsort s s.

Inductive nsubsort: sort -> sort -> Prop :=
  | nsin: nsubsort sint snat
  | nsbi: nsubsort sbool sint
  | nsib: nsubsort sint sbool
  | nsbn: nsubsort sbool snat
  | nsnb: nsubsort snat sbool
  | nsun: nsubsort sunit snat
  | nsnu: nsubsort snat sunit
  | nsbu: nsubsort sbool sunit
  | nsub: nsubsort sunit sbool.

Lemma ssnssL: forall s t, subsort s t -> (nsubsort s t -> False).
Proof. intro s.
       induction s; intros; case_eq t; intros; subst; try easy.
Qed.

Lemma ssnssR: forall s t, nsubsort s t -> (subsort s t -> False).
Proof. intro s.
       induction s; intros; case_eq t; intros; subst; try easy.
Qed.

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


