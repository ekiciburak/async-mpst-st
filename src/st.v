From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.types.local.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.

(* session trees *)
CoInductive st: Type :=
  | st_end    : st
  | st_receive: participant -> coseq (label*sort*st) -> st
  | st_send   : participant -> coseq (label*sort*st) -> st.

Inductive st_equiv (R: st -> st -> Prop): st -> st -> Prop :=
  | eq_st_end: st_equiv R st_end st_end
  | eq_st_rcv: forall p l s xs ys,
(*                colen_eqC xs ys -> *)
               Forall2C (fun u v => R u v) xs ys ->
               st_equiv R (st_receive p (cozip (cozip l s) xs)) (st_receive p (cozip (cozip l s) ys))
  | eq_st_snd: forall p l s xs ys,
(*                colen_eqC xs ys -> *)
               Forall2C (fun u v => R u v) xs ys ->
               st_equiv R (st_send p (cozip (cozip l s) xs)) (st_send p (cozip (cozip l s) ys)).


(* Inductive st_equiv (R: st -> st -> Prop): st -> st -> Prop :=
  | eq_st_end: st_equiv R st_end st_end
  | eq_st_rcv: forall p f g,
               (forall l,
                match (f l, g l) with
                  | (Some (s1, t1), Some (s2, t2)) => s1 = s2 /\ R t1 t2
                  | (None, None)                   => True
                  | _                              => False
                end
               ) ->
               st_equiv R (st_receive p f) (st_receive p g)
  | eq_st_snd: forall p f g,
               (forall l, 
                match (f l, g l) with
                  | (Some (s1, t1), Some (s2, t2)) => s1 = s2 /\ R t1 t2
                  | (None, None)                   => True
                  | _                              => False
                end
               ) ->
               st_equiv R (st_send p f) (st_send p g). *)

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

Fixpoint lst2fun (l:list(label*sort*st)) (l':label): option(sort*st) :=
  match l with
    | (l1,s1,t1)::xs => if eqb l' l1 then Some (s1,t1) else lst2fun xs l'
    | nil            => None
  end.

Fixpoint retLoc (l:list(label*sort*local)) (l':label): option (sort*local) :=
  match l with
    | (l1,s1,lt1)::ys => if eqb l' l1 then Some(s1, lt1) else retLoc ys l'
    | nil             => None
  end.

Require Import ST.processes.unscoped.

Definition unf (l: local): local :=
  match l with
    | lt_mu l => subst_local ((lt_mu l) .: lt_var) l
    | _       => l
  end.

Fixpoint rec_depth G :=
  match G with
    | lt_mu G => S (rec_depth G)
    | _       => 0
  end.

Fixpoint n_unroll d G :=
  match d with
  | 0   => G
  | S d =>
    match G with
    | lt_mu G' => n_unroll d (unf G')
    | _        => G
    end
  end.

CoFixpoint lt2st (l: local): st :=
  match n_unroll (rec_depth l) l with
    | lt_receive p xs =>
      let cofix next xs :=
       match xs with
         | (l1,s1,t1)::ys => cocons (l1,s1,lt2st t1) (next ys)
         | nil            => conil
       end
      in st_receive p (next xs)
    | lt_send p xs    =>
      let cofix next xs :=
       match xs with
         | (l1,s1,t1)::ys => cocons (l1,s1,lt2st t1) (next ys)
         | nil            => conil
       end
      in st_send p (next xs)
    | _               => st_end
  end.

Lemma monH2: forall ys xs r r',
  Forall2C (fun u v : string * sort * st => exists (l : string) (s : sort) (t : st) (l' : string) (s' : sort) (t' : st), u = (l, s, t) /\ v = (l', s', t') /\ r t t') ys xs ->
  (forall x0 x1 : st, r x0 x1 -> r' x0 x1) ->
  Forall2C (fun u v : string * sort * st => exists (l : string) (s : sort) (t : st) (l' : string) (s' : sort) (t' : st), u = (l, s, t) /\ v = (l', s', t') /\ r' t t') ys xs.
Proof. intros. revert xs ys H. pcofix CIH.
       intros.
       pfold.
       pinversion H1. subst.
       constructor. subst.
       constructor.
       destruct H as (l1,(s1,(t1,(l1',(s1',(t1',(Ha,(Hb,Hc)))))))).
       exists l1. exists s1. exists t1. exists l1'. exists s1'. exists t1'.
       split. easy. split. easy. apply H0; easy. 
       right.
       apply CIH.
       easy. 
       unfold monotone2.
       intros.
       induction IN; intros.
       constructor.
       constructor. easy. apply LE. easy.
Qed.

(* CoFixpoint lt2st (l: local): st :=
  match n_unroll (rec_depth l) l with
    | lt_receive p xs =>
      st_receive p 
      (fun lb =>
       match retLoc xs lb with
         | Datatypes.Some (s1,lt1) => Datatypes.Some(s1, lt2st lt1)
         | Datatypes.None          => Datatypes.None
       end
      )
    | lt_send p xs =>
      st_send  p 
      (fun lb =>
       match retLoc xs lb with
         | Datatypes.Some (s1,lt1) => Datatypes.Some(s1, lt2st lt1)
         | Datatypes.None          => Datatypes.None
       end
      )
    | _               => st_end
  end. *)

(* Inductive lt2st (R: local -> st -> Prop): local -> st -> Prop :=
  | lt2st_end: lt2st R lt_end st_end
  | lt2st_rcv: forall p l s xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               lt2st R (lt_receive p (zip (zip l s) xs)) (st_receive p (zip (zip l s) ys))
  | lt2st_snd: forall p l s xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               lt2st R (lt_send p (zip (zip l s) xs)) (st_send p (zip (zip l s) ys))
  | lt2st_mu : forall l t,
               lt2st R (unfold_muL (lt_mu l)) t ->
               lt2st R (lt_mu l) t.

Definition lt2stC l t := paco2 lt2st bot2 l t.

Lemma lt2st_mon: monotone2 lt2st.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply lt2st_end.
       - specialize (lt2st_rcv r'); intro HS.
         apply HS with (l := l) (s := s). easy.
         apply Forall_forall.
         intros (lt,st) H1. simpl in H1. simpl.
         rewrite Forall_forall in H0. simpl in H0.
         specialize (H0 (lt,st)). simpl in H0.
         apply LE, H0. exact H1.
       - specialize (lt2st_snd r'); intro HS.
         apply HS with (l := l) (s := s). easy.
         apply Forall_forall.
         intros (lt,st) H1. simpl in H1. simpl.
         rewrite Forall_forall in H0. simpl in H0.
         specialize (H0 (lt,st)). simpl in H0.
         apply LE, H0. exact H1.
       - apply lt2st_mu. exact IHIN.
Qed.
 *)
(*
Check lt_send.
Check lt_var 0.

Let lr := lt_mu (lt_send "p" [("l",sint,(lt_var 0))] ).
Let lr2 := Eval simpl in unfold_muL lr.
Eval simpl in unfold_muL lr2.
Print lr.
Print lr2.  *)

Definition sfun (l: label) (s: sort) (x: st): (label -> option(sort*st)) :=
  fun l' => if eqb l l' then Datatypes.Some(s,x) else Datatypes.None. 
  
Definition sort_eqb (s1 s2: local.sort): bool :=
  match (s1,s2) with
    | (sunit, sunit) => true
    | (sbool, sbool) => true
    | (sint, sint)   => true
    | (snat, snat)   => true
    | _              => false
  end.

Fixpoint pathsel (u: label) (v: local.sort) (l: list (label*local.sort*st)): st :=
  match l with
    | (lbl,s,x)::xs => if andb (eqb u lbl) (sort_eqb v s) then x else pathsel u v xs
    | nil           => st_end
  end.

Inductive copathsel: label -> sort -> coseq(label*sort*st) -> st -> Prop :=
  | psleeq : forall l s t xs, copathsel l s (cocons (l,s,t) xs) t
  | pselneq: forall l l' s s' t t' xs, l <> l' -> s <> s' -> copathsel l' s' xs t' -> copathsel l' s' (cocons (l,s,t) xs) t'.

