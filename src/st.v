From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.types.local.
Require Import String List Nat.
Local Open Scope string_scope.
Import ListNotations.
Import CoListNotations.

(* session trees *)
CoInductive st: Type :=
  | st_end    : st
  | st_receive: participant -> coseq (label*sort*st) -> st
  | st_send   : participant -> coseq (label*sort*st) -> st.

Inductive wfH (R: st -> Prop): st -> Prop :=
  | wf_end: wfH R st_end
  | wf_rcv: forall p xs,
            xs <> [||] ->
            ForallCo (fun u => exists l s t, u = (l,s,t) /\ R t) xs ->
            wfH R (st_receive p xs)
  | wf_snd: forall p xs,
            xs <> [||] ->
            ForallCo (fun u => exists l s t, u = (l,s,t) /\ R t) xs ->
            wfH R (st_send p xs).

Definition wfC: st -> Prop := fun s1 => paco1 wfH bot1 s1.

Lemma fHo_forall: forall l r r',
  (forall x0 : st, r x0 -> r' x0) ->
  paco1 (ForallHo (fun u : string * sort * st => exists (l : string) (s : sort) (t : st), u = (l, s, t) /\ r t)) bot1 l ->
  paco1 (ForallHo (fun u : string * sort * st => exists (l0 : string) (s : sort) (t : st), u = (l0, s, t) /\ r' t)) bot1 l.
Proof. intros.
       revert l H0.
       pcofix CIH. intros.
       pinversion H1. pfold. constructor.
       subst. pfold. constructor.
       destruct H0 as (l1,(s1,(t1,(Ha,Hb)))).
       exists l1. exists s1. exists t1. split. easy. apply H; easy.
       right. apply CIH. easy.
       apply mon_fHo.
Qed.

Lemma mon_wfH: monotone1 wfH.
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - constructor.
       - constructor. easy.
         pinversion H0. subst. easy. subst.
         pfold. constructor.
         destruct H1 as (l1,(s1,(t1,(Ha,Hb)))).
         exists l1. exists s1. exists t1. split. easy. apply LE; easy.
         left. apply fHo_forall with (r := r); easy.
         apply mon_fHo.
       - constructor. easy.
         pinversion H0. subst. easy. subst.
         pfold. constructor.
         destruct H1 as (l1,(s1,(t1,(Ha,Hb)))).
         exists l1. exists s1. exists t1. split. easy. apply LE; easy.
         left. apply fHo_forall with (r := r); easy.
         apply mon_fHo.
Qed.

Inductive st_equiv (R: st -> st -> Prop): st -> st -> Prop :=
  | eq_st_end: st_equiv R st_end st_end
  | eq_st_rcv: forall p xs ys,
               Forall2Co (fun u v => exists l s t l' s' t', u = (l,s,t) /\ v = (l',s',t') /\ l = l' /\ s = s'/\ R t t') ys xs ->
               st_equiv R (st_receive p ys) (st_receive p xs)
  | eq_st_snd: forall p xs ys,
               Forall2Co (fun u v => exists l s t l' s' t', u = (l,s,t) /\ v = (l',s',t') /\ l = l' /\ s = s'/\ R t t') ys xs ->
               st_equiv R (st_send p ys) (st_send p xs). 

Definition st_equivC: st -> st -> Prop := fun s1 s2 => paco2 st_equiv bot2 s1 s2.

Axiom stExt: forall s1 s2, st_equivC s1 s2 -> s1 = s2.

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
    | (l1,s1,t1)::xs => if String.eqb l' l1 then Some (s1,t1) else lst2fun xs l'
    | nil            => None
  end.

Fixpoint retLoc (l:list(label*sort*local)) (l':label): option (sort*local) :=
  match l with
    | (l1,s1,lt1)::ys => if String.eqb l' l1 then Some(s1, lt1) else retLoc ys l'
    | nil             => None
  end.

CoFixpoint lt2st (l: local): st :=
  match full_unf l with
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

Lemma sameTree: forall l, lt2st l = lt2st (full_unf l). 
Proof. 
  intros. 
  rewrite(st_eq(lt2st (full_unf l))). simpl.
  rewrite full_unf_idemp.
  destruct l.
  rewrite(st_eq(lt2st (lt_var n))). simpl. easy. simpl.
  rewrite(st_eq(lt2st lt_end)). simpl. easy. simpl.
  rewrite(st_eq(lt2st (lt_send s l))). simpl. easy. simpl.
  rewrite(st_eq(lt2st (lt_receive s l))). simpl. easy.
  rewrite(st_eq(lt2st (lt_mu l) )). simpl. easy.
Qed.

Lemma monH2: forall ys xs r r',
  Forall2C (fun u v : string * sort * st => exists (l : string) (s : sort) (t : st) (t' : st), u = (l, s, t) /\ v = (l, s, t') /\ r t t') ys xs ->
  (forall x0 x1 : st, r x0 x1 -> r' x0 x1) ->
  Forall2C (fun u v : string * sort * st => exists (l : string) (s : sort) (t : st) (t' : st), u = (l, s, t) /\ v = (l, s, t') /\ r' t t') ys xs.
Proof. intros.
       induction H; intros.
       - constructor.
       - constructor.
         destruct H as (l1,(s1,(t1,(t2,(Ha,(Hb,Hc)))))).
         exists l1. exists s1. exists t1. exists t2.
         split. easy. split. easy. apply H0. easy.
         apply IHForall2C.
Qed.

Lemma monHo2: forall ys xs r r',
  Forall2Co (fun u v : string * sort * st => exists (l : string) (s : sort) (t : st) (t' : st), u = (l, s, t) /\ v = (l, s, t') /\ r t t') ys xs ->
  (forall x0 x1 : st, r x0 x1 -> r' x0 x1) ->
  Forall2Co (fun u v : string * sort * st => exists (l : string) (s : sort) (t : st) (t' : st), u = (l, s, t) /\ v = (l, s, t') /\ r' t t') ys xs.
Proof. intros. revert xs ys H. pcofix CIH.
       intros.
       pfold.
       pinversion H1.
       subst.
       constructor.
       subst.
       constructor.
       destruct H as (l1,(s1,(t1,(t2,(Ha,(Hb,Hc)))))).
       exists l1. exists s1. exists t1. exists t2. 
       split. easy. split. easy.
       apply H0; easy.
       right. apply CIH.
       easy.
       unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - constructor. 
         destruct H as (l1,(s1,(t1,(t2,(Ha,(Hb,Hc)))))).
       exists l1. exists s1. exists t1. exists t2. 
       split. easy. split. easy.
       easy.
       apply LE; easy.
Qed.

(*
Check lt_send.
Check lt_var 0.

Let lr := lt_mu (lt_send "p" [("l",sint,(lt_var 0))] ).
Let lr2 := Eval simpl in unfold_muL lr.
Eval simpl in unfold_muL lr2.
Print lr.
Print lr2.  *)

Definition sfun (l: label) (s: sort) (x: st): (label -> option(sort*st)) :=
  fun l' => if String.eqb l l' then Datatypes.Some(s,x) else Datatypes.None. 

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
    | (lbl,s,x)::xs => if andb (String.eqb u lbl) (sort_eqb v s) then x else pathsel u v xs
    | nil           => st_end
  end.

(*co-path selection example*)

Inductive copathsel: label -> sort -> coseq(label*sort*st) -> st -> Prop :=
  | psleeq  : forall l s t xs, copathsel l s (cocons (l,s,t) xs) t
  | pselneql: forall l l' s s' t t' xs, l <> l' -> copathsel l' s' xs t' -> copathsel l' s' (cocons (l,s,t) xs) t'
  | pselneqs: forall l l' s s' t t' xs, s <> s' -> copathsel l' s' xs t' -> copathsel l' s' (cocons (l,s,t) xs) t'.

CoFixpoint Ext1 := st_receive "q" (cocons ("l7", sint, Ext1) conil).
CoFixpoint Ext2 := st_send "q" (cocons ("l8", sint, Ext2) conil).
Definition cpath := (cocons("l4",sint,Ext1) (cocons ("l5",sint,Ext2) (cocons("l6",sint,st_end) conil))).

Lemma cpselC: copathsel "l6" sint cpath st_end.
Proof. constructor. easy.
       constructor. easy.
       constructor.
Qed.

