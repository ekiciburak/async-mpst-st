Require Import ST.processes.unscoped ST.processes.process ST.types.local ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import List Datatypes ZArith.
Local Open Scope string_scope.
Import ListNotations.
From MMaps Require Import MMaps.

CoInductive coseq (A: Type): Type :=
  | conil : coseq A
  | cocons: A -> coseq A -> coseq A.

Arguments conil {_}.
Arguments cocons {_} _ _.

Definition coseq_id {A: Type} (c: coseq A): coseq A :=
  match c with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Lemma coseq_eq: forall {A: Type} (c: coseq A), c = coseq_id c.
Proof. destruct c; easy. Defined.

CoInductive coqes (A: Type): Type :=
  | colin : coqes A
  | cosnoc: coqes A -> A -> coqes A.

Arguments colin {_}.
Arguments cosnoc {_} _ _.

Definition coqes_id {A: Type} (c: coqes A): coqes A :=
  match c with
    | colin       => colin
    | cosnoc xs x => cosnoc xs x
  end.

Lemma coqes_eq: forall {A: Type} (c: coqes A), c = coqes_id c.
Proof. destruct c; easy. Defined.

Module SS.

  Import String.
  Definition t := string.
  Definition eq x y := if eqb x y then True else False.

  Lemma equiv: Equivalence eq.
  Proof. constructor.
         - repeat intro. unfold eq. rewrite eqb_refl. easy.
         - repeat intro. unfold eq in *.
           case_eq(x =? y ); intros.
           + rewrite eqb_sym in H0. rewrite H0. easy.
           + rewrite H0 in H. easy.
         - repeat intro. unfold eq in *.
           case_eq(x =? y ); intros.
           + case_eq(y =? z); intros.
             ++ rewrite eqb_eq in H1. rewrite eqb_eq in H2.
                subst. rewrite eqb_refl. easy.
             ++ rewrite H2 in H0. easy.
           + rewrite H1 in H. easy. 
  Qed.

  Lemma dec : forall x y : string, {eq x y} + {~ eq x y}.
  Proof. intros.
         unfold eq.
         case_eq(x =? y ); intros.
         + left. easy.
         + right. easy.
  Qed.

  Definition eq_equiv := equiv.

  Definition eq_dec := dec.

End SS.

Module M  := MMaps.WeakList.Make(SS).
Module MF := MMaps.Facts.Properties SS M. 

Notation queue := (list (participant*label*local.sort)) (only parsing).
Definition ctx: Type := M.t (queue*local).

Definition both (z: nat) (o:option local) (o':option local) :=
 match o,o' with 
   | Some _, None  => o
   | None, Some _  => o'
   | _,_           => None
 end.

Definition unf (l: local): local :=
  match l with
    | lt_mu L => subst_local ((lt_mu l) .: lt_var) L
    | _       => l
  end.

CoFixpoint capp {A: Type} (s1 s2: coseq A): coseq A :=
  match s2 with
    | conil       => s1
    | cocons x xs => cocons x (capp xs s2)
  end.

Inductive qCong: queue -> queue -> Prop :=
  | qcl   : forall q, qCong (q ++ []) q
  | qcr   : forall q, qCong ([] ++ q) q
  | qassoc: forall q1 q2 q3, qCong (q1 ++ (q2 ++ q3)) ((q1 ++ q2) ++ q3)
  | qcomm : forall q q' p1 p2 l1 l2 s1 s2, 
            p1 <> p2 -> 
            qCong (q ++ [(p1,l1,s1)] ++ [(p2,l2,s2)] ++ q') 
                  (q ++ [(p2,l2,s2)] ++ [(p1,l1,s1)] ++ q').

Inductive lCong: local -> local -> Prop :=
  | lunf: forall l, lCong l (unf l). 

Inductive lab: Type :=
  | ls: participant -> participant -> label -> lab
  | lr: participant -> participant -> label -> lab.

Fixpoint retc (l: list (label*local.sort*local)) (a: label): option (local.sort*local) :=
  match l with
    | nil         => None
    | (x,s,T)::xs => if String.eqb x a then Some (s,T) else retc xs a 
  end.

Definition cCong (g1 g2: ctx):= 
  (forall p c1 c2, M.find p g1 = Some c1 -> M.find p g2 = Some c2 -> qCong (fst c1) (fst c2) /\ lCong (snd c1) (snd c2)) \/
  (forall p q c1 c2, M.find p g1 = Some c1 -> M.find p g2 = None -> M.find q g1 = None -> M.find q g2 = Some c2 -> qCong (fst c1) nil /\ lCong (snd c1) lt_end /\ qCong (fst c2) nil /\ lCong (snd c2) lt_end).

Inductive red: ctx -> lab -> ctx -> Prop :=
  | e_recv  : forall p q sigp sigq gam l Tp s s' Tk xs,
              M.mem p gam = false ->
              M.mem q gam = false ->
              retc xs l = Some (s, Tk) ->
              subsort s' s ->
              red (M.add p (((q,l,s')::sigp), Tp) (M.add q (sigq, lt_receive p xs) gam)) (lr q p l) (M.add p (sigp, Tp) (M.add q (sigq, Tk) gam))
  | e_send  : forall p q sig gam l s Tk xs,
              M.mem p gam = false ->
              retc xs l = Some (s, Tk) ->
              red (M.add p (sig, lt_send q xs) gam) (ls p q l) ((M.add p ((sig ++ [(q,l,s)]), Tk)) gam)
  | e_struct: forall g g1 g' g1' a,
              cCong g g1 ->
              cCong g1' g' ->
              red g1 a g1' -> red g a g'.

Definition redE l g := exists g', red g l g'.


Notation Path := (coseq (ctx*lab)) (only parsing).

Inductive eventually {A: Type} (F: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall xs, F xs -> eventually F xs
  | evc: forall x xs, eventually F xs -> eventually F (cocons x xs).

Definition eventualyP := @eventually (ctx*lab).

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).

Definition alwaysP := @alwaysG (ctx*lab).

Definition alwaysC F p := paco1 (alwaysP F) bot1 p.

Definition enabled (F: ctx -> Prop) (pt: Path): Prop :=
  match pt with
    | cocons (g, l) xs => F g
    | _                => False 
  end.

Definition hPR (p q: participant) (l: label) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lr a b l')) xs => if andb (String.eqb p a) (andb (String.eqb q b) (String.eqb l l')) then True else False
    | _                          => False 
  end.

Definition hPS (p q: participant) (l: label) (pt: Path): Prop :=
  match pt with
    | cocons (g, (ls a b l')) xs => if andb (String.eqb p a) (andb (String.eqb q b) (String.eqb l l')) then True else False
    | _                          => False 
  end.

Inductive fairPath (pt: Path): Prop :=
  | F1: forall p q l l', enabled (redE (ls p q l)) pt -> eventually (hPS p q l') pt -> fairPath pt
  | F2: forall p q l,    enabled (redE (lr q p l)) pt -> eventually (hPR p q l) pt  -> fairPath pt.

Definition fairness := alwaysC fairPath.

Definition enqueued (p q: participant) (l: label) (s: local.sort) sig (T: local) (pt: Path): Prop :=
  match pt with
    | cocons (g, tl) xs => 
      match M.find p g with
        | Some (queue, T') => qCong queue ((q,l,s)::sig) /\ lCong T' T
        | _                => False 
      end
    | _                => False 
  end.

Fixpoint inL (l: list (label*local.sort*local)) (a: label): bool :=
  match l with
    | nil         => false
    | (x,s,T)::xs => if String.eqb x a then true else inL xs a 
  end.

Definition dequeued (p q: participant) (l: label) (s: local.sort) sigp ys (pt: Path): Prop :=
  match pt with
    | cocons (g, tl) xs => 
      match M.find p g with
        | Some (queue, T') => inL ys l /\ qCong queue sigp /\ lCong T' (lt_receive q ys)
        | _                => False 
      end
    | _                => False 
  end.

Inductive livePath (pt: Path): Prop :=
  | L1: forall p q l s sig T,  enqueued p q l s sig T pt  -> eventually (hPR q p l) pt -> livePath pt
  | L2: forall p q l s sig ys, dequeued p q l s sig ys pt -> eventually (hPR p q l) pt -> livePath pt.

Definition liveness := alwaysC livePath.


Definition exGamma p q l s := M.add p (@conil ctx, lt_mu (lt_send q (cons (l, s, (lt_var 0)) nil))) M.empty.




