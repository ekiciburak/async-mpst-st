Require Import ST.processes.unscoped ST.processes.process ST.types.local ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import List Datatypes ZArith.
Local Open Scope string_scope.
Import ListNotations.
Import CoListNotations.
From MMaps Require Import MMaps.

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
  Defined.

  Lemma dec : forall x y : string, {eq x y} + {~ eq x y}.
  Proof. intros.
         unfold eq.
         case_eq(x =? y ); intros.
         + left. easy.
         + right. easy.
  Defined.

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

Inductive qCong: queue -> queue -> Prop :=
  | qcl   : forall q, qCong (q ++ []) q
  | qcr   : forall q, qCong ([] ++ q) q
  | qassoc: forall q1 q2 q3, qCong (q1 ++ (q2 ++ q3)) ((q1 ++ q2) ++ q3)
  | qcomm : forall q q' p1 p2 l1 l2 s1 s2, 
            p1 <> p2 -> 
            qCong (q ++ [(p1,l1,s1)] ++ [(p2,l2,s2)] ++ q') 
                  (q ++ [(p2,l2,s2)] ++ [(p1,l1,s1)] ++ q').

Declare Instance Equivalence_qcong : Equivalence qCong.
#[global] Declare Instance RWQC: Proper (qCong ==> qCong ==> impl) qCong.

Inductive lCong: local -> local -> Prop :=
  | lunf: forall l, lCong l (unf l).

Declare Instance Equivalence_lcong : Equivalence lCong.
#[global] Declare Instance RWLC: Proper (lCong ==> lCong ==> impl) lCong.

Inductive lab: Type :=
  | ls: participant -> participant -> label -> lab
  | lr: participant -> participant -> label -> lab.

Fixpoint retc (l: list (label*local.sort*local)) (a: label): option (local.sort*local) :=
  match l with
    | nil         => None
    | (x,s,T)::xs => if String.eqb x a then Some (s,T) else retc xs a 
  end.

Definition cCong (g1 g2: ctx):= 
  (forall p c1 c2 t1 t2, M.find p g1 = Some (c1,t1) -> M.find p g2 = Some (c2,t2) -> qCong c1 c2 /\ lCong t1 t2) /\
  (forall p c t, M.find p g1 = Some (c,t) -> M.find p g2 = None -> qCong c nil /\ lCong t lt_end) /\
  (forall p c t, M.find p g1 = None -> M.find p g2 = Some (c,t) -> qCong c nil /\ lCong t lt_end).

Lemma ccT: Transitive cCong.
Proof. repeat intro.
       destruct H as (Ha,(Hb,Hc)).
       destruct H0 as (Hd,(He,Hf)).
       split.
       + intros.
         case_eq(M.find p y); intros.
         destruct p0 as (c3,t3).
         specialize(Ha p c1 c3 t1 t3 H H1).
         specialize(Hd p c3 c2 t3 t2 H1 H0).
         destruct Ha as (Ha1,Ha2).
         destruct Hd as (Hd1,Hd2).
         rewrite Ha1 Hd1 Ha2 Hd2. easy.
         specialize(Hb p c1 t1 H H1).
         specialize(Hf p c2 t2 H1 H0).
         destruct Hb as (Hb1,Hb2).
         destruct Hf as (Hf1,Hf2).
         rewrite Hb1 Hf1 Hb2 Hf2. easy.
       split.
       + intros.
         case_eq(M.find p y); intros.
         destruct p0 as (c3,t3).
         specialize(Ha p c c3 t t3 H H1).
         specialize(He p c3 t3 H1 H0).
         destruct Ha as (Ha1,Ha2).
         destruct He as (He1,He2).
         rewrite Ha1 He1 Ha2 He2. easy.
         specialize(Hb p c t H H1). easy.
       + intros.
         case_eq(M.find p y); intros.
         destruct p0 as (c3,t3).
         specialize(Hc p c3 t3 H H1).
         specialize(Hd p c3 c t3 t H1 H0).
         destruct Hc as (Hc1,Hc2).
         destruct Hd as (Hd1,Hd2).
         rewrite <- Hd1, <- Hd2. easy.
         specialize(Hf p c t H1 H0).
         easy.
Qed.

Lemma ccS: Symmetric cCong.
Proof. repeat intro.
       unfold cCong in H.
       destruct H as (Ha,(Hb,Hc)).
       split.
       + intros.
         specialize(Ha p c2 c1 t2 t1 H0 H).
         destruct Ha as (Ha1, Ha2).
         rewrite Ha1 Ha2. easy.
       split.
       + intros.
         specialize(Hc p c t H0 H). easy.
       + intros.
         specialize(Hb p c t H0 H). easy.
Qed.

Lemma ccR: Reflexive cCong.
Proof. repeat intro.
       split.
       + intros. rewrite H in H0. inversion H0. subst. easy.
       split.
       + intros. rewrite H in H0. inversion H0.
       + intros. rewrite H in H0. inversion H0.
Qed.

Instance Equivalence_ccong : Equivalence cCong.
Proof. unshelve econstructor.
       - exact ccR.
       - exact ccS.
       - exact ccT.
Defined.

#[global] Declare Instance RWCC: Proper (cCong ==> cCong ==> impl) cCong.

Inductive red: ctx -> lab -> ctx -> Prop :=
  | e_recv  : forall p q sigp sigq gam l Tp s s' Tk xs,
              p <> q ->
              M.mem p gam = false ->
              M.mem q gam = false ->
              retc xs l = Some (s, Tk) ->
              subsort s' s ->
              red (M.add p (((q,l,s')::sigp), Tp) (M.add q (sigq, lt_receive p xs) gam)) (lr q p l) (M.add p (sigp, Tp) (M.add q (sigq, Tk) gam))
  | e_send  : forall p q sig gam l s Tk xs,
              p <> q ->
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

Definition fairPath (pt: Path): Prop :=
  (forall p q l l', enabled (redE (ls p q l)) pt -> eventually (hPS p q l') pt) /\
  (forall p q l,    enabled (redE (lr q p l)) pt -> eventually (hPR p q l) pt).

Definition fairPathC := alwaysC fairPath.

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

Definition livePath (pt: Path): Prop :=
  (forall p q l s sig T,  enqueued p q l s sig T pt  -> eventually (hPR q p l) pt) /\
  (forall p q l s sig ys, dequeued p q l s sig ys pt -> eventually (hPR p q l) pt).

Definition livePathC := alwaysC livePath.

Definition live (g: ctx) := forall (pt: Path) (l: lab), fairPathC (cocons (g, l) pt) -> livePathC (cocons (g, l) pt).

Lemma cong_red: forall g g' gr l, red g l gr -> cCong g g' -> red g' l gr.
Proof. intros. revert g' H0. 
       induction H; intros.
       - apply e_struct with (g1  := (M.add p ((q, l, s') :: sigp, Tp) (M.add q (sigq, lt_receive p xs) gam))) 
                             (g1' := (M.add p (sigp, Tp) (M.add q (sigq, Tk) gam))).
         rewrite <- H4. easy. easy.
       - apply e_recv with (s := s); try easy.
       - eapply e_struct with (g1  := (M.add p (sig, lt_send q xs) gam)) 
                              (g1' := (M.add p (sig ++ [(q, l, s)], Tk) gam)).
         rewrite <- H2. easy. easy.
         apply e_send; easy.
       - apply e_struct with (g1 := g) (g1' := g1').
         rewrite H2. easy.
         rewrite H0. easy.
         apply IHred. rewrite H. easy.
Qed.


Lemma _49: forall g l g', live g -> red g l g' -> live g'.
Proof. pcofix CIH. intros.
       pinversion H2.
       subst. pfold.
       constructor.
       unfold live in H0.
Admitted.

