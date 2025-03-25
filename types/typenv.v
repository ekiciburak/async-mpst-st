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

Inductive pathRed (R: Path -> Prop): Path -> Prop :=
  | rpn: pathRed R [||]
  | rps: forall x, pathRed R [|x|]
  | rpc: forall x y ys, R (cocons y ys) -> (exists l, red (fst x) l (fst y)) -> pathRed R (cocons x (cocons y ys)).

Lemma mon_pr: monotone1 pathRed.
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       constructor.
       constructor.
       constructor. apply LE, H.
       destruct H0 as (l,H0).
       exists l. apply H0.
Qed.

Definition pathRedC pt := paco1 (pathRed) bot1 pt. 

Inductive eventually {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall x xs, F xs -> eventually F R (cocons x xs)
  | evc: forall x xs, R xs -> eventually F R (cocons x xs).

Definition eventualyP := @eventually (ctx*lab).

Lemma mon_ev: forall F, monotone1 (eventualyP F).
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - apply evh. easy.
       - apply evc, LE, H. 
Qed.

Definition eventuallyC F p := paco1 (eventualyP F) bot1 p.

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).

Definition alwaysP := @alwaysG (ctx*lab).

Lemma mon_alw: forall F, monotone1 (alwaysP F).
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - apply alwn. easy.
       - apply alwc. easy. apply LE, H0. 
Qed.

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
  (forall p q l l', enabled (redE (ls p q l)) pt -> eventuallyC (hPS p q l') pt) /\
  (forall p q l,    enabled (redE (lr q p l)) pt -> eventuallyC (hPR p q l) pt).

Definition fairPathC pt := pathRedC pt /\ alwaysC fairPath pt.

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
  (forall p q l s sig T,  enqueued p q l s sig T pt  -> eventuallyC (hPR q p l) pt) /\
  (forall p q l s sig ys, dequeued p q l s sig ys pt -> eventuallyC (hPR p q l) pt).

Definition livePathC pt := pathRedC pt /\ alwaysC livePath pt.

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

Lemma cong_fair: forall g g' l pt,
  fairPathC (cocons (g,l) pt) ->
  cCong g g' ->
  fairPathC (cocons (g',l) pt).
Proof. (* pcofix CIH. *)
       intros. destruct H as (Hr,H).
       pinversion H.
       subst.
       split.
       pinversion Hr. subst.
       pfold. constructor.
       subst. destruct H6 as (l1, H6). simpl in H6. 
       pfold. constructor. left. easy.
       exists l1. simpl. eapply cong_red with (g' := g') in H6; easy.
       apply mon_pr.
       pfold. constructor.
       split. destruct H3 as (H3a,H3b).
       intros. simpl in H1.
       destruct H1 as (g'',H1).
       specialize(H3a p q l0 l').
       assert(enabled (redE (ls p q l0)) (cocons (g, l) pt)).
       { simpl. exists g''. apply cong_red with (g := g'). easy. easy. }
       apply H3a in H2.

       pinversion H2. subst. pfold. constructor. easy.
       subst. pfold. apply evc. left. easy.
       apply mon_ev.

       intros. simpl in H1.
       destruct H1 as (g'',H1).
       destruct H3 as (H3a,H3b).
       specialize(H3b p q l0).
       assert(enabled (redE (lr q p l0)) (cocons (g, l) pt)).
       { simpl. exists g''. apply cong_red with (g := g'). easy. easy. }
       apply H3b in H2.

       pinversion H2. subst. pfold. constructor. easy.
       subst. pfold. apply evc. left. easy.
       apply mon_ev.

       left. easy.
       apply mon_alw.
Qed.

Lemma qinvF: forall sig a, qCong nil (a :: sig) -> False. 
Proof. intro xs.
       induction xs; intros.
       - inversion H.
         assert(q = nil).
         { case_eq q; intros; subst; easy. }
         subst. easy.
         assert(q = nil).
         { case_eq q; intros; subst; easy. }
         subst. easy.
         assert(q1 = nil /\ q2 = nil /\ q3 = nil).
         { case_eq q1; case_eq q2; case_eq q3; intros; subst; easy. }
         destruct H0 as (Ha,(Hb,Hc)).
         subst. easy.
         assert(q = nil /\ [:: (p1, l1, s1), (p2, l2, s2) & q'] = nil).
         { case_eq q; intros; subst; easy. }
         destruct H3 as (Ha,Hb). subst. easy.
      - inversion H.
         assert(q = nil).
         { case_eq q; intros; subst; easy. }
         subst. easy.
         assert(q = nil).
         { case_eq q; intros; subst; easy. }
         subst. easy.
         assert(q1 = nil /\ q2 = nil /\ q3 = nil).
         { case_eq q1; case_eq q2; case_eq q3; intros; subst; easy. }
         destruct H0 as (Ha,(Hb,Hc)).
         subst. easy.
         assert(q = nil /\ [:: (p1, l1, s1), (p2, l2, s2) & q'] = nil).
         { case_eq q; intros; subst; easy. }
         destruct H3 as (Ha,Hb). subst. easy.
Qed.

Lemma _B_1: forall g g', live g -> cCong g g' -> live g'.
Proof. intros.
       unfold live. intros.
       symmetry in H0.
       specialize(cong_fair g' g l pt H1 H0); intro Hf.
       unfold live in H.
       apply H in Hf.
       destruct Hf as (Hr, Hf).
       pinversion Hf.
       subst. 
       split. 
       pinversion Hr. subst. pfold. constructor. subst. pfold. constructor. left. easy.
       destruct H7 as (l',H7).
       simpl in H7.
       exists l'. simpl. eapply cong_red with (g' := g') in H7; easy.
       apply mon_pr.
       pfold. constructor.
       destruct H4 as (H4a,H4b).
       split.

       intros.
       specialize(H4a p q l0 s sig T).
       assert(enqueued p q l0 s sig T (cocons (g, l) pt) ).
       { simpl. simpl in H2.
         destruct H0 as (Ha,(Hb,Hc)).
         case_eq(M.find p g'); intros.
         destruct p0 as (c1,t1).
         rewrite H0 in H2.
         case_eq(M.find p g); intros.
         destruct p0 as (c2,t2).
         specialize(Ha p c1 c2 t1 t2 H0 H3).
         destruct Ha as (Ha1,Ha2).
         rewrite <- Ha1, <- Ha2. easy.
         specialize(Hb p c1 t1 H0 H3).
         destruct Hb as (Hb1,Hb2).
         destruct H2 as (H2a,H2b).
         rewrite Hb1 in H2a.
         apply qinvF in H2a. easy.
         rewrite H0 in H2.
         easy.
       } 
       apply H4a in H3.
       pinversion H3. subst. pfold. constructor. easy.
       subst. pfold. apply evc. left. easy.
       apply mon_ev.
       
       intros.
       specialize(H4b p q l0 s sig ys).
       assert(dequeued p q l0 s sig ys (cocons (g, l) pt)).
       { simpl. simpl in H2.
         destruct H0 as (Ha,(Hb,Hc)).
         case_eq(M.find p g'); intros.
         destruct p0 as (c1,t1).
         rewrite H0 in H2.
         case_eq(M.find p g); intros.
         destruct p0 as (c2,t2).
         specialize(Ha p c1 c2 t1 t2 H0 H3).
         destruct Ha as (Ha1,Ha2).
         rewrite <- Ha1, <- Ha2. easy.
         specialize(Hb p c1 t1 H0 H3).
         destruct Hb as (Hb1,Hb2).
         destruct H2 as (H2a,(H2b,H2c)).
         rewrite Hb2 in H2c.
         inversion H2c.
         rewrite H0 in H2.
         easy.
       }
       apply H4b in H3.
       pinversion H3. subst. pfold. constructor. easy.
       subst. pfold. apply evc. left. easy.
       apply mon_ev.

       left. easy.
       apply mon_alw.
Qed.

(* Lemma fair_red: forall g g' l l0 pt,
  fairPathC (cocons (g', l0) pt) ->
  red g l g' ->
  fairPathC (cocons (g, l) (cocons (g', l0) pt)).
Proof. intros.
       destruct H as (Hr,H).
       pinversion H.
       split. admit.
       subst. pfold. constructor.
       split. intros.
       simpl in H1.
       destruct H3 as (H3a, H3b).
       pfold. apply evc. left.
       apply H3a with (l := l1).
       simpl. unfold redE in H1.
       unfold redE.

Lemma _49: forall g l g', live g -> red g l g' -> live g'.
Proof. unfold live.
       intros.
       specialize(H (cocons (g', l0) pt) l).
       


         intros.
         unfold live.
         intros.
         unfold live in H.

         split. admit.
         pfold. constructor. split. intros.
         simpl in H2.
         destruct H1 as (Hr, H1).
         pinversion H1. subst.
         destruct H5 as (H5a,H5b).
         apply H5b.
         simpl.
         unfold redE.
         inversion H0.
         subst.
       
       revert H.
       induction H0; intros.
       - subst. unfold live. intros.
         unfold live in H4.
         pfold. constructor.
         split.
         intros.
         simpl in H6.
         pinversion H5. subst.
         destruct H9 as (H9a,H9b). apply H9b.
         simpl.
         case_eq(String.eqb p0 p); intros.
         + rewrite String.eqb_eq in H7.
           subst. rewrite M.add_spec1 in H6.
           
           Search M.find.
         pfold. .
          destruct H6 as (g,Hg).
         assert(fairPathC (cocons (M.add p ((q, l, s') :: sigp, Tp) (M.add q (sigq, lt_receive p xs) gam), l0) pt) ).
         { pfold. constructor.
           split.
           intros. simpl in H6.
           destruct H6 as (g,Hg).
           inversion Hg. subst.
           pfold. apply evc. left. 
           pinversion H5. subst.
           split.
           destruct H8 as (H8a, H8b).
           intros.
           pfold. apply evc. simpl in H6.
           
         
       specialize(H  (cocons (g', l0) pt) l).

       
Admitted. *)

