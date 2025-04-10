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

#[global] Instance RWQC: Proper (qCong ==> qCong ==> impl) qCong.
Proof. repeat intro.
       destruct H.
       - destruct H0.
         + rewrite !app_nil_r in H1. easy.
         + rewrite app_nil_r app_nil_l in H1. easy.
         + rewrite app_nil_r in H1. rewrite <- app_assoc. easy.
         + apply transitivity with (y := (q0 ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           rewrite !app_nil_r in H1. easy.
           apply qcomm. easy.
       - destruct H0.
         + rewrite !app_nil_r in H1. easy.
         + rewrite !app_nil_l in H1. easy.
         + rewrite app_nil_l in H1. rewrite <- app_assoc. easy.
         + apply transitivity with (y := (q0 ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           rewrite app_nil_l in H1. easy.
           apply qcomm. easy.
       - destruct H0.
         + rewrite !app_nil_r in H1. rewrite <- app_assoc. easy.
         + rewrite app_nil_l in H1. rewrite <- app_assoc. easy.
         + rewrite <- app_assoc. rewrite <- app_assoc.
           easy.
         + rewrite <- app_assoc.
           apply transitivity with (y :=  (q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           easy.
           apply qcomm. easy.
       - destruct H0.
         + rewrite !app_nil_r in H1.
           apply transitivity with (y := (q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           constructor. easy. easy.
         + rewrite !app_nil_l in H1.
           apply transitivity with (y := (q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           constructor. easy. easy.
         + apply transitivity with (y :=  (q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           symmetry.
           constructor. easy.
           rewrite <- app_assoc. easy.
         + apply transitivity with (y := (q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')).
           constructor. easy.
           symmetry.
           apply transitivity with (y := (q0 ++ [(p0, l0, s0)] ++ [(p3, l3, s3)] ++ q'0)).
           constructor. easy.
           easy.
Qed.

Inductive lCong: local -> local -> Prop :=
  | lunf: forall l, lCong l (unf l).

Declare Instance Equivalence_lcong : Equivalence lCong.

#[global] Instance RWLC: Proper (lCong ==> lCong ==> impl) lCong.
Proof. repeat intro.
       destruct H.
       destruct H1. easy.
Qed.

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

Definition update (g: ctx) (p: participant) (a: queue*local): ctx :=
  match M.find p g with
    | Some b => M.add p a g 
    | None   => g
  end.

Inductive red: ctx -> lab -> ctx -> Prop :=
  | e_recv  : forall p q sigp sigq gam l Tp s s' Tk xs,
              p <> q ->
              retc xs l = Some (s, Tk) ->
              subsort s' s ->
              (
                match M.find p gam with
                  | Some (sig', T') => qCong sig' ((q,l,s')::sigp) /\ lCong T' Tp
                  | _               => False 
                end
              ) ->
              (
                match M.find q gam with
                  | Some (sig', T') => qCong sig' sigq /\ lCong T' (lt_receive p xs)
                  | None            => False
                end
              ) ->
              red gam (lr q p l) (M.add p (sigp, Tp) (M.add q (sigq, Tk) gam))
  | e_send  : forall p q sig gam l s Tk xs,
              p <> q ->
              retc xs l = Some (s, Tk) ->
              (
                match M.find p gam with
                 | Some (sig', T') => qCong sig' sig /\ lCong T' (lt_send q xs)
                 | _               => False
                end
              ) ->
              red gam (ls p q l) (M.add p ((sig ++ [(q,l,s)]), Tk) gam)
  | e_struct: forall g g1 g' g1' a,
              cCong g g1 ->
              cCong g1' g' ->
              red g1 a g1' -> red g a g'.

Definition redE l g := exists g', red g l g'.

Notation Path := (coseq (ctx*lab)) (only parsing).

Inductive pathRed (R: Path -> Prop): Path -> Prop :=
  | rpn: pathRed R [||]
  | rps: forall x, pathRed R [|x|]
  | rpc: forall x y ys, R (cocons y ys) -> red (fst x) (snd x) (fst y) -> pathRed R (cocons x (cocons y ys)).

Lemma mon_pr: monotone1 pathRed.
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       constructor.
       constructor.
       constructor. apply LE, H.
       apply H0.
Qed.

Definition pathRedC pt := paco1 (pathRed) bot1 pt. 

Class path: Type :=
  mkpath
  {
    upth: Path;
    pobl: pathRedC upth
  }.

Inductive eventually {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall x xs, F (cocons x xs) -> eventually F R (cocons x xs)
  | evc: forall x xs, R xs -> eventually F R (cocons x xs).

(* Definition eventualyP := @eventually (ctx*lab). *)
(* Definition eventualyP pt := @eventually (@upth pt).  *)

Lemma mon_ev: forall {A} (F: coseq A -> Prop), monotone1 (eventually F).
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - apply evh. easy.
       - apply evc, LE, H. 
Qed.

Definition eventuallyC {A} (F: coseq A -> Prop) p := paco1 (eventually F) bot1 p.

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).

(* Definition alwaysP := @alwaysG (ctx*lab).  *)

(* Definition alwaysP := @alwaysG (path). *)

Lemma mon_alw: forall {A} (F: coseq A -> Prop), monotone1 (alwaysG F).
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - apply alwn. easy.
       - apply alwc. easy. apply LE, H0. 
Qed.

Definition alwaysC {A} (F: coseq A -> Prop) p := paco1 (alwaysG F) bot1 p.

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
  (forall p q l, enabled (redE (ls p q l)) pt -> exists l', eventuallyC (hPS p q l') pt) /\
  (forall p q l, enabled (redE (lr p q l)) pt -> eventuallyC (hPR p q l) pt).

Definition fairPathC (pt: Path) := (* pathRedC pt /\ *) alwaysC fairPath pt.

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
  (forall p q l s sig ys, dequeued p q l s sig ys pt -> exists l', List.In l' (map fst (map fst ys)) /\  eventuallyC (hPR p q l') pt).

Definition livePathC (pt: Path) := (* pathRedC pt /\ *) alwaysC livePath pt.

(* Definition livePathC (pt: path) := alwaysC livePath (@upth pt). *)

Definition live (g: ctx) := forall (pt: Path) (l: lab), fairPathC (cocons (g, l) pt) -> livePathC (cocons (g, l) pt).

Require Import Coq.Program.Equality.

(* Lemma red_deq: forall g g' l, red g l g' -> M.Eqdom g g'.
Proof. intros.
       induction H; intros.
       - unfold update. 
         unfold M.Eqdom. intros.
         split. intro.
         apply MF.in_add. apply MF.in_add. easy.
         intros.
         apply MF.in_find.
         apply MF.in_find in H4. unfold not in *.
         intros.
         apply H4.
         case_eq(String.eqb p y); intros.
         + rewrite String.eqb_eq in H6. subst.
           rewrite H2 in H5. easy.
           rewrite M.add_spec2.
           case_eq(String.eqb q y); intros.
           ++ rewrite String.eqb_eq in H7. subst.
              rewrite H3 in H5. easy.
              rewrite M.add_spec2. easy.
              rewrite H7. easy. rewrite H6. easy.
       - unfold M.Eqdom. intros.
         split. intro.
         apply MF.in_add. easy.
         intros.
         apply MF.in_find.
         apply MF.in_find in H2. unfold not in *.
         intros.
         apply H2.
         case_eq(String.eqb p y); intros.
         ++ rewrite String.eqb_eq in H4. subst.
            rewrite H1 in H3. easy.
            rewrite M.add_spec2. easy.
            rewrite H4. easy.
         unfold M.Eqdom in *.
         split. intros.
         apply H0, IHred, H. easy.
         intros.
         apply H, IHred, H0. easy.
Qed.
 *)
 
Lemma cong_red: forall g g' gr l, red g l gr -> cCong g g' -> red g' l gr.
Proof. intros.
       revert g' H0.
       induction H; intros.
       - apply e_struct with (g1  := gam)
                             (g1' := (M.add p (sigp, Tp) (M.add q (sigq, Tk) gam))).
         easy. easy.
       - apply e_recv with (s := s) (s' := s') (xs := xs); try easy.
       - eapply e_struct with (g1  := gam) 
                              (g1' := (M.add p (sig ++ [(q, l, s)], Tk) gam)).
         rewrite <- H2. easy. easy.
         apply e_send with (xs := xs); easy.
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
       intros. 
(*        destruct H as (Hr,H). *)
       pinversion H. 
(*     subst.
       split.
       pinversion Hr. subst.
       pfold. constructor.
       subst. simpl in H6. 
       pfold. constructor. left. easy.
       simpl. eapply cong_red with (g' := g') in H6; easy.
       apply mon_pr. *)
       pfold. constructor.
       split. destruct H3 as (H3a,H3b).
       intros.
       specialize(H3a p q l0). simpl in H3.
(*        exists l0. intros. *)
       destruct H3 as (g'',H3).
       assert(enabled (redE (ls p q l0)) (cocons (g, l) pt)).
       { simpl. exists g''. apply cong_red with (g := g'). easy. easy. }
       apply H3a in H5.
       destruct H5 as (l',H5). exists l'.
       pinversion H5. subst. pfold. constructor. easy.
       subst. pfold. apply evc. left. easy.
       apply mon_ev.

       intros. simpl in H5.
       destruct H5 as (g'',H5).
       destruct H3 as (H3a,H3b).
       specialize(H3b p q l0).
       assert(enabled (redE (lr p q l0)) (cocons (g, l) pt)).
       { simpl. exists g''. apply cong_red with (g := g'). easy. easy. }
       apply H3b in H3.

       pinversion H3. subst. pfold. constructor. easy.
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

Lemma qcong_app: forall xs ys a b,
  qCong xs (b::ys) ->
  qCong (xs ++ [a]) (b::ys++[a]). 
Proof. intro xs.
       induction xs; intros.
       - apply qinvF in H. easy.
       - inversion H.
         rewrite app_nil_r in H1.
         subst. inversion H1. subst.
         rewrite app_nil_r.
         easy.
         rewrite app_nil_l in H0.
         subst. inversion H0. subst. easy.
         rewrite <- app_assoc in H2.
         rewrite H1 in H2. inversion H2. subst. rewrite H1. easy.
         rewrite app_comm_cons.
         rewrite <- H1.
         assert(((q ++ [:: (p1, l1, s1), (p2, l2, s2) & q']) ++ [a0]) =
                ((q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ (q' ++ [a0])))).
         { simpl. rewrite <- app_assoc. f_equal. }
         rewrite H3.
         assert(((q ++ [:: (p2, l2, s2), (p1, l1, s1) & q']) ++ [a0]) =
                ((q ++ [(p2, l2, s2)] ++ [(p1, l1, s1)] ++ (q' ++ [a0])))).
         { simpl. rewrite <- app_assoc. f_equal. }
         rewrite H4.
         constructor. easy.
Qed.

Lemma _B_1: forall g g', live g -> cCong g g' -> live g'.
Proof. intros.
       unfold live. intros.
       symmetry in H0.
       specialize(cong_fair g' g l pt H1 H0); intro Hf.
       unfold live in H.
       apply H in Hf.
       pinversion Hf.
       subst. 
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
       destruct H3 as (l', (Hin, H3)). exists l'.
       split. easy.
       pinversion H3. subst. pfold. constructor. easy.
       subst. pfold. apply evc. left. easy.
       apply mon_ev.

       left. easy.
       apply mon_alw.
Qed.

Lemma ev_or: forall {A: Type} (F: coseq A -> Prop) x xs, 
  eventuallyC F (cocons x xs) ->
  F (cocons x xs) \/ eventuallyC F xs.
Proof. intros.
       pinversion H.
       subst. left. easy.
       subst. right. easy.
       apply mon_ev.
Qed.

Lemma red_rcv_inv: forall g g' p r l l',
  l = lr p r l' -> 
  red g l g' ->
  exists ys s t s' sigp,
  match M.find p g with
    | Some (que, T) => lCong T (lt_receive r ys) /\ Some (s, t) = retc ys l' /\ p <> r
    | _             => False
  end /\
  match M.find r g with
    | Some (que, T) => qCong que ((p,l',s')::sigp) /\ subsort s' s /\ p <> r
    | _             => False
  end.
Proof. intros.
       induction H0; intros.
       - inversion H. subst.
         destruct (M.find p gam). destruct p0.
         exists xs. exists s. exists Tk. exists s'. exists sigp. split. easy.
         destruct (M.find r gam). destruct p0.
         easy. easy. easy.
       - easy.
         subst.
         assert(lr p r l' = lr p r l') by easy.
         specialize(IHred H).
         destruct IHred as (ys,(s,(t,(s',(sig',(IH1, IH2)))))).
         exists ys. exists s. exists t. exists s'. exists sig'.
         case_eq(M.find p g1); intros.
         + destruct p0 as (c1, t1).
           rewrite H3 in IH1.
           destruct IH1 as (Hys,(Hys1,Hys2)).
           case_eq(M.find p g); intros.
           ++ destruct p0 as (c2, t2).
              pose proof H0 as Haa.
              destruct H0 as (Ha,(Hb,Hc)).
              specialize(Ha p c2 c1 t2 t1 H4 H3).
              rewrite <- Hys. split. easy.
              case_eq(M.find r g1); intros.
              * destruct p0 as (c3, t3).
                rewrite H0 in IH2.
                destruct IH2 as (Hs,Hs1).
                case_eq(M.find r g); intros.
                ** destruct p0 as (c4,t4).
                   destruct Haa as (Haa,(Hab,Hac)).
                   specialize(Haa r c4 c3 t4 t3 H5 H0).
                   destruct Haa as (Haa1, Haa2).
                   rewrite <- Hs. easy.
                ** destruct Haa as (Haa,(Hab,Hac)).
                   specialize(Hac r c3 t3 H5 H0).
                   destruct Hac as (Hac1,Hac2).
                   rewrite Hac1 in Hs.
                   apply qinvF in Hs. easy.
              * rewrite H0 in IH2. easy.
           ++ destruct H0 as (Ha,(Hb,Hc)).
              specialize(Hc p c1 t1 H4 H3).
              rewrite Hys in Hc. easy.
         + rewrite H3 in IH1. easy.
Qed.

Lemma red_snd_inv: forall g g' p r l l',
  l = ls p r l' -> 
  red g l g' ->
  exists ys s t,
  match M.find p g with
    | Some (que, T) => lCong T (lt_send r ys) /\ Some (s, t) = retc ys l' /\ p <> r
    | _             => False
  end.
Proof. intros.
       induction H0; intros.
       - easy.
       - inversion H. subst.
         exists xs. exists s. exists Tk.
         destruct(M.find p gam). destruct p0. easy. easy.
       - inversion H. subst.
         assert(ls p r l' = ls p r l') by easy.
         specialize(IHred H).
         destruct IHred as (ys, (s, (t, IHred))).
         exists ys. exists s. exists t.
         case_eq(M.find p g1); intros.
         + destruct p0 as (c1, t1).
           rewrite H4 in IHred.
           case_eq(M.find p g); intros.
           ++ destruct p0 as (c2, t2).
              destruct H0 as (Ha,(Hb,Hc)).
              specialize(Ha p c2 c1 t2 t1 H5 H4).
              destruct IHred as (Hys,(Hys1,Hys2)).
              rewrite <- Hys. easy.
              destruct H0 as (Ha,(Hb,Hc)).
              specialize(Hc p c1 t1 H5 H4).
              destruct Hc as (Hc1,Hc2).
              destruct IHred as (Hys,(Hys1,Hys2)).
              rewrite Hc2 in Hys. easy.
         + rewrite H4 in IHred. easy.
Qed.

Lemma _B_2_1a: forall g g' g'' p q r l l' l1 l2,
  l1 = ls p q l ->
  l2 = lr p r l' ->
  red g l1 g' -> red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H0 H2.
       induction H1; intros.
       - easy.
       - inversion H. subst.
         apply red_rcv_inv with (p := p) (r := r) (l' := l') in H4.
         destruct H4 as (ys,(s1,(t1,(s2,(sigp,(H4a, H4b)))))).
         destruct( M.find p gam). destruct p0.
         destruct H4a. rewrite H3 in H2. easy. easy. easy.
       - subst.
         apply IHred with (l2 := lr p r l') (g'' := g''). easy. easy.
         apply cong_red with (g' := g1) in H4; easy.
Qed.

Lemma _B_2_1ad: forall g g' g'' p q r l l' l1 l2,
  r <> q ->
  l1 = ls p q l ->
  l2 = ls p r l' ->
  red g l1 g' -> red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H1 H3.
       induction H2; intros.
       - easy.
       - inversion H0. subst.
         apply red_snd_inv with (p := p) (r := r) (l' := l') in H5.
         destruct H5 as (ys,(s1,(t1,H5))).
         destruct( M.find p gam). destruct p0.
         destruct H3. destruct H5.
         rewrite H4 in H5. inversion H5. subst. easy. easy. easy.
       - subst.
         apply IHred with (l2 := ls p r l') (g'' := g''). easy. easy.
         apply cong_red with (g' := g1) in H5; easy.
Qed.

Lemma _B_2_1b: forall g p q r r' lb1 lb2 l1 l2,
  p <> r ->
  lb1 = ls p q l1 -> 
  lb2 = ls r r' l2 ->
  (exists g', red g lb2 g') -> (forall g', red g lb1 g' -> exists g'', red g' lb2 g'').
Proof. intros.
       induction H3; intros.
       - easy.
       - inversion H0. subst.
         destruct H2 as (g'',H2).
         apply red_snd_inv with (p := r) (r := r') (l' := l2) in H2.
         destruct H2 as (ys, (s', (t', H2))).
         case_eq(M.find r gam); intros.
         + destruct p0 as (c1, t1).
           rewrite H1 in H2.
           exists(M.add r (c1++[(r',l2,s')], t') ((M.add p (sig ++ [(q, l1, s)], Tk) gam))).
           apply e_send with (xs := ys). easy. easy.
           rewrite M.add_spec2. rewrite H1. easy.
           apply String.eqb_neq in H. rewrite H. easy.
           rewrite H1 in H2. easy.
           easy.
       - subst.
         destruct H2 as (g'', H2).
         assert(ls p q l1 = ls p q l1 ) by easy.
         assert((exists g' : ctx, red g1 (ls r r' l2) g') ).
         { exists g''.
           apply e_struct with (g1 := g) (g1' := g'').
           easy. easy. easy.
         }
         specialize(IHred H0 H1).
         destruct IHred as (g''', H3').
         exists g'''.
         apply e_struct with (g1 := g1') (g1' := g'''); easy.
Qed.

Lemma _B_2_1c: forall g p q r r' lb1 lb2 l1 l2,
  lb1 = ls p q l1 -> 
  lb2 = lr r r' l2 ->
  (exists g', red g lb2 g') -> (forall g', red g lb1 g' -> exists g'', red g' lb2 g'').
Proof. intros.
       case_eq(String.eqb r p); intros Hneq.
       rewrite String.eqb_eq in Hneq. subst. 
       destruct H1.
       assert((ls p q l1) = (ls p q l1)) by easy.
       assert(lr p r' l2 = lr p r' l2) by easy.
       specialize(_B_2_1a g g' x p q r' l1 l2 (ls p q l1) (lr p r' l2) H0 H1 H2 H); intros. easy.
       induction H2; intros.
       - easy.
       - inversion H. subst. 
         case_eq(M.find p gam); intros.
         + destruct p0 as (c1, t1).
           destruct H1 as (g',H1).
           rewrite H0 in H4.
           apply red_rcv_inv with (p := r) (r := r') (l' := l2) in H1.
           destruct H1 as (ys,(s',(t',(s1,(sigp,(H1a, H1b)))))).
           case_eq(M.find r gam); intros.
           ++ destruct p0 as (c2, t2).
              rewrite H1 in H1a.
              case_eq(String.eqb r' p); intros Heq.
              rewrite String.eqb_eq in Heq. subst.
              rewrite H0 in H1b.
              exists(M.add p ((sigp++[(q, l1, s)]), Tk) (M.add r (c2,t') ((M.add p (sig ++ [(q, l1, s)], Tk) gam)))).
              apply e_recv with (s := s') (s' := s1) (xs := ys). easy. easy. easy.
              rewrite M.add_spec1. 
              destruct H4 as (H4a, H4b). 
              destruct H1b as (H1b,H1b1).
              rewrite H4a in H1b.
              apply qcong_app with (a := (q, l1, s)) in H1b. easy.
              rewrite M.add_spec2. rewrite H1. easy.
              rewrite String.eqb_sym. rewrite Hneq. easy.
              case_eq(M.find r' gam); intros.
              * destruct p0 as (c3,t3).
                rewrite H5 in H1b.
                destruct H1b as (H1b1,(H1b2,H1b3)).
                exists(M.add r' (sigp, t3) (M.add r (c2,t') ((M.add p (sig ++ [(q, l1, s)], Tk) gam)))).
                apply e_recv with (s := s') (s' := s1) (xs := ys). easy. easy. easy.
                rewrite M.add_spec2. rewrite H5. easy.
                rewrite String.eqb_sym. rewrite Heq. easy.
                rewrite M.add_spec2. rewrite H1. easy.
                rewrite String.eqb_sym. rewrite Hneq. easy.
              * rewrite H5 in H1b. easy.
           ++ rewrite H1 in H1a. easy. easy.
         + rewrite H0 in H4. easy.
       - subst.
         destruct H1 as (g'', H1).
         assert(ls p q l1 = ls p q l1 ) by easy.
         assert((exists g' : ctx, red g1 (lr r r' l2) g') ).
         { exists g''.
           apply e_struct with (g1 := g) (g1' := g'').
           easy. easy. easy.
         }
         specialize(IHred H H0).
         destruct IHred as (g''', H3').
         exists g'''.
         apply e_struct with (g1 := g1') (g1' := g'''); easy.
Qed.

Lemma _B_2_2a: forall g g' g'' p q r l l' l1 l2,
  l1 = lr p q l ->
  l2 = ls p r l' ->
  red g l1 g' -> red g l2 g'' -> False.
Proof. intros.
       specialize (_B_2_1a g g'' g' p r q l' l l2 l1); intros.
       apply H3; easy.
Qed.

Lemma _B_2_2ad: forall g g' g'' p q r l l' l1 l2,
  r <> q ->
  l1 = lr p q l ->
  l2 = lr p r l' ->
  red g l1 g' -> red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H1 H3.
       induction H2; intros.
       - inversion H0. subst.
         apply red_rcv_inv with (p := p) (r := r) (l' := l') in H7.
         destruct H7 as (ys,(s1,(t1,(s2,(sig,(H7a, H7b)))))).
         destruct( M.find p gam). destruct p0.
         destruct H5. destruct H7a.
         rewrite H6 in H7. inversion H7. subst. easy. easy. easy.
       - easy.
       - subst.
         apply IHred with (l2 := lr p r l') (g'' := g''). easy. easy.
         apply cong_red with (g' := g1) in H5; easy.
Qed.

Lemma _B_2_2adl: forall g g' g'' p q l l' l1 l2,
  l <> l' ->
  l1 = lr p q l ->
  l2 = lr p q l' ->
  red g l1 g' -> red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H1 H3.
       induction H2; intros.
       - inversion H0. subst.
         apply red_rcv_inv with (p := p) (r := q) (l' := l') in H7.
         destruct H7 as (ys,(s1,(t1,(s2,(sig,(H7a, H7b)))))).
         destruct(M.find p gam). destruct p0.
         destruct H5. destruct H7a.
         rewrite H6 in H7. inversion H7. subst. 
         destruct(M.find q gam). destruct p0.
         destruct H4.
         destruct H7b.
         rewrite H4 in H10.
         inversion H10. 
         rewrite app_nil_r in H13.
         rewrite H12 in H13. inversion H13. subst. easy.
         rewrite app_nil_l in H12.
         rewrite H12 in H13. inversion H13. subst. easy.
         rewrite <- app_assoc in H14.
         rewrite H13 in H14. inversion H14. subst. easy.
         destruct q0.
         rewrite app_nil_l in H12. rewrite app_nil_l in H13.
         inversion H12. inversion H13. subst. easy.
         inversion H12. inversion H13. subst. inversion H18. subst. easy.
         easy. easy. easy.
       - easy.
       - subst.
         apply IHred with (l2 := lr p q l') (g'' := g''). easy. easy.
         apply cong_red with (g' := g1) in H5; easy.
Qed.

Lemma _B_2_2b: forall g p q r r' lb1 lb2 l1 l2,
  lb1 = lr p q l1 -> 
  lb2 = ls r r' l2 ->
  (exists g', red g lb2 g') -> (forall g', red g lb1 g' -> exists g'', red g' lb2 g'').
Proof. intros.
       case_eq(String.eqb r p); intros Hneq.
       rewrite String.eqb_eq in Hneq. subst. 
       destruct H1.
       assert((lr p q l1) = (lr p q l1)) by easy.
       assert(ls p r' l2 = ls p r' l2) by easy.
       specialize(_B_2_1a g x g' p r' q l2 l1 (ls p r' l2) (lr p q l1) H1 H0 H H2); intros. easy.
       induction H2; intros.
       - inversion H. subst.
         destruct H1 as (g'',H1).
         apply red_snd_inv with (p := r) (r := r') (l' := l2) in H1.
         destruct H1 as (ys, (s1, (t1, H1))).
         case_eq(M.find r gam); intros.
         + destruct p0 as (c2, t2).
           rewrite H0 in H1.
           case_eq(String.eqb r q); intros Heq.
           rewrite String.eqb_eq in Heq. subst.
           rewrite H0 in H5.
           exists(M.add q ((sigp ++ ([(r',l2,s1)])), t1) ((M.add q (sigp, Tp) (M.add p (sigq, Tk) gam)))).
           apply e_send with (xs := ys). easy. easy. 
           rewrite M.add_spec1. split. easy. 
           destruct H5. rewrite <- H7. easy.
           exists(M.add r ((c2 ++ ([(r',l2,s1)])), t1) ((M.add q (sigp, Tp) (M.add p (sigq, Tk) gam)))).
           apply e_send with (xs := ys). easy. easy. 
           rewrite M.add_spec2. rewrite M.add_spec2. rewrite H0.
           easy.
           rewrite String.eqb_sym. rewrite Hneq. easy.
           rewrite String.eqb_sym. rewrite Heq. easy.
         + rewrite H0 in H1. easy.
         easy.
         easy.
       - destruct H1 as (g'', H1).
         subst.
         assert(lr p q l1 = lr p q l1) by easy.
         assert(exists g' : ctx, red g1 (ls r r' l2) g').
         { exists g''. 
           apply e_struct with (g1 := g) (g1' := g'').
           easy. easy. easy.
         }
         specialize(IHred H H0).
         destruct IHred as (g''', H3').
         exists g'''.
         apply e_struct with (g1 := g1') (g1' := g'''); easy.
Qed.

Lemma _B_2_2c: forall g p q r r' lb1 lb2 l1 l2,
  p <> r ->
  lb1 = lr p q l1 -> 
  lb2 = lr r r' l2 ->
  (exists g', red g lb2 g') -> (forall g', red g lb1 g' -> exists g'', red g' lb2 g'').
Proof. intros.
       induction H3; intros.
       - inversion H0. subst.
         destruct H2 as (g'',H2).
         apply red_rcv_inv with (p := r) (r := r') (l' := l2) in H2.
         destruct H2 as (ys, (s1, (t1, (s2, (sig, (H2a, H2b)))))).
         case_eq(M.find r gam); intros.
         + destruct p0 as (c2, t2).
           rewrite H1 in H2a.
           case_eq(M.find r' gam); intros.
           ++ destruct p0 as (c3,t3).
              rewrite H2 in H2b.
              case_eq(String.eqb r' q); intros.
              * rewrite String.eqb_eq in H8. subst.
                rewrite H2 in H6.
                destruct H6 as (H6a,H6b).
                destruct H2b as (H2b1,(H2b2,H2b3)).
                rewrite H6a in H2b1.
                inversion H2b1.
                rewrite app_nil_r in H8. rewrite H6 in H8. inversion H8. subst. easy.
                rewrite app_nil_l in H6. rewrite H6 in H8. inversion H8. subst. easy.
                rewrite <- app_assoc in H9. rewrite H9 in H8. inversion H8. subst. easy.
                case_eq(q0); intros.
                ** subst. rewrite app_nil_l in H6. rewrite app_nil_l in H8.
                   inversion H6. subst. inversion H8. subst.
                   exists(M.add q (q', t3) (M.add r (c2, t1) (M.add q ((r, l2, s2) :: q', Tp) (M.add p (sigq, Tk) gam)))).
                   apply e_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                   rewrite M.add_spec1. easy.
                   rewrite M.add_spec2. rewrite M.add_spec2. rewrite H1. easy.
                   apply String.eqb_neq in H. rewrite H. easy.
                   apply String.eqb_neq in H2b3. rewrite String.eqb_sym. rewrite H2b3. easy.
               ** subst.
                  inversion H8. inversion H6. subst. inversion H13. subst. easy.
               case_eq(String.eqb r' p); intros.
               * rewrite String.eqb_eq in H9. subst.
                 rewrite H2 in H7.
                 case_eq(String.eqb r q); intros.
                 ** rewrite String.eqb_eq in H9. subst.
                    rewrite H1 in H6.
                    exists(M.add p (sig, Tk) (M.add q (sigp, t1) (M.add q (sigp, Tp) (M.add p (sigq, Tk) gam)))).
                    apply e_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                    rewrite M.add_spec2. rewrite M.add_spec1. 
                    destruct H7 as (H7a,H7b).
                    rewrite <- H7a. easy.
                    apply String.eqb_neq in H3. rewrite H3. easy.
                    rewrite M.add_spec1. 
                    destruct H6 as (H6a,H6b).
                    rewrite <- H6b. easy.
                 ** exists(M.add p (sig, Tk) (M.add r (c2, t1) (M.add q (sigp, Tp) (M.add p (sigq, Tk) gam)))).
                    apply e_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                    rewrite M.add_spec2. rewrite M.add_spec1.
                    destruct H7 as (H7a,H7b).
                    rewrite <- H7a. easy.
                    rewrite String.eqb_sym. rewrite H8. easy.
                    rewrite M.add_spec2. rewrite M.add_spec2.
                    rewrite H1.
                    easy.
                    apply String.eqb_neq in H. rewrite H. easy.
                    rewrite String.eqb_sym. rewrite H9. easy.
                 * case_eq(String.eqb r q); intros.
                   ** rewrite String.eqb_eq in H10. subst.
                      rewrite H1 in H6. 
                      exists(M.add r' (sig, t3) (M.add q (sigp, t1) (M.add q (sigp, Tp) (M.add p (sigq, Tk) gam)))).
                      apply e_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                      rewrite M.add_spec2. rewrite M.add_spec2.
                      rewrite H2. easy.
                      rewrite String.eqb_sym. rewrite H9. easy.
                      rewrite String.eqb_sym. rewrite H8. easy.
                      rewrite M.add_spec1.
                      destruct H6 as (H6a,H6b).
                      rewrite <- H6b. easy.
                   ** exists(M.add r' (sig, t3) (M.add r (c2, t1) (M.add q (sigp, Tp) (M.add p (sigq, Tk) gam)))).
                      apply e_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                      rewrite M.add_spec2. rewrite M.add_spec2.
                      rewrite H2. easy.
                      rewrite String.eqb_sym. rewrite H9. easy.
                      rewrite String.eqb_sym. rewrite H8. easy.
                      rewrite M.add_spec2. rewrite M.add_spec2.
                      rewrite H1. easy.
                      apply String.eqb_neq in H. rewrite H. easy.
                      rewrite String.eqb_sym. rewrite H10. easy.
                      rewrite H2 in H2b. easy.
                      rewrite H1 in H2a. easy.
                      easy.
       - easy.
       - destruct H2 as (g'', H2).
         subst.
         assert(lr p q l1 = lr p q l1) by easy.
         assert(exists g' : ctx, red g1 (lr r r' l2) g').
         { exists g''. 
           apply e_struct with (g1 := g) (g1' := g'').
           easy. easy. easy.
         }
         specialize(IHred H0 H1).
         destruct IHred as (g''', H3').
         exists g'''.
         apply e_struct with (g1 := g1') (g1' := g'''); easy.
Qed.

(* Fixpoint cnth {A: Type} (n: nat) (c: coseq A): option A :=
  match n with
    | O   => 
      match c with
        | conil       => None
        | cocons x xs => Some x
      end
    | S k =>
      match c with
        | conil       => None
        | cocons x xs => cnth k xs
      end
  end.

Definition Fairness pt := 
  (forall p q l, enabled (redE (ls p q l)) pt -> 
   exists k l',
     match (cnth k pt, cnth (S k) pt) with
       | (Some g, Some g') => red (fst g) (ls p q l') (fst g')
       | _                 => False 
     end
   )
   /\
  (forall p q l, enabled (redE (lr p q l)) pt -> 
   exists k,
     match (cnth k pt, cnth (S k) pt) with
       | (Some g, Some g') => red (fst g) (lr p q l) (fst g')
       | _                 => False 
     end
   ).

Definition FairPath pt := alwaysC Fairness pt. *)

Lemma _B_3: forall g lb1 g' lb2 pt, 
  red g lb1 g' -> 
  fairPathC (cocons (g', lb2) pt) -> 
  fairPathC (cocons (g, lb1) (cocons (g', lb2) pt)).
Proof. intros.
       pinversion H0.
       - subst.
         pfold. constructor.
         destruct H3 as (H3a, H3b).
         split.
         + intros. simpl in H1.
           case_eq lb1; intros.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              case_eq(String.eqb r p); intros.
              * rewrite String.eqb_eq in H3. subst.
                exists l'. 
                pfold. apply evh. simpl.
                case_eq (String.eqb q r'); intros.
                ** rewrite !String.eqb_refl. easy.
                ** apply String.eqb_neq in H2.
                   destruct H1 as (g'', H1).
                   assert(r' <> q) by easy.
                   assert(ls p q l = ls p q l) by easy.
                   assert(ls p r' l' = ls p r' l') by easy.
                   specialize(_B_2_1ad g g'' g' p q r' l l' (ls p q l) (ls p r' l') H3 H5 H6 H1 H); intros HH.
                   easy.
              * (* specialize(H3a r r' l). *)
                simpl in H1. apply String.eqb_neq in H3.
                assert(ls r r' l' = ls r r' l') by easy.
                assert(ls p q l = ls p q l) by easy.
                destruct H1 as (g'',H1).
                assert((exists g' : ctx, red g (ls p q l) g')).
                { exists g''. easy. }
                subst.
                specialize(_B_2_1b g r r' p q (ls r r' l') (ls p q l) l' l H3 H5 H6 H7 g' H); intro HH.
                specialize(H3a p q l).
                assert(enabled (redE (ls p q l)) (cocons (g', lb2) pt) ).
                { simpl. destruct HH as (g''', HH). exists g'''. easy. }
                apply H3a in H2.
                destruct H2 as (l1, H2).
                exists l1. pfold.
                apply evc. left. easy.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              assert(lr r r' l' = lr r r' l') by easy.
              assert(ls p q l = ls p q l) by easy.
              destruct H1 as (g'',H1).
              assert((exists g' : ctx, red g (ls p q l) g')).
              { exists g''. easy. }
              subst.
              specialize(_B_2_2b g r r' p q (lr r r' l') (ls p q l) l' l H3 H5 H6 g' H); intro HH.
              specialize(H3a p q l).
              assert(enabled (redE (ls p q l)) (cocons (g', lb2) pt) ).
              { simpl. destruct HH as (g''', HH). exists g'''. easy. }
              apply H3a in H2.
              destruct H2 as (l1, H2).
              exists l1. pfold.
              apply evc. left. easy.
         + intros. simpl in H1.
           case_eq lb1; intros.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              assert(ls r r' l' = ls r r' l') by easy.
              assert(lr p q l = lr p q l) by easy.
              destruct H1 as (g'',H1).
              assert((exists g' : ctx, red g (lr p q l) g')).
              { exists g''. easy. }
              subst.
              specialize(_B_2_1c g r r' p q (ls r r' l') (lr p q l) l' l H3 H5 H6 g' H); intro HH.
              specialize(H3b p q l).
              assert(enabled (redE (lr p q l)) (cocons (g', lb2) pt) ).
              { simpl. destruct HH as (g''', HH). exists g'''. easy. }
              apply H3b in H2.
              pfold.
              apply evc. left. easy.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              case_eq(String.eqb r p); intros.
              * rewrite String.eqb_eq in H3. subst.
                pfold. apply evh. simpl.
                case_eq(String.eqb q r'); intros.
                ** case_eq(String.eqb l l'); intros.
                   *** rewrite !String.eqb_refl. easy.
                   *** destruct H1 as (g'',H1).
                       rewrite String.eqb_eq in H2. subst.
                       apply String.eqb_neq in H3.
                       specialize(_B_2_2adl g g'' g' p r' l l' (lr p r' l) (lr p r' l') H3); intro HH.
                       destruct HH; easy.
                ** destruct H1 as (g'',H1).
                   rewrite String.eqb_neq in H2.
                   specialize(_B_2_2ad g g'' g' p q r' l l' (lr p q l) (lr p r' l')); intro HH.
                   destruct HH; easy.
              * simpl in H1. apply String.eqb_neq in H3.
                assert(lr r r' l' = lr r r' l') by easy.
                assert(lr p q l = lr p q l) by easy.
                destruct H1 as (g'',H1).
                assert((exists g' : ctx, red g (lr p q l) g')).
                { exists g''. easy. }
                subst.
                specialize(_B_2_2c g r r' p q (lr r r' l') (lr p q l) l' l H3 H5 H6 H7 g' H); intro HH.
                specialize(H3b p q l).
                assert(enabled (redE (lr p q l)) (cocons (g', lb2) pt) ).
                { simpl. destruct HH as (g''', HH). exists g'''. easy. }
                apply H3b in H2.
                pfold.
                apply evc. left. easy.
       left. pfold. easy.
       apply mon_alw.
Qed.

Lemma _4_9: forall g l g', live g -> red g l g' -> live g'.
Proof. unfold live.
       intros.
       specialize(H (cocons (g', l0) pt) l).
       apply _B_3 with (g := g) (lb1 := l) in H1; try easy.
       apply H in H1.
       pinversion H1.
       subst. pfold.
       pinversion H5.
       apply mon_alw.
       apply mon_alw.
Qed.


(*for trees*)

Require Import ST.src.st.

Module T  := MMaps.WeakList.Make(SS).
Module TF := MMaps.Facts.Properties SS M. 

Definition Ctx: Type := T.t (queue*st).

Notation TPath := (coseq (Ctx*lab)) (only parsing).

Definition Enqueued (p q: participant) (l: label) (s: local.sort) (pt: TPath): Prop :=
  match pt with
    | cocons (g, tl) (cocons (g',tl') xs) =>
      match (T.find p g, T.find q g, T.find p g', T.find q g') with
        | (Some (((a,b,c)::sigp'), Tp'), Some (sigq, st_receive d ys), Some (q3, T3), Some (q4, T4)) => 
           a = q /\ b = l /\ c = s /\ d = p /\ qCong q3 sigp' /\ T4 = Tp' /\ qCong q4 sigq /\ (exists k s, copathsel k s ys T4)
        | _                                                                                          => False 
      end
    | _                => False 
  end.

Definition Dequeued (p q: participant) sigp ys (pt: TPath): Prop :=
  match pt with
    | cocons (g, tl) (cocons (g',tl') xs) =>
      match (T.find p g, T.find q g, T.find p g', T.find q g') with
        | (Some (q1, Tp), Some (((a,l,s)::sig'), Tq), Some (q3, T3), Some (q4, T4)) => 
          a = p /\ qCong q1 sigp /\ qCong q3 sigp /\ qCong q4 sig' /\ Tp = st_receive q ys /\ Tq = T4 /\ copathsel l s ys T3
        | _                                                                         => False 
      end
    | _                => False 
  end. 

Inductive Red: Ctx -> lab -> Ctx -> Prop :=
  | E_recv  : forall p q sigp sigq gam l Tp s s' Tk xs,
              p <> q ->
              copathsel l s xs Tk ->
              subsort s' s ->
              (
                match T.find p gam with
                  | Some (sig', T') => qCong sig' ((q,l,s')::sigp) /\ T' = Tp
                  | _               => False 
                end
              ) ->
              (
                match T.find q gam with
                  | Some (sig', T') => qCong sig' sigq /\ T' = (st_receive p xs)
                  | None            => False
                end
              ) ->
              Red gam (lr q p l) (T.add p (sigp, Tp) (T.add q (sigq, Tk) gam))
  | E_send  : forall p q sig gam l s Tk xs,
              p <> q ->
              copathsel l s xs Tk ->
              (
                match T.find p gam with
                 | Some (sig', T') => qCong sig' sig /\ T' = (st_send q xs)
                 | _               => False
                end
              ) ->
              Red gam (ls p q l) (T.add p ((sig ++ [(q,l,s)]), Tk) gam).

Definition HPR (p q: participant) (l: label) (pt: TPath): Prop :=
  match pt with
    | cocons (g, (lr a b l')) xs => if andb (String.eqb p a) (andb (String.eqb q b) (String.eqb l l')) then True else False
    | _                          => False 
  end.

Definition HPS (p q: participant) (l: label) (pt: TPath): Prop :=
  match pt with
    | cocons (g, (ls a b l')) xs => if andb (String.eqb p a) (andb (String.eqb q b) (String.eqb l l')) then True else False
    | _                          => False 
  end.

Definition Enabled (F: Ctx -> Prop) (pt: TPath): Prop :=
  match pt with
    | cocons (g, l) xs => F g
    | _                => False 
  end.

Definition RedE l g := exists g', Red g l g'.

Definition FairPath (pt: TPath): Prop :=
  (forall p q l, Enabled (RedE (ls p q l)) pt -> exists l', eventuallyC (HPS p q l') pt) /\
  (forall p q l, Enabled (RedE (lr p q l)) pt -> eventuallyC (HPR p q l) pt).

Definition FairPathC (pt: TPath) := (* pathRedC pt /\ *) alwaysC FairPath pt.

Inductive pLiveness (R: Ctx -> participant -> Prop): Ctx -> participant -> Prop :=
  | lpR: forall p gam,
         (
           match T.find p gam with
             | Some (sigp, st_receive q ys) => forall l pt, FairPathC (cocons (gam, l) pt) -> eventuallyC (Dequeued p q sigp ys) (cocons (gam, l) pt)
             | _                            => False
           end
         ) -> pLiveness R gam p
  | lpS: forall p gam,
         (
           match T.find p gam with
             | Some ((q,l,s)::sigp, Tp)     => forall lb pt, FairPathC (cocons (gam, lb) pt) -> eventuallyC (Enqueued p q l s) (cocons (gam, lb) pt)
             | _                            => False
           end
         ) -> pLiveness R gam p
  | lpC: forall gam l gam' p, Red gam l gam' -> R gam' p -> pLiveness R gam p.

Definition pLivenessC g p := paco2 pLiveness bot2 g p.

Definition Live g := forall p, T.mem p g -> pLivenessC g p.

Lemma Red_snd_inv: forall g g' p r l l',
  l = ls p r l' -> 
  Red g l g' ->
  exists ys s t,
  match T.find p g with
    | Some (que, T) => T = (st_send r ys) /\ copathsel l' s ys t /\ p <> r
    | _             => False
  end.
Proof. intros.
       induction H0; intros.
       - easy.
       - inversion H. subst.
         exists xs. exists s. exists Tk.
         destruct(T.find p gam). destruct p0. easy. easy.
Qed.

Lemma Red_rcv_inv: forall g g' p r l l',
  l = lr p r l' -> 
  Red g l g' ->
  exists ys s t s' sigp,
  match T.find p g with
    | Some (que, T) => T = (st_receive r ys) /\ copathsel l' s ys t /\ p <> r
    | _             => False
  end /\
  match T.find r g with
    | Some (que, T) => qCong que ((p,l',s')::sigp) /\ subsort s' s /\ p <> r
    | _             => False
  end.
Proof. intros.
       induction H0; intros.
       - inversion H. subst.
         destruct (T.find p gam). destruct p0.
         exists xs. exists s. exists Tk. exists s'. exists sigp. split. easy.
         destruct (T.find r gam). destruct p0.
         easy. easy. easy.
       - easy.
Qed.

Lemma _B_2_1A: forall g g' g'' p q r l l' l1 l2,
  l1 = ls p q l ->
  l2 = lr p r l' ->
  Red g l1 g' -> Red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H0 H2.
       induction H1; intros.
       - easy.
       - inversion H. subst.
         apply Red_rcv_inv with (p := p) (r := r) (l' := l') in H4.
         destruct H4 as (ys,(s1,(t1,(s2,(sigp,(H4a, H4b)))))).
         destruct(T.find p gam). destruct p0.
         destruct H4a. rewrite H3 in H2. easy. easy. easy.
Qed.

Lemma _B_2_1AD: forall g g' g'' p q r l l' l1 l2,
  r <> q ->
  l1 = ls p q l ->
  l2 = ls p r l' ->
  Red g l1 g' -> Red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H1 H3.
       induction H2; intros.
       - easy.
       - inversion H0. subst.
         apply Red_snd_inv with (p := p) (r := r) (l' := l') in H5.
         destruct H5 as (ys,(s1,(t1,H5))).
         destruct(T.find p gam). destruct p0.
         destruct H3. destruct H5.
         rewrite H4 in H5. inversion H5. subst. easy. easy. easy.
Qed.

Lemma _B_2_1B: forall g p q r r' lb1 lb2 l1 l2,
  p <> r ->
  lb1 = ls p q l1 -> 
  lb2 = ls r r' l2 ->
  (exists g', Red g lb2 g') -> (forall g', Red g lb1 g' -> exists g'', Red g' lb2 g'').
Proof. intros.
       induction H3; intros.
       - easy.
       - inversion H0. subst.
         destruct H2 as (g'',H2).
         apply Red_snd_inv with (p := r) (r := r') (l' := l2) in H2.
         destruct H2 as (ys, (s', (t', H2))).
         case_eq(T.find r gam); intros.
         + destruct p0 as (c1, t1).
           rewrite H1 in H2.
           exists(T.add r (c1++[(r',l2,s')], t') ((T.add p (sig ++ [(q, l1, s)], Tk) gam))).
           apply E_send with (xs := ys). easy. easy.
           rewrite T.add_spec2. rewrite H1. easy.
           apply String.eqb_neq in H. rewrite H. easy.
           rewrite H1 in H2. easy.
           easy.
Qed.

Lemma _B_2_1C: forall g p q r r' lb1 lb2 l1 l2,
  lb1 = ls p q l1 -> 
  lb2 = lr r r' l2 ->
  (exists g', Red g lb2 g') -> (forall g', Red g lb1 g' -> exists g'', Red g' lb2 g'').
Proof. intros.
       case_eq(String.eqb r p); intros Hneq.
       rewrite String.eqb_eq in Hneq. subst. 
       destruct H1.
       assert((ls p q l1) = (ls p q l1)) by easy.
       assert(lr p r' l2 = lr p r' l2) by easy.
       specialize(_B_2_1A g g' x p q r' l1 l2 (ls p q l1) (lr p r' l2) H0 H1 H2 H); intros. easy.
       induction H2; intros.
       - easy.
       - inversion H. subst. 
         case_eq(T.find p gam); intros.
         + destruct p0 as (c1, t1).
           destruct H1 as (g',H1).
           rewrite H0 in H4.
           apply Red_rcv_inv with (p := r) (r := r') (l' := l2) in H1.
           destruct H1 as (ys,(s',(t',(s1,(sigp,(H1a, H1b)))))).
           case_eq(T.find r gam); intros.
           ++ destruct p0 as (c2, t2).
              rewrite H1 in H1a.
              case_eq(String.eqb r' p); intros Heq.
              rewrite String.eqb_eq in Heq. subst.
              rewrite H0 in H1b.
              exists(T.add p ((sigp++[(q, l1, s)]), Tk) (T.add r (c2,t') ((T.add p (sig ++ [(q, l1, s)], Tk) gam)))).
              apply E_recv with (s := s') (s' := s1) (xs := ys). easy. easy. easy.
              rewrite T.add_spec1. 
              destruct H4 as (H4a, H4b). 
              destruct H1b as (H1b,H1b1).
              rewrite H4a in H1b.
              apply qcong_app with (a := (q, l1, s)) in H1b. easy.
              rewrite T.add_spec2. rewrite H1. easy.
              rewrite String.eqb_sym. rewrite Hneq. easy.
              case_eq(T.find r' gam); intros.
              * destruct p0 as (c3,t3).
                rewrite H5 in H1b.
                destruct H1b as (H1b1,(H1b2,H1b3)).
                exists(T.add r' (sigp, t3) (T.add r (c2,t') ((T.add p (sig ++ [(q, l1, s)], Tk) gam)))).
                apply E_recv with (s := s') (s' := s1) (xs := ys). easy. easy. easy.
                rewrite T.add_spec2. rewrite H5. easy.
                rewrite String.eqb_sym. rewrite Heq. easy.
                rewrite T.add_spec2. rewrite H1. easy.
                rewrite String.eqb_sym. rewrite Hneq. easy.
              * rewrite H5 in H1b. easy.
           ++ rewrite H1 in H1a. easy. easy.
         + rewrite H0 in H4. easy.
Qed.

Lemma _B_2_2A: forall g g' g'' p q r l l' l1 l2,
  l1 = lr p q l ->
  l2 = ls p r l' ->
  Red g l1 g' -> Red g l2 g'' -> False.
Proof. intros.
       specialize (_B_2_1A g g'' g' p r q l' l l2 l1); intros.
       apply H3; easy.
Qed.

Lemma _B_2_2AD: forall g g' g'' p q r l l' l1 l2,
  r <> q ->
  l1 = lr p q l ->
  l2 = lr p r l' ->
  Red g l1 g' -> Red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H1 H3.
       induction H2; intros.
       - inversion H0. subst.
         apply Red_rcv_inv with (p := p) (r := r) (l' := l') in H7.
         destruct H7 as (ys,(s1,(t1,(s2,(sig,(H7a, H7b)))))).
         destruct(T.find p gam). destruct p0.
         destruct H5. destruct H7a.
         rewrite H6 in H7. inversion H7. subst. easy. easy. easy.
       - easy.
Qed.

Lemma _B_2_2ADL: forall g g' g'' p q l l' l1 l2,
  l <> l' ->
  l1 = lr p q l ->
  l2 = lr p q l' ->
  Red g l1 g' -> Red g l2 g'' -> False.
Proof. intros.
       revert l2 g'' H1 H3.
       induction H2; intros.
       - inversion H0. subst.
         apply Red_rcv_inv with (p := p) (r := q) (l' := l') in H7.
         destruct H7 as (ys,(s1,(t1,(s2,(sig,(H7a, H7b)))))).
         destruct(T.find p gam). destruct p0.
         destruct H5. destruct H7a.
         rewrite H6 in H7. inversion H7. subst. 
         destruct(T.find q gam). destruct p0.
         destruct H4.
         destruct H7b.
         rewrite H4 in H9.
         inversion H9. 
         rewrite app_nil_r in H12.
         rewrite H11 in H12. inversion H12. subst. easy.
         rewrite app_nil_l in H11.
         rewrite H11 in H12. inversion H12. subst. easy.
         rewrite <- app_assoc in H13.
         rewrite H12 in H13. inversion H13. subst. easy.
         destruct q0.
         rewrite app_nil_l in H11. rewrite app_nil_l in H12.
         inversion H11. inversion H12. subst. easy.
         inversion H11. inversion H12. subst. inversion H17. subst. easy.
         easy. easy. easy.
       - easy.
Qed.

Lemma _B_2_2B: forall g p q r r' lb1 lb2 l1 l2,
  lb1 = lr p q l1 -> 
  lb2 = ls r r' l2 ->
  (exists g', Red g lb2 g') -> (forall g', Red g lb1 g' -> exists g'', Red g' lb2 g'').
Proof. intros.
       case_eq(String.eqb r p); intros Hneq.
       rewrite String.eqb_eq in Hneq. subst. 
       destruct H1.
       assert((lr p q l1) = (lr p q l1)) by easy.
       assert(ls p r' l2 = ls p r' l2) by easy.
       specialize(_B_2_1A g x g' p r' q l2 l1 (ls p r' l2) (lr p q l1) H1 H0 H H2); intros. easy.
       induction H2; intros.
       - inversion H. subst.
         destruct H1 as (g'',H1).
         apply Red_snd_inv with (p := r) (r := r') (l' := l2) in H1.
         destruct H1 as (ys, (s1, (t1, H1))).
         case_eq(T.find r gam); intros.
         + destruct p0 as (c2, t2).
           rewrite H0 in H1.
           case_eq(String.eqb r q); intros Heq.
           rewrite String.eqb_eq in Heq. subst.
           rewrite H0 in H5.
           exists(T.add q ((sigp ++ ([(r',l2,s1)])), t1) ((T.add q (sigp, Tp) (T.add p (sigq, Tk) gam)))).
           apply E_send with (xs := ys). easy. easy. 
           rewrite T.add_spec1. split. easy. 
           destruct H5. rewrite <- H7. easy.
           exists(T.add r ((c2 ++ ([(r',l2,s1)])), t1) ((T.add q (sigp, Tp) (T.add p (sigq, Tk) gam)))).
           apply E_send with (xs := ys). easy. easy. 
           rewrite T.add_spec2. rewrite T.add_spec2. rewrite H0.
           easy.
           rewrite String.eqb_sym. rewrite Hneq. easy.
           rewrite String.eqb_sym. rewrite Heq. easy.
         + rewrite H0 in H1. easy.
         easy.
         easy.
Qed.

Lemma _B_2_2C: forall g p q r r' lb1 lb2 l1 l2,
  p <> r ->
  lb1 = lr p q l1 -> 
  lb2 = lr r r' l2 ->
  (exists g', Red g lb2 g') -> (forall g', Red g lb1 g' -> exists g'', Red g' lb2 g'').
Proof. intros.
       induction H3; intros.
       - inversion H0. subst.
         destruct H2 as (g'',H2).
         apply Red_rcv_inv with (p := r) (r := r') (l' := l2) in H2.
         destruct H2 as (ys, (s1, (t1, (s2, (sig, (H2a, H2b)))))).
         case_eq(T.find r gam); intros.
         + destruct p0 as (c2, t2).
           rewrite H1 in H2a.
           case_eq(T.find r' gam); intros.
           ++ destruct p0 as (c3,t3).
              rewrite H2 in H2b.
              case_eq(String.eqb r' q); intros.
              * rewrite String.eqb_eq in H8. subst.
                rewrite H2 in H6.
                destruct H6 as (H6a,H6b).
                destruct H2b as (H2b1,(H2b2,H2b3)).
                rewrite H6a in H2b1.
                inversion H2b1.
                rewrite app_nil_r in H8. rewrite H6 in H8. inversion H8. subst. easy.
                rewrite app_nil_l in H6. rewrite H6 in H8. inversion H8. subst. easy.
                rewrite <- app_assoc in H9. rewrite H9 in H8. inversion H8. subst. easy.
                case_eq(q0); intros.
                ** subst. rewrite app_nil_l in H6. rewrite app_nil_l in H8.
                   inversion H6. subst. inversion H8. subst.
                   exists(T.add q (q', Tp) (T.add r (c2, t1) (T.add q ((r, l2, s2) :: q', Tp) (T.add p (sigq, Tk) gam)))).
                   apply E_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                   rewrite T.add_spec1. easy.
                   rewrite T.add_spec2. rewrite T.add_spec2. rewrite H1. easy.
                   apply String.eqb_neq in H. rewrite H. easy.
                   apply String.eqb_neq in H2b3. rewrite String.eqb_sym. rewrite H2b3. easy.
               ** subst.
                  inversion H8. inversion H6. subst. inversion H13. subst. easy.
               case_eq(String.eqb r' p); intros.
               * rewrite String.eqb_eq in H9. subst.
                 rewrite H2 in H7.
                 case_eq(String.eqb r q); intros.
                 ** rewrite String.eqb_eq in H9. subst.
                    rewrite H1 in H6.
                    exists(T.add p (sig, Tk) (T.add q (sigp, t1) (T.add q (sigp, Tp) (T.add p (sigq, Tk) gam)))).
                    apply E_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                    rewrite T.add_spec2. rewrite T.add_spec1. 
                    destruct H7 as (H7a,H7b).
                    rewrite <- H7a. easy.
                    apply String.eqb_neq in H3. rewrite H3. easy.
                    rewrite T.add_spec1. 
                    destruct H6 as (H6a,H6b).
                    rewrite <- H6b. easy.
                 ** exists(T.add p (sig, Tk) (T.add r (c2, t1) (T.add q (sigp, Tp) (T.add p (sigq, Tk) gam)))).
                    apply E_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                    rewrite T.add_spec2. rewrite T.add_spec1.
                    destruct H7 as (H7a,H7b).
                    rewrite <- H7a. easy.
                    rewrite String.eqb_sym. rewrite H8. easy.
                    rewrite T.add_spec2. rewrite T.add_spec2.
                    rewrite H1.
                    easy.
                    apply String.eqb_neq in H. rewrite H. easy.
                    rewrite String.eqb_sym. rewrite H9. easy.
                 * case_eq(String.eqb r q); intros.
                   ** rewrite String.eqb_eq in H10. subst.
                      rewrite H1 in H6. 
                      exists(T.add r' (sig, t3) (T.add q (sigp, t1) (T.add q (sigp, Tp) (T.add p (sigq, Tk) gam)))).
                      apply E_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                      rewrite T.add_spec2. rewrite T.add_spec2.
                      rewrite H2. easy.
                      rewrite String.eqb_sym. rewrite H9. easy.
                      rewrite String.eqb_sym. rewrite H8. easy.
                      rewrite T.add_spec1.
                      destruct H6 as (H6a,H6b).
                      rewrite <- H6b. easy.
                   ** exists(T.add r' (sig, t3) (T.add r (c2, t1) (T.add q (sigp, Tp) (T.add p (sigq, Tk) gam)))).
                      apply E_recv with (s := s1) (s' := s2) (xs := ys). easy. easy. easy.
                      rewrite T.add_spec2. rewrite T.add_spec2.
                      rewrite H2. easy.
                      rewrite String.eqb_sym. rewrite H9. easy.
                      rewrite String.eqb_sym. rewrite H8. easy.
                      rewrite T.add_spec2. rewrite T.add_spec2.
                      rewrite H1. easy.
                      apply String.eqb_neq in H. rewrite H. easy.
                      rewrite String.eqb_sym. rewrite H10. easy.
                      rewrite H2 in H2b. easy.
                      rewrite H1 in H2a. easy.
                      easy.
       - easy.
Qed.

Lemma _B_3T: forall g lb1 g' lb2 pt, 
  Red g lb1 g' -> 
  FairPathC (cocons (g', lb2) pt) -> 
  FairPathC (cocons (g, lb1) (cocons (g', lb2) pt)).
Proof. intros.
       pinversion H0.
       - subst.
         pfold. constructor.
         destruct H3 as (H3a, H3b).
         split.
         + intros. simpl in H1.
           case_eq lb1; intros.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              case_eq(String.eqb r p); intros.
              * rewrite String.eqb_eq in H3. subst.
                exists l'. 
                pfold. apply evh. simpl.
                case_eq (String.eqb q r'); intros.
                ** rewrite !String.eqb_refl. easy.
                ** apply String.eqb_neq in H2.
                   destruct H1 as (g'', H1).
                   assert(r' <> q) by easy.
                   assert(ls p q l = ls p q l) by easy.
                   assert(ls p r' l' = ls p r' l') by easy.
                   specialize(_B_2_1AD g g'' g' p q r' l l' (ls p q l) (ls p r' l') H3 H5 H6 H1 H); intros HH.
                   easy.
              * (* specialize(H3a r r' l). *)
                simpl in H1. apply String.eqb_neq in H3.
                assert(ls r r' l' = ls r r' l') by easy.
                assert(ls p q l = ls p q l) by easy.
                destruct H1 as (g'',H1).
                assert((exists g' : Ctx, Red g (ls p q l) g')).
                { exists g''. easy. }
                subst.
                specialize(_B_2_1B g r r' p q (ls r r' l') (ls p q l) l' l H3 H5 H6 H7 g' H); intro HH.
                specialize(H3a p q l).
                assert(Enabled (RedE (ls p q l)) (cocons (g', lb2) pt) ).
                { simpl. destruct HH as (g''', HH). exists g'''. easy. }
                apply H3a in H2.
                destruct H2 as (l1, H2).
                exists l1. pfold.
                apply evc. left. easy.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              assert(lr r r' l' = lr r r' l') by easy.
              assert(ls p q l = ls p q l) by easy.
              destruct H1 as (g'',H1).
              assert((exists g' : Ctx, Red g (ls p q l) g')).
              { exists g''. easy. }
              subst.
              specialize(_B_2_2B g r r' p q (lr r r' l') (ls p q l) l' l H3 H5 H6 g' H); intro HH.
              specialize(H3a p q l).
              assert(Enabled (RedE (ls p q l)) (cocons (g', lb2) pt) ).
              { simpl. destruct HH as (g''', HH). exists g'''. easy. }
              apply H3a in H2.
              destruct H2 as (l1, H2).
              exists l1. pfold.
              apply evc. left. easy.
         + intros. simpl in H1.
           case_eq lb1; intros.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              assert(ls r r' l' = ls r r' l') by easy.
              assert(lr p q l = lr p q l) by easy.
              destruct H1 as (g'',H1).
              assert((exists g' : Ctx, Red g (lr p q l) g')).
              { exists g''. easy. }
              subst.
              specialize(_B_2_1C g r r' p q (ls r r' l') (lr p q l) l' l H3 H5 H6 g' H); intro HH.
              specialize(H3b p q l).
              assert(Enabled (RedE (lr p q l)) (cocons (g', lb2) pt) ).
              { simpl. destruct HH as (g''', HH). exists g'''. easy. }
              apply H3b in H2.
              pfold.
              apply evc. left. easy.
           ++ rename s into r. rename s0 into r'. rename s1 into l'.
              case_eq(String.eqb r p); intros.
              * rewrite String.eqb_eq in H3. subst.
                pfold. apply evh. simpl.
                case_eq(String.eqb q r'); intros.
                ** case_eq(String.eqb l l'); intros.
                   *** rewrite !String.eqb_refl. easy.
                   *** destruct H1 as (g'',H1).
                       rewrite String.eqb_eq in H2. subst.
                       apply String.eqb_neq in H3.
                       specialize(_B_2_2ADL g g'' g' p r' l l' (lr p r' l) (lr p r' l') H3); intro HH.
                       destruct HH; easy.
                ** destruct H1 as (g'',H1).
                   rewrite String.eqb_neq in H2.
                   specialize(_B_2_2AD g g'' g' p q r' l l' (lr p q l) (lr p r' l')); intro HH.
                   destruct HH; easy.
              * simpl in H1. apply String.eqb_neq in H3.
                assert(lr r r' l' = lr r r' l') by easy.
                assert(lr p q l = lr p q l) by easy.
                destruct H1 as (g'',H1).
                assert((exists g' : Ctx, Red g (lr p q l) g')).
                { exists g''. easy. }
                subst.
                specialize(_B_2_2C g r r' p q (lr r r' l') (lr p q l) l' l H3 H5 H6 H7 g' H); intro HH.
                specialize(H3b p q l).
                assert(Enabled (RedE (lr p q l)) (cocons (g', lb2) pt) ).
                { simpl. destruct HH as (g''', HH). exists g'''. easy. }
                apply H3b in H2.
                pfold.
                apply evc. left. easy.
       left. pfold. easy.
       apply mon_alw.
Qed.



