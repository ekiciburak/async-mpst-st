Require Import ST.aux.unscoped ST.types.local ST.subtyping.subtyping.
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
  (forall p q l l', enabled (redE (ls p q l)) pt -> eventuallyC (hPS p q l') pt) /\
  (forall p q l,    enabled (redE (lr p q l)) pt -> eventuallyC (hPR p q l) pt).

Definition fairPathC (pt: Path) := pathRedC pt /\ alwaysC fairPath pt.

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


Definition livePathC (pt: Path) := pathRedC pt /\ alwaysC livePath pt.

(* Definition livePathC (pt: path) := alwaysC livePath (@upth pt). *)

Definition live (g: ctx) := forall (pt: Path) (l: lab), fairPathC (cocons (g, l) pt) -> livePathC (cocons (g, l) pt).

Require Import Coq.Program.Equality.

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
       intros. destruct H as (Hr,H).
       pinversion H.
       subst.
       split.
       pinversion Hr. subst.
       pfold. constructor.
       subst. simpl in H6. 
       pfold. constructor. left. easy.
       simpl. eapply cong_red with (g' := g') in H6; easy.
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
       assert(enabled (redE (lr p q l0)) (cocons (g, l) pt)).
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
       destruct Hf as (Hr, Hf).
       pinversion Hf.
       subst. 
       split. 
       pinversion Hr. subst. pfold. constructor. subst. pfold. constructor. left. easy.
       simpl in H7.
       simpl. eapply cong_red with (g' := g') in H7; easy.
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