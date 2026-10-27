Require Import ST.processes.unscoped ST.processes.process ST.types.local ST.subtyping.subtyping ST.types.typenv.
Require Import ST.src.st.
From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import List Datatypes ZArith.
Local Open Scope string_scope.
Import ListNotations.
Import CoListNotations.
From MMaps Require Import MMaps.

Require Import ST.types.typenv.
From Paco Require Import paco.

Definition valid_path_new (pt : Path) : Prop := pathRedC pt.

Definition fair_path_new (pt : Path) : Prop := alwaysC fairPath pt.

Definition live_path_new (pt : Path) : Prop := alwaysC livePath pt.

Definition live_new (g : ctx) : Prop :=
  forall (pt : Path) (l : lab),
    valid_path_new (cocons (g,l) pt) ->
    fair_path_new (cocons (g,l) pt) ->
    live_path_new (cocons (g,l) pt).

Definition proposition_4_9_new_statement : Prop := forall g l g', live_new g -> red g l g' -> live_new g'.

Inductive tree_path_red_new (R : TPath -> Prop) : TPath -> Prop :=
| tpr_nil_new : tree_path_red_new R conil
| tpr_one_new : forall x, tree_path_red_new R (cocons x conil)
| tpr_cons_new : forall x y ys,
    Red (fst x) (snd x) (fst y) ->
    R (cocons y ys) ->
    tree_path_red_new R (cocons x (cocons y ys)).

Definition valid_tree_path_new (pt : TPath) : Prop := paco1 tree_path_red_new bot1 pt.

Definition fair_tree_path_new (pt : TPath) : Prop := valid_tree_path_new pt /\ alwaysC FairPath pt.

Definition input_liveness_new (gam : Ctx) (p : participant) : Prop :=
  match T.find p gam with
  | Some (sigp, st_receive q ys) =>
      forall (lb : lab) (pt : TPath),
        fair_tree_path_new (cocons (gam,lb) pt) ->
        eventuallyC (Dequeued p q sigp ys) (cocons (gam,lb) pt)
  | _ => True
  end.

Definition output_liveness_new (gam : Ctx) (p : participant) : Prop :=
  match T.find p gam with
  | Some ((q,l,s)::sigp, Tp) =>
      forall (lb : lab) (pt : TPath),
        fair_tree_path_new (cocons (gam,lb) pt) ->
        eventuallyC (Enqueued p q l s) (cocons (gam,lb) pt)
  | _ => True
  end.

Inductive pLivenessF_new (R : Ctx -> participant -> Prop): Ctx -> participant -> Prop :=
| lp_intro_new : forall gam p,
    input_liveness_new gam p ->
    output_liveness_new gam p ->
    (forall l gam', Red gam l gam' -> R gam' p) ->
    pLivenessF_new R gam p.

Definition pLivenessC_new (gam : Ctx) (p : participant) : Prop :=  paco2 pLivenessF_new bot2 gam p.

Definition Live_new (gam : Ctx) : Prop := forall p, T.mem p gam -> pLivenessC_new gam p.

Lemma terminated_obligations_new : forall gam p,
  T.find p gam = Some ([], st_end) ->
  input_liveness_new gam p /\ output_liveness_new gam p.
Proof.
  intros gam p H.
  unfold input_liveness_new, output_liveness_new.
  rewrite H. easy.
Qed.

Lemma pLivenessF_new_mon :
  monotone2 pLivenessF_new.
Proof.
  unfold monotone2.
  intros r p R R' Hlive Hinc.
  inversion Hlive; subst.
  constructor.
  - assumption.
  - assumption.
  - intros l gam' Hred.
    apply Hinc.
    eauto.
Qed.

Lemma pLivenessC_new_unfold :
  forall gam p,
    pLivenessC_new gam p ->
    input_liveness_new gam p /\
    output_liveness_new gam p /\
    (forall l gam',
      Red gam l gam' ->
      pLivenessC_new gam' p).
Proof.
  intros gam p Hlive.

  unfold pLivenessC_new in Hlive.
  eapply paco2_unfold in Hlive.
  2: exact pLivenessF_new_mon.

  inversion Hlive as [gam0 p0 Hin Hout Hstep]; subst.

  repeat split.
  - exact Hin.
  - exact Hout.
  - specialize (Hstep l gam' H).
    unfold upaco2 in Hstep.
    destruct Hstep as [Hpaco | Hbot].
    + cbn beta in Hpaco. apply Hpaco.
    + destruct Hbot.
Qed.

Lemma pLivenessC_new_red :
  forall gam gam' p l,
    pLivenessC_new gam p ->
    Red gam l gam' ->
    pLivenessC_new gam' p.
Proof.
  intros gam gam' p l Hlive Hred.
  destruct (pLivenessC_new_unfold gam p Hlive)
    as [_ [_ Hstep]].
  exact (Hstep l gam' Hred).
Qed.


Lemma pLivenessC_new_input :
  forall gam p,
    pLivenessC_new gam p ->
    input_liveness_new gam p.
Proof.
  intros gam p Hlive.
  destruct (pLivenessC_new_unfold gam p Hlive)
    as [Hin [_ _]].
  exact Hin.
Qed.

Lemma pLivenessC_new_output :
  forall gam p,
    pLivenessC_new gam p ->
    output_liveness_new gam p.
Proof.
  intros gam p Hlive.
  destruct (pLivenessC_new_unfold gam p Hlive)
    as [_ [Hout _]].
  exact Hout.
Qed.

From Coq Require Import Strings.String.

Lemma mem_add_existing :
  forall (g : Ctx) k v x,
    T.mem k g ->
    T.mem x (T.add k v g) ->
    T.mem x g.
Proof.
  intros g k v x Hk Hx.
  destruct (string_dec x k) as [Heq | Hneq].
  - subst.
    exact Hk.
  - apply T.mem_spec.
    apply T.mem_spec in Hx.
    destruct Hx as [value Hfind].
    exists value.
    apply T.find_spec.
    apply T.find_spec in Hfind.
    rewrite T.add_spec2 in Hfind.
    - exact Hfind.
    - apply String.eqb_neq in Hneq. rewrite String.eqb_sym in Hneq. rewrite Hneq.
      easy.
Qed.

Lemma Red_mem_preserved :
  forall gam gam' l p,
    Red gam l gam' ->
    T.mem p gam' ->
    T.mem p gam.
Proof.
  intros gam gam' l p Hred Hmem.
  inversion Hred; subst.

  - assert (Hp0 : T.mem p0 gam).
  {
    destruct (T.find p0 gam) eqn:Hfind.
    apply T.mem_spec.
    exists p1.
    eapply T.find_spec.
    exact Hfind.
    contradiction.
  }

  assert (Hq : T.mem q gam).
  {
    destruct (T.find q gam) eqn:Hfind.
    - apply T.mem_spec.
      exists p1.
      apply T.find_spec.
      exact Hfind.
    - simpl in H3.
      contradiction.
  }

  destruct (string_dec p p0) as [Heq1 | Hneq1].
  - subst p.
    exact Hp0.

  - destruct (string_dec p q) as [Heq2 | Hneq2].
    + subst p.
      exact Hq.

    + apply T.mem_spec.
      apply T.mem_spec in Hmem.
      destruct Hmem as [value Hmap].
      exists value.

      apply T.find_spec.
      apply T.find_spec in Hmap.

      rewrite T.add_spec2 in Hmap.
      2:{ apply String.eqb_neq in Hneq1. rewrite String.eqb_sym in Hneq1.
          rewrite Hneq1. easy.
        }

      rewrite T.add_spec2 in Hmap.
      2:{ apply String.eqb_neq in Hneq2. rewrite String.eqb_sym in Hneq2.
          rewrite Hneq2. easy.
        }

      exact Hmap.

      assert (Hp0 : T.mem p0 gam).
      {
        destruct (T.find p0 gam) eqn:Hfind.
        - apply T.mem_spec.
          exists p1.
          apply T.find_spec.
          exact Hfind. easy.
      }

      eapply mem_add_existing.
      - exact Hp0.
      - exact Hmem.
Qed.

Lemma Live_new_red :
  forall gam gam' l,
    Live_new gam ->
    Red gam l gam' ->
    Live_new gam'.
Proof.
  intros gam gam' l Hlive Hred.
  unfold Live_new in *.
  intros p Hmem.

  apply (pLivenessC_new_red gam gam' p l).
  - apply Hlive.
    eapply Red_mem_preserved; eauto.
  - exact Hred.
Qed.

Definition LivePath_new (pt : TPath) : Prop :=
  match pt with
  | conil => True

  | cocons (gam, lbl) rest =>

      (* L1: Every queued message is eventually received. *)
      (forall p q l s sig Tp,
        T.find p gam = Some ((q, l, s) :: sig, Tp) ->
        eventuallyC
          (HPR q p l)
          pt)

      /\

      (* L2: Every pending input eventually receives a message. *)
      (forall p q sig xs,
        T.find p gam = Some (sig, st_receive q xs) ->
        exists l s Tk,
          copathsel l s xs Tk /\
          eventuallyC
            (HPR p q l)
            pt)
  end.

Definition live_tree_path_new (pt : TPath) : Prop :=
  alwaysC LivePath_new pt.

Definition live_tree_new (gam : Ctx) : Prop :=
  forall (lbl : lab) (pt : TPath),
    fair_tree_path_new (cocons (gam, lbl) pt) ->
    live_tree_path_new (cocons (gam, lbl) pt).

Lemma live_tree_path_tail_new :
  forall gam lbl gam' lbl' pt,
    live_tree_path_new
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt)) ->
    live_tree_path_new
      (cocons (gam', lbl') pt).
Proof.
  intros gam lbl gam' lbl' pt Hlive.
  unfold live_tree_path_new in *.

  punfold Hlive.
  inversion Hlive; subst.

  unfold upaco1 in H2.
  destruct H2 as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.
    apply mon_alw.
Qed.

Lemma valid_tree_prefix_new :
  forall gam gam' lbl lbl' pt,
    Red gam lbl gam' ->
    valid_tree_path_new (cocons (gam', lbl') pt) ->
    valid_tree_path_new
      (cocons (gam, lbl) (cocons (gam', lbl') pt)).
Proof.
  intros gam gam' lbl lbl' pt Hred Hvalid.
  unfold valid_tree_path_new.
  pfold.
  econstructor.
  - exact Hred.
  - unfold upaco1.
    left.
    exact Hvalid.
Qed.

Lemma fair_tree_prefix_new :
  forall gam gam' lbl lbl' pt,
    Red gam lbl gam' ->
    fair_tree_path_new (cocons (gam', lbl') pt) ->
    fair_tree_path_new
      (cocons (gam, lbl) (cocons (gam', lbl') pt)).
Proof.
  intros gam gam' lbl lbl' pt Hred Hfair.

  unfold fair_tree_path_new in *.
  destruct Hfair as [Hvalid Hfair].

  split.

  - (* Validity of the prefixed path *)
    eapply valid_tree_prefix_new.
    + exact Hred.
    + exact Hvalid.

  - (* Fairness of the prefixed path *)
    eapply _B_3T.
    + exact Hred.
    + exact Hfair.
Qed.


Lemma proposition_4_9_tree_new :
  forall gam gam' lbl,
    live_tree_new gam ->
    Red gam lbl gam' ->
    live_tree_new gam'.
Proof.
  intros gam gam' lbl Hlive Hred.
  unfold live_tree_new in *.
  intros lbl' pt Hfair.

  assert (Hfair_prefix :
    fair_tree_path_new
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt))).
  {
    eapply fair_tree_prefix_new; eauto.
  }

  specialize
    (Hlive lbl (cocons (gam', lbl') pt) Hfair_prefix).

  eapply live_tree_path_tail_new.
  exact Hlive.
Qed.

Definition receive_event_new
  (receiver sender : participant)
  (lbl : label)
  (pt : TPath) : Prop :=
  match pt with
  | cocons (gam, lr p q l)
      (cocons (gam', next_lbl) rest) =>
      p = receiver /\
      q = sender /\
      l = lbl /\
      Red gam (lr p q l) gam'
  | _ => False
  end.

Lemma receive_event_implies_HPR :
  forall receiver sender lbl pt,
    receive_event_new receiver sender lbl pt ->
    HPR receiver sender lbl pt.
Proof.
  intros receiver sender lbl pt H.
  destruct pt as [ | [gam action] rest].
  - simpl in H. contradiction.
  - destruct action; simpl in H;
      try contradiction.
    destruct rest as [ | [gam' next] tail].
    + simpl in H. contradiction.
    + destruct H as [Hp [Hq [Hl Hred]]].
      subst.
      unfold HPR.
      simpl.
      repeat rewrite String.eqb_refl.
      cbn. easy.
Qed.

Lemma tree_path_red_new_mon :
  monotone1 tree_path_red_new.
Proof.
  unfold monotone1.
  intros x R R' Hstep Hinc.
  destruct Hstep.
  - constructor.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma HPR_implies_receive_event :
  forall receiver sender lbl gam action gam' next rest,
    valid_tree_path_new
      (cocons (gam, action)
        (cocons (gam', next) rest)) ->
    HPR receiver sender lbl
      (cocons (gam, action)
        (cocons (gam', next) rest)) ->
    receive_event_new receiver sender lbl
      (cocons (gam, action)
        (cocons (gam', next) rest)).
Proof.
  intros receiver sender lbl gam action gam' next rest
         Hvalid Hreceive.

  unfold valid_tree_path_new in Hvalid.

  punfold Hvalid.
  inversion Hvalid; subst.

  destruct action; simpl in Hreceive;
    try contradiction.

  destruct (String.eqb receiver s) eqn:Hp;
    try contradiction.
  destruct (String.eqb sender s0) eqn:Hq;
    try contradiction.
  destruct (String.eqb lbl s1) eqn:Hl;
    try contradiction.

  apply String.eqb_eq in Hp.
  apply String.eqb_eq in Hq.
  apply String.eqb_eq in Hl.

  subst.

  unfold receive_event_new.
  simpl.

  repeat split; auto.
  apply tree_path_red_new_mon.
Qed.

Lemma HPR_receive_event_equiv :
  forall receiver sender lbl gam action gam' next rest,
    valid_tree_path_new
      (cocons (gam, action)
        (cocons (gam', next) rest)) ->
    (
      HPR receiver sender lbl
        (cocons (gam, action)
          (cocons (gam', next) rest))
      <->
      receive_event_new receiver sender lbl
        (cocons (gam, action)
          (cocons (gam', next) rest))
    ).
Proof.
  intros receiver sender lbl gam action gam' next rest Hvalid.
  split.
  - eapply HPR_implies_receive_event; eauto.
  - apply receive_event_implies_HPR.
Qed.

Definition pending_message_new
  (gam : Ctx)
  (p q : participant)
  (l : label)
  (s : local.sort) : Prop :=
  exists sig Tp sigma,
    T.find p gam = Some (sigma, Tp) /\
    qCong sigma ((q, l, s) :: sig).

Definition consume_event_new
  (p q : participant)
  (l : label)
  (pt : TPath) : Prop :=
  receive_event_new q p l pt.

Definition queued_liveness_new
  (pt : TPath) : Prop :=
  match pt with
  | conil => True

  | cocons (gam, lbl) rest =>
      forall p q l s,
        pending_message_new gam p q l s ->
        eventuallyC
          (consume_event_new p q l)
          pt
  end.

Definition input_path_liveness_new
  (pt : TPath) : Prop :=
  match pt with
  | conil => True

  | cocons (gam, lbl) rest =>
      forall p q sig xs,
        T.find p gam = Some (sig, st_receive q xs) ->
        exists l s Tk,
          copathsel l s xs Tk /\
          eventuallyC
            (receive_event_new p q l)
            pt
  end.

Definition LivePath_corrected
  (pt : TPath) : Prop :=
  queued_liveness_new pt /\
  input_path_liveness_new pt.

Definition live_tree_path_corrected
  (pt : TPath) : Prop :=
  alwaysC LivePath_corrected pt.

Definition live_tree_corrected
  (gam : Ctx) : Prop :=
  forall (lbl : lab) (pt : TPath),
    fair_tree_path_new (cocons (gam, lbl) pt) ->
    live_tree_path_corrected
      (cocons (gam, lbl) pt).

Lemma live_tree_path_corrected_tail :
  forall gam lbl gam' lbl' pt,
    live_tree_path_corrected
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt)) ->
    live_tree_path_corrected
      (cocons (gam', lbl') pt).
Proof.
  intros gam lbl gam' lbl' pt Hlive.
  unfold live_tree_path_corrected in *.

  punfold Hlive.
  inversion Hlive; subst.

  unfold upaco1 in H2.
  destruct H2 as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.
  apply mon_alw.
Qed.

Lemma proposition_4_9_corrected :
  forall gam gam' lbl,
    live_tree_corrected gam ->
    Red gam lbl gam' ->
    live_tree_corrected gam'.
Proof.
  intros gam gam' lbl Hlive Hred.

  unfold live_tree_corrected in *.
  intros lbl' pt Hfair.

  assert (Hfair_prefix :
    fair_tree_path_new
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt))).
  {
    eapply fair_tree_prefix_new.
    - exact Hred.
    - exact Hfair.
  }

  specialize
    (Hlive lbl (cocons (gam', lbl') pt) Hfair_prefix).

  eapply live_tree_path_corrected_tail.
  exact Hlive.
Qed.

Definition LiveAt_new (pt : TPath) : Prop :=
  match pt with
  | conil => True
  | cocons (gam, _) _ => Live_new gam
  end.

Lemma Live_new_always :
  forall gam lbl pt,
    Live_new gam ->
    valid_tree_path_new (cocons (gam, lbl) pt) ->
    alwaysC LiveAt_new (cocons (gam, lbl) pt).
Proof.
  pcofix CIH.
  intros gam lbl pt Hlive Hvalid.

  pfold.
  constructor.

  - simpl.
    exact Hlive.

  - destruct pt as [ | [gam' lbl'] rest].

    + (* Empty tail *)
      left.
      pfold.
      constructor.

    + (* Nonempty tail *)
      unfold valid_tree_path_new in Hvalid.
      punfold Hvalid.
      inversion Hvalid; subst. constructor.
      apply tree_path_red_new_mon.

      right.
      eapply CIH.
      *
unfold valid_tree_path_new in Hvalid.

eapply paco1_unfold in Hvalid.
2: exact tree_path_red_new_mon.
inversion Hvalid; subst; clear Hvalid.
eapply Live_new_red with (l := lbl).
- exact Hlive.
- eassumption.

unfold valid_tree_path_new in Hvalid.

eapply paco1_unfold in Hvalid.
2: exact tree_path_red_new_mon.

inversion Hvalid; subst.
unfold upaco1 in H3.
destruct H3 as [Htail | Hbot].
- exact Htail.
- destruct Hbot.
Qed.

Definition Dequeued_new
  (p q : participant)
  (sigp : queue)
  (ys : coseq (label * local.sort * st))
  (pt : TPath) : Prop :=
  match pt with
  | cocons (gam, action)
      (cocons (gam', next) rest) =>
      exists l s Tk sig Tp sig' Tp',
        action = lr p q l /\
        Red gam action gam' /\
        copathsel l s ys Tk /\
        T.find p gam = Some (sig, Tp) /\
        qCong sig sigp /\
        Tp = st_receive q ys /\
        T.find p gam' = Some (sig', Tp') /\
        qCong sig' sigp /\
        Tp' = Tk
  | _ => False
  end.

Lemma Dequeued_new_implies_receive_event :
  forall p q sigp ys pt,
    Dequeued_new p q sigp ys pt ->
    exists l s Tk,
      copathsel l s ys Tk /\
      receive_event_new p q l pt.
Proof.
  intros p q sigp ys pt Hdeq.

  destruct pt as [ | [gam action] rest].
  - simpl in Hdeq.
    contradiction.

  - destruct rest as [ | [gam' next] tail].
    + simpl in Hdeq.
      contradiction.

    + unfold Dequeued_new in Hdeq.
      simpl in Hdeq.

      destruct Hdeq as
        [l [s [Tk [sig [Tp [sig' [Tp'
          [Haction [Hred [Hsel Hrest]]]]]]]]]].

      exists l, s, Tk.
      split.
      * exact Hsel.

      * unfold receive_event_new.
        simpl.
        subst action.
        repeat split; auto.
Qed.

Lemma eventuallyC_mon_new :
  forall (P Q : TPath -> Prop) (pt : TPath),
    (forall path, P path -> Q path) ->
    eventuallyC P pt ->
    eventuallyC Q pt.
Proof.
  intros P Q pt HPQ Hev.
  unfold eventuallyC in *.

  eapply paco1_mon_gen.
  - exact Hev.
  - intros r path Hr.
    destruct Hr.
    + constructor 1.
      apply HPQ.
      assumption.
    + constructor 2.
      assumption.
  - intros lc Hr.
    exact Hr.
Qed.

Lemma eventually_Dequeued_new_implies_receive :
  forall p q sigp ys pt,
    eventuallyC (Dequeued_new p q sigp ys) pt ->
    eventuallyC
      (fun path =>
        exists l s Tk,
          copathsel l s ys Tk /\
          receive_event_new p q l path)
      pt.
Proof.
  intros p q sigp ys pt H.

  eapply eventuallyC_mon_new.
  - intros path Hdeq.
    eapply Dequeued_new_implies_receive_event.
    exact Hdeq.
  - exact H.
Qed.

Print Enabled.

Inductive eventually_new {A : Type}
  (F : coseq A -> Prop)
  : coseq A -> Prop :=

| eventually_here_new :
    forall x xs,
      F (cocons x xs) ->
      eventually_new F (cocons x xs)

| eventually_later_new :
    forall x xs,
      eventually_new F xs ->
      eventually_new F (cocons x xs).

Lemma eventually_new_mon :
  forall {A : Type}
         (P Q : coseq A -> Prop)
         (pt : coseq A),
    (forall path, P path -> Q path) ->
    eventually_new P pt ->
    eventually_new Q pt.
Proof.
  intros A P Q pt HPQ Hev.
  induction Hev.
  - apply eventually_here_new.
    apply HPQ.
    assumption.
  - apply eventually_later_new.
    assumption.
Qed.

Definition FairPath_new (pt : TPath) : Prop :=
  (forall p q l,
    Enabled (RedE (ls p q l)) pt ->
    exists l',
      eventually_new (HPS p q l') pt)
  /\
  (forall p q l,
    Enabled (RedE (lr p q l)) pt ->
    eventually_new (HPR p q l) pt).

Definition FairPathC_new (pt : TPath) : Prop :=
  alwaysC FairPath_new pt.

Definition fair_tree_path_corrected (pt : TPath) : Prop :=
  valid_tree_path_new pt /\
  FairPathC_new pt.

Definition live_tree_final (gam : Ctx) : Prop :=
  forall (lbl : lab) (pt : TPath),
    fair_tree_path_corrected (cocons (gam, lbl) pt) ->
    live_tree_path_corrected
      (cocons (gam, lbl) pt).

Lemma eventually_new_prefix :
  forall (P : TPath -> Prop) gam lbl pt,
    eventually_new P pt ->
    eventually_new P (cocons (gam, lbl) pt).
Proof.
  intros P gam lbl pt H.
  apply eventually_later_new.
  exact H.
Qed.

Lemma enabled_send_step_new :
  forall gam gam' lbl p q l,
    Red gam lbl gam' ->
    RedE (ls p q l) gam ->
    (exists l', lbl = ls p q l') \/
    (exists l', RedE (ls p q l') gam').
Proof.
  intros gam gam' lbl p q l Hred Henabled.

  unfold RedE in Henabled.
  destruct Henabled as [gam_send Hsend].

  inversion Hred; subst; clear Hred.
right.
exists l.
unfold RedE.
inversion Hsend; subst.
destruct (string_dec p q0) as [Heq_q | Hneq_q].

- (* p = q0: impossible *)
  subst p.
  destruct (T.find q0 gam) as [[sigma T0] | ] eqn:Hfind.
  + simpl in H3, H11.
    destruct H3 as [_ Hrecv].
    destruct H11 as [_ Hsend_type].
    rewrite Hrecv in Hsend_type.
    discriminate.
  + simpl in H3.
    contradiction.

- (* p <> q0 *)
  destruct (string_dec p p0) as [Heq_p | Hneq_p].

  + (* p = p0: queue changed, type unchanged *)
    subst p.

destruct (T.find p0 gam) as [[sigma T0] | ] eqn:Hfind.
- simpl in H2, H11. 
  destruct H2 as [Hcong2 HTp].
  destruct H11 as [Hcong11 HTsend].

  assert (HTp_send : Tp = q ! xs0).
  {
    rewrite <- HTp.
    exact HTsend.
  }
  subst.
eexists.
eapply E_send with
  (sig := sigp)
  (s := s0)
  (xs := xs0). easy. eauto.
rewrite T.add_spec1.
simpl.
split. easy. easy. easy.

exists
  (T.add p
    (sig ++ [(q, l, s0)], Tk0)
    (T.add p0 (sigp, Tp)
      (T.add q0 (sigq, Tk) gam))).

eapply E_send with
  (sig := sig)
  (s := s0)
  (xs := xs0).

easy. easy.
rewrite T.add_spec2.
rewrite T.add_spec2.
exact H11.
apply String.eqb_neq in Hneq_p, Hneq_q.
rewrite String.eqb_sym. rewrite Hneq_q. easy.
apply String.eqb_neq in Hneq_p, Hneq_q.
rewrite String.eqb_sym. rewrite Hneq_p. easy.

destruct (string_dec p p0) as [Heq | Hneq].

- (* Same sender: p = p0 *)
  subst p.
  inversion Hsend; subst; clear Hsend.

  match goal with
  | Hlookup : context [T.find p0 gam] |- _ =>
      destruct (T.find p0 gam) as [[sigma T0] | ] eqn:Hfind
  end.

  + simpl in H1.
    match goal with
    | Hlookup :
        (qCong _ _ /\ _ = q ! _) |- _ =>
        destruct Hlookup as [_ Htype_send]
    end.
    destruct H1 as [_ Htype_original].
    rewrite Htype_original in Htype_send.
    inversion Htype_send; subst.

    left.
    exists l0.
    reflexivity.

  + simpl in H1.
    contradiction.

- (* Different senders: p <> p0 *)
  right.
  exists l.
  unfold RedE.

  inversion Hsend; subst; clear Hsend.

  eexists.
  eapply E_send.
  + eassumption.
  + eassumption.
  + rewrite T.add_spec2.
    eassumption.
apply String.eqb_neq in Hneq.
rewrite String.eqb_sym. rewrite Hneq. easy.
Qed.

Definition queued_liveness_final
  (pt : TPath) : Prop :=
  match pt with
  | conil => True
  | cocons (gam, lbl) rest =>
      forall p q l s,
        pending_message_new gam p q l s ->
        eventually_new
          (consume_event_new p q l)
          pt
  end.

Definition input_path_liveness_final
  (pt : TPath) : Prop :=
  match pt with
  | conil => True
  | cocons (gam, lbl) rest =>
      forall p q sig xs,
        T.find p gam = Some (sig, st_receive q xs) ->
        exists l s Tk,
          copathsel l s xs Tk /\
          eventually_new
            (receive_event_new p q l)
            pt
  end.


Definition LivePath_final (pt : TPath) : Prop :=
  queued_liveness_final pt /\
  input_path_liveness_final pt.

Definition live_tree_path_final (pt : TPath) : Prop :=
  alwaysC LivePath_final pt.

Lemma live_tree_path_final_tail :
  forall gam lbl gam' lbl' pt,
    live_tree_path_final
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt)) ->
    live_tree_path_final
      (cocons (gam', lbl') pt).
Proof.
  intros gam lbl gam' lbl' pt Hlive.
  unfold live_tree_path_final in *.

  punfold Hlive.
  inversion Hlive; subst.

  unfold upaco1 in H2.
  destruct H2 as [Hco | Hbot].
  - exact Hco.
  - destruct Hbot.

  apply mon_alw.
Qed.

Definition queue_projection (p : string) (sigma : queue) : queue :=
  filter
    (fun '(q, _, _) => String.eqb p q)
    sigma.

Lemma qCong_projection :
  forall sigma tau p,
    qCong sigma tau ->
    queue_projection p sigma =
    queue_projection p tau.
Proof.
  intros sigma tau p Hcong.
  destruct Hcong.

  - (* qcl *)
    rewrite app_nil_r.
    reflexivity.

  - (* qcr *)
    rewrite app_nil_l.
    reflexivity.

  - (* qassoc *)
    repeat rewrite app_assoc.
    reflexivity.

  - (* qcomm *)
    unfold queue_projection.
    repeat rewrite filter_app.
    simpl.

    destruct (String.eqb p p1) eqn:Hp1;
    destruct (String.eqb p p2) eqn:Hp2;
    simpl;
    try reflexivity.

    + (* p = p1 and p = p2: impossible *)
      apply String.eqb_eq in Hp1.
      apply String.eqb_eq in Hp2.
      subst.
      contradiction.
Qed.

Lemma qCong_swap_head :
  forall (x : string * string * local.sort)
         (p l : string) (s : local.sort)
         (rest : queue),
    let '(q, _, _) := x in
    q <> p ->
    qCong
      (x :: (p, l, s) :: rest)
      ((p, l, s) :: x :: rest).
Proof.
  intros [[q l0] s0] p l s rest Hneq.
  simpl in Hneq.

  change
    (qCong
      ([] ++ [(q, l0, s0)] ++ [(p, l, s)] ++ rest)
      ([] ++ [(p, l, s)] ++ [(q, l0, s0)] ++ rest)).

  apply qcomm.
  exact Hneq.
Qed.

Lemma qCong_cons :
  forall (x : string * string * local.sort) sigma tau,
    qCong sigma tau ->
    qCong (x :: sigma) (x :: tau).
Proof.
  intros x sigma tau Hcong.
  destruct Hcong.

  - (* qcl *)
    rewrite app_nil_r.
    reflexivity.

  - (* qcr *)
    rewrite app_nil_l.
    reflexivity.

  - (* qassoc *)
    repeat rewrite app_assoc.
    reflexivity.

  - (* qcomm *)
    destruct x as [[r lab] sort].
    change
      (qCong
        ([(r, lab, sort)] ++
         q ++ [(p1, l1, s1)] ++ [(p2, l2, s2)] ++ q')
        ([(r, lab, sort)] ++
         q ++ [(p2, l2, s2)] ++ [(p1, l1, s1)] ++ q')).

    repeat rewrite <- app_assoc.

replace
  ([(r, lab, sort)] ++ q ++ [(p1, l1, s1)] ++
   [(p2, l2, s2)] ++ q')
  with
  (([(r, lab, sort)] ++ q) ++ [(p1, l1, s1)] ++
   [(p2, l2, s2)] ++ q')
  by (repeat rewrite app_assoc; reflexivity).

replace
  ([(r, lab, sort)] ++ q ++ [(p2, l2, s2)] ++
   [(p1, l1, s1)] ++ q')
  with
  (([(r, lab, sort)] ++ q) ++ [(p2, l2, s2)] ++
   [(p1, l1, s1)] ++ q')
  by (repeat rewrite app_assoc; reflexivity).

apply qcomm.
exact H.
Qed.

Lemma qCong_head_projection :
  forall (sigma : queue) p l s restp,
    queue_projection p sigma = (p, l, s) :: restp ->
    exists rest,
      qCong sigma ((p, l, s) :: rest).
Proof.
  induction sigma as [ | [[q l0] s0] sigma IH].
  - intros p l s restp Hproj.
    simpl in Hproj.
    discriminate.

  - intros p l s restp Hproj.

    unfold queue_projection in Hproj.
    simpl in Hproj.

    destruct (String.eqb p q) eqn:Heq.

    + (* The first message is addressed to p. *)
      apply String.eqb_eq in Heq.
      subst q.

      inversion Hproj; subst.

      exists sigma.
      reflexivity.

    + (* The first message is addressed elsewhere. *)
      apply String.eqb_neq in Heq.

      assert (Htail :
        queue_projection p sigma = (p, l, s) :: restp).
      {
        exact Hproj.
      }

      destruct (IH p l s restp Htail)
        as [rest Hcong].

      exists ((q, l0, s0) :: rest).

      (* Lift the tail congruence under the head. *)
      assert (Hcons :
        qCong
          ((q, l0, s0) :: sigma)
          ((q, l0, s0) :: (p, l, s) :: rest)).
      {
        cbn.
        apply qCong_cons.
        exact Hcong.
        (* Requires congruence compatibility with cons. *)
        (* This follows by induction over the elementary
           qCong constructors, using equivalence. *)
      }

      etransitivity.
      * exact Hcons.
      * change
  (qCong
    ([] ++ [(q, l0, s0)] ++ [(p, l, s)] ++ rest)
    ([] ++ [(p, l, s)] ++ [(q, l0, s0)] ++ rest)).

apply qcomm.
congruence.
Qed.

Lemma qCong_consume_other :
  forall sigma sigp sigp0 q0 p l0 l s' s'0,
    p <> q0 ->
    qCong sigma ((q0, l0, s') :: sigp) ->
    qCong sigma ((p, l, s'0) :: sigp0) ->
    exists rest,
      qCong sigp ((p, l, s'0) :: rest).
Proof.
  intros sigma sigp sigp0 q0 p l0 l s' s'0
         Hneq Hcong1 Hcong2.

  assert (Hproj1 :
    queue_projection p sigma =
    queue_projection p ((q0, l0, s') :: sigp)).
  {
    eapply qCong_projection.
    exact Hcong1.
  }

  assert (Hproj2 :
    queue_projection p sigma =
    queue_projection p ((p, l, s'0) :: sigp0)).
  {
    eapply qCong_projection.
    exact Hcong2.
  }

  assert (Hpq : (p =? q0) = false).
  {
    apply String.eqb_neq.
    exact Hneq.
  }

  assert (Hhead :
    queue_projection p sigp =
      (p, l, s'0) :: queue_projection p sigp0).
  {
    rewrite Hproj1 in Hproj2.
    unfold queue_projection in Hproj2.
    simpl in Hproj2.
    rewrite Hpq in Hproj2.
    rewrite String.eqb_refl in Hproj2.
    simpl in Hproj2.
    exact Hproj2.
  }

  eapply qCong_head_projection.
  exact Hhead.
Qed.

Definition FairPath_final (pt : TPath) : Prop :=
  (forall p q l,
    Enabled (RedE (ls p q l)) pt ->
    exists l',
      eventually_new (HPS p q l') pt)
  /\
  (forall p q l,
    Enabled (RedE (lr p q l)) pt ->
    exists l',
      eventually_new (HPR p q l') pt).

Definition fair_tree_path_final (pt : TPath) : Prop :=
  valid_tree_path_new pt /\
  alwaysC FairPath_final pt.

Definition live_tree_final_corrected (gam : Ctx) : Prop :=
  forall (lbl : lab) (pt : TPath),
    fair_tree_path_final (cocons (gam, lbl) pt) ->
    live_tree_path_final (cocons (gam, lbl) pt).

Lemma enabled_receive_step_final :
  forall gam gam' lbl p q l,
    Red gam lbl gam' ->
    RedE (lr p q l) gam ->
    (exists l', lbl = lr p q l') \/
    (exists l', RedE (lr p q l') gam').
Proof.
  intros gam gam' lbl p q l Hred Henabled.

  unfold RedE in Henabled.
  destruct Henabled as [gam_recv Hrecv].

  inversion Hred; subst; clear Hred.

  - (* E_recv *)
    inversion Hrecv; subst; clear Hrecv.

    destruct (string_dec p q0) as [Heq | Hneq].

    + (* Both receives are performed by p. *)
      subst p.
destruct (T.find q0 gam)
  as [[sigma T0] | ] eqn:Hfind.

- simpl in H3, H13.
  destruct H3 as [_ HT1].
  destruct H13 as [_ HT2].

  assert (Hsender : p0 = q).
  {
    rewrite HT1 in HT2.
    inversion HT2.
    reflexivity.
  }

  subst q.

  left.
  exists l0.
  reflexivity. easy.

right.
exists l.
unfold RedE.
destruct (string_dec q p0)
  as [Heq_sender | Hneq_sender].
- subst q.

  destruct (T.find p0 gam)
    as [[sigma T0] | ] eqn:Hfind.

  + simpl in H2, H12.
    destruct H2 as [Hcong_first HTp].
    destruct H12 as [Hcong_second HTp0].

    destruct
      (qCong_consume_other
         sigma sigp sigp0 q0 p l0 l s' s'0
         Hneq Hcong_first Hcong_second)
      as [rest Hrest].
assert (HTypes : Tp = Tp0).
{
  rewrite <- HTp.
  exact HTp0.
}

eexists.
eapply E_recv
  with (sigp := rest)
       (sigq := sigq0)
       (Tp := Tp0)
       (s := s0)
       (s' := s'0)
       (Tk := Tk0)
       (xs := xs0).

- exact H7.
- exact H8.
- exact H10.

- rewrite T.add_spec1.
subst.
split.
- exact Hrest.
- reflexivity.
  2: {
  easy.
  }
  subst.
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in H7.
    rewrite H7. easy.
  }

- rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq.
    rewrite String.eqb_sym.
    rewrite Hneq. easy.
  }
  exact H13.
  
destruct (string_dec q q0) as [Heq_q | Hneq_q].
- subst q.
  destruct (string_dec p p0) as [Heq_p | Hneq_p].
  subst.
eexists.
eapply E_recv
  with (sigp := sigp0)
       (sigq := sigp)
       (Tp := Tk)
       (s := s0)
       (s' := s'0)
       (Tk := Tk0)
       (xs := xs0).

- exact H7.
- exact H8.
- exact H10.

- rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_sender.
    rewrite String.eqb_sym.
    rewrite Hneq_sender. easy.
  }

  rewrite T.add_spec1.
  simpl.

  destruct (T.find q0 gam)
    as [[sigma T0] | ] eqn:Hfind.

  + simpl in H3, H12.
    destruct H3 as [HC1 HT1].
    destruct H12 as [HC2 HT2].

    split.
    * transitivity sigma.
      -- symmetry. exact HC1.
      -- exact HC2.
    * reflexivity.
    easy.

  rewrite T.add_spec1.
  simpl.
split.
- reflexivity.
- destruct (T.find p0 gam) as [[sigma T0] | ] eqn:Hfind.
  + simpl in H2, H13.
    destruct H2 as [_ HTp].
    destruct H13 as [_ HTrecv].
    rewrite <- HTp.
    exact HTrecv.
  + simpl in H2.
    contradiction.

eexists.
eapply E_recv
  with (sigp := sigp0)
       (sigq := sigq0)
       (Tp := Tk)
       (s := s0)
       (s' := s'0)
       (Tk := Tk0)
       (xs := xs0).

- (* Distinct sender and receiver *)
  exact H7.

- (* Receive branch *)
  exact H8.

- (* Subsorting *)
  exact H10.

- (* Sender q0: updated binding *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_sender.
    rewrite String.eqb_sym.
    rewrite Hneq_sender. easy.
  }

  rewrite T.add_spec1.
  simpl.

  destruct (T.find q0 gam)
    as [[sigma T0] | ] eqn:Hfind.

  + simpl in H3, H12.
    destruct H3 as [HC1 HT1].
    destruct H12 as [HC2 HT2].

    split.
    * transitivity sigma.
      -- symmetry.
         exact HC1.
      -- exact HC2.
    * reflexivity.

  + simpl in H3.
    contradiction.

- (* Receiver p: unchanged binding *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_p.
    rewrite String.eqb_sym.
    rewrite Hneq_p. easy.
  }

  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq.
    rewrite String.eqb_sym.
    rewrite Hneq. easy.
  }

  exact H13.

destruct (string_dec p p0) as [Heq_p | Hneq_p].
- subst p.

  eexists.
  eapply E_recv
    with (sigp := sigp0)
         (sigq := sigp)
         (Tp := Tp0)
         (s := s0)
         (s' := s'0)
         (Tk := Tk0)
         (xs := xs0).

  + exact H7.
  + exact H8.
  + exact H10.

  + (* Sender q is unchanged *)
    rewrite T.add_spec2.
    2: {
      apply String.eqb_neq in Hneq_sender.
      rewrite String.eqb_sym.
      rewrite Hneq_sender. easy.
    }

    rewrite T.add_spec2.
    2: {
      apply String.eqb_neq in Hneq_q.
      rewrite String.eqb_sym.
      rewrite Hneq_q. easy.
    }

    exact H12.

  + (* Receiver p0 has updated queue sigp *)
    rewrite T.add_spec1.
    simpl.

    destruct (T.find p0 gam)
      as [[sigma T0] | ] eqn:Hfind.

    * simpl in H2, H13.
      destruct H2 as [HC1 HT1].
      destruct H13 as [HC2 HT2].

      split.
      -- reflexivity.
      -- rewrite <- HT1.
         exact HT2.

    * simpl in H2.
      contradiction.

eexists.
eapply E_recv
  with (sigp := sigp0)
       (sigq := sigq0)
       (Tp := Tp0)
       (s := s0)
       (s' := s'0)
       (Tk := Tk0)
       (xs := xs0).

- (* Sender and receiver are distinct *)
  exact H7.

- (* Valid receive branch *)
  exact H8.

- (* Subsorting *)
  exact H10.

- (* Sender q is unchanged *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_sender.
    rewrite String.eqb_sym.
    rewrite Hneq_sender. easy.
  }

  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_q.
    rewrite String.eqb_sym.
    rewrite Hneq_q. easy.
  }

  exact H12.

- (* Receiver p is unchanged *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_p.
    rewrite String.eqb_sym.
    rewrite Hneq_p. easy.
  }

  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq.
    rewrite String.eqb_sym.
    rewrite Hneq. easy.
  }

  exact H13.

right.
exists l.
unfold RedE.

inversion Hrecv; subst; clear Hrecv.
destruct (string_dec p p0) as [Heq_p | Hneq_p].
- subst p.

  destruct (T.find p0 gam)
    as [[sigma T0] | ] eqn:Hfind.

  + simpl in H1.
    destruct H1 as [_ Hsend_type].
    subst.
destruct H11 as [_ Htype].
discriminate Htype. easy.

destruct (string_dec q p0) as [Heq_q | Hneq_q].
- subst q.

  destruct (T.find p0 gam)
    as [[sigma T0] | ] eqn:Hfind.

  + simpl in H1, H10.
    destruct H1 as [HCsend HTsend].
    destruct H10 as [HCrecv HTrecv].

assert (HC :
  qCong sig ((p, l, s') :: sigp)).
{
  transitivity sigma.
  - symmetry.
    exact HCsend.
  - exact HCrecv.
}
assert (Hqueue :
  qCong
    (sig ++ [(q0, l0, s)])
    ((p, l, s') :: (sigp ++ [(q0, l0, s)]))).
{
  apply qcong_app.
  exact HC.
}
subst.

eexists.
eapply E_recv
  with (sigp := sigp ++ [(q0, l0, s)])
       (sigq := sigq)
       (Tp := Tk)
       (s := s0)
       (s' := s')
       (Tk := Tk0)
       (xs := xs0).

- (* Sender and receiver are distinct *)
  exact H5.

- (* Receive branch *)
  exact H6.

- (* Subsorting *)
  exact H8.

- (* Sender p0: queue extended by the send *)
  rewrite T.add_spec1.
  simpl.
  split.
  + exact Hqueue.
  + reflexivity.

- (* Receiver p: unchanged by the send *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_p.
    rewrite String.eqb_sym.
    rewrite Hneq_p. easy.
  }

  exact H11.
  easy.

eexists.
eapply E_recv
  with (sigp := sigp)
       (sigq := sigq)
       (Tp := Tp)
       (s := s0)
       (s' := s')
       (Tk := Tk0)
       (xs := xs0).

- (* Sender and receiver are distinct *)
  exact H5.

- (* Valid receive branch *)
  exact H6.

- (* Subsorting *)
  exact H8.

- (* Sender q is unchanged *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_q.
    rewrite String.eqb_sym.
    rewrite Hneq_q. easy.
  }
  exact H10.

- (* Receiver p is unchanged *)
  rewrite T.add_spec2.
  2: {
    apply String.eqb_neq in Hneq_p.
    rewrite String.eqb_sym.
    rewrite Hneq_p. easy.
  }
  exact H11.
Qed.


Lemma FairPath_final_head_prefix :
  forall gam gam' lbl lbl' pt,
    Red gam lbl gam' ->
    alwaysC FairPath_final (cocons (gam', lbl') pt) ->
    FairPath_final
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt)).
Proof.
  intros gam gam' lbl lbl' pt Hred Hfair.

  assert (Hfair_head :
    FairPath_final (cocons (gam', lbl') pt)).
  {
    unfold alwaysC in Hfair.
    punfold Hfair.
    inversion Hfair; subst.
    assumption.
    apply mon_alw.
  }

  destruct Hfair_head as [HF1 HF2].

  unfold FairPath_final.
  split.

  - (* F1: Send fairness *)
    intros p q l Henabled.
    simpl in Henabled.

    destruct
      (enabled_send_step_new
         gam gam' lbl p q l Hred Henabled)
      as [[l0 Haction] | [l0 Henabled']].

    + exists l0.
      subst lbl.
      apply eventually_here_new.
      unfold HPS.
      simpl.
      repeat rewrite String.eqb_refl.
      easy.

    + destruct (HF1 p q l0) as [l1 Hevent].
      * simpl.
        exact Henabled'.
      * exists l1.
        apply eventually_later_new.
        exact Hevent.

  - (* F2: Receive fairness *)
    intros p q l Henabled.
    simpl in Henabled.
destruct
  (enabled_receive_step_final
     gam gam' lbl p q l Hred Henabled)
  as [[l0 Haction] | [l0 Henabled']].

- (* Case 1: the receive occurs immediately *)
  exists l0.
  subst lbl.
  apply eventually_here_new.
  unfold HPR.
  simpl.
  repeat rewrite String.eqb_refl.
  easy.

- (* Case 2: the receive remains enabled in gam' *)
  assert (Henabled_suffix :
    Enabled (RedE (lr p q l0))
      (cocons (gam', lbl') pt)).
  {
    simpl.
    exact Henabled'.
  }

  destruct (HF2 p q l0 Henabled_suffix)
    as [l1 Hevent].

  exists l1.
  apply eventually_later_new.
  exact Hevent.
Qed.

Lemma B_3T_final :
  forall gam gam' lbl lbl' pt,
    Red gam lbl gam' ->
    alwaysC FairPath_final (cocons (gam', lbl') pt) ->
    alwaysC FairPath_final
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt)).
Proof.
  intros gam gam' lbl lbl' pt Hred Hfair.

  pfold.
  constructor.

  - (* Fairness at the new head *)
    eapply FairPath_final_head_prefix.
    + exact Hred.
    + exact Hfair.

  - (* Fairness of the suffix *)
    left.
    exact Hfair.
Qed.

Lemma fair_tree_prefix_final :
  forall gam gam' lbl lbl' pt,
    Red gam lbl gam' ->
    fair_tree_path_final (cocons (gam', lbl') pt) ->
    fair_tree_path_final
      (cocons (gam, lbl) (cocons (gam', lbl') pt)).
Proof.
  intros gam gam' lbl lbl' pt Hred Hfair.

  unfold fair_tree_path_final in *.
  destruct Hfair as [Hvalid Hfair].

  split.

  - eapply valid_tree_prefix_new.
    + exact Hred.
    + exact Hvalid.

  - eapply B_3T_final.
    + exact Hred.
    + exact Hfair.
Qed.

Lemma proposition_4_9_final :
  forall gam gam' lbl,
    live_tree_final_corrected gam ->
    Red gam lbl gam' ->
    live_tree_final_corrected gam'.
Proof.
  intros gam gam' lbl Hlive Hred.

  unfold live_tree_final_corrected in *.
  intros lbl' pt Hfair.

  assert (Hfair_prefix :
    fair_tree_path_final
      (cocons (gam, lbl)
        (cocons (gam', lbl') pt))).
  {
    eapply fair_tree_prefix_final.
    - exact Hred.
    - exact Hfair.
  }

  specialize
    (Hlive lbl (cocons (gam', lbl') pt) Hfair_prefix).

  eapply live_tree_path_final_tail.
  exact Hlive.
Qed.
