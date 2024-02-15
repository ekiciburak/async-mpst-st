From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.
Require Import ProofIrrelevance.
(* Require dpdgraph.dpdgraph. *)

Lemma exts: forall {p l s} w, singleton w -> singleton (st_send p [(l,s,w)]).
Proof. intros p l s w H.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Qed.

Lemma extsR: forall {p l s} w, singleton (st_send p [(l,s,w)]) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.

Lemma extr: forall {p l s} w, singleton w -> singleton (st_receive p [(l,s,w)]).
Proof. intros.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Qed.

Lemma extrR: forall {p l s} w, singleton (st_receive p [(l,s,w)]) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.

Lemma extap: forall {p a} w, singleton w -> singleton ((merge_ap_cont p a w)).
Proof. induction a; intros.
       rewrite(siso_eq((merge_ap_cont p (ap_receive q n s s0) w))).
       simpl. apply extr. easy.
       rewrite(siso_eq((merge_ap_cont p (ap_merge q n s s0 a) w))).
       simpl. pfold. constructor. unfold singleton in IHa, H.
       left.
       apply IHa. easy.
       rewrite apend_an.
       easy.
Qed.

Lemma extapR: forall {p a} w, singleton ((merge_ap_cont p a w)) -> singleton w.
Proof. intros p a.
       induction a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) w)) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) w)) in H.
       simpl in H.
       apply IHa. apply extrR in H. easy.
       rewrite apend_an in H. easy.
Qed.

Lemma extapnR: forall {n p a} w, singleton ((merge_ap_contn p a w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       apply extapR in H.
       apply (IHn p a). easy.
Qed.

Lemma extapn: forall {n p a} w, singleton w -> singleton ((merge_ap_contn p a w n)).
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply extap.
       apply IHn. easy.
Qed.


Lemma extcpR: forall {p c} w, singleton (merge_cp_cont p c w) -> singleton w.
Proof. intros p c.
       induction c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) w)) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq((merge_cp_cont p (cp_mergea q n s s0 c) w))) in H.
       simpl in H.
       apply IHc. apply extrR in H. easy.
       rewrite(siso_eq((merge_cp_cont p (cp_send s s0 s1) w))) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(siso_eq((merge_cp_cont p (cp_merge s s0 s1 c) w))) in H.
       simpl in H. 
       apply IHc. apply extsR in H. easy.
       rewrite cpend_an in H. easy.
Qed.

Lemma extdcnR: forall {n p c} w, singleton ((merge_cp_contn p c w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply (@extcpR p c w).
       apply (IHn p c (merge_cp_cont p c w)).
       simpl in H.
       rewrite mcomm3. exact H.
Qed.

Lemma extdpR: forall {p d} w, singleton ((merge_dp_cont p d w)) -> singleton w.
Proof. intros p d.
       induction d; intros.
       subst.
       rewrite(siso_eq((merge_dp_cont p (dp_receive q n s s0) w))) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq((merge_dp_cont p (dp_mergea q n s s0 d) w))) in H.
       simpl in H.
       apply IHd. apply extrR in H. easy.
       rewrite(siso_eq((merge_dp_cont p (dp_send q n s s0) w))) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(siso_eq((merge_dp_cont p (dp_merge q n s s0 d) w))) in H.
       simpl in H. 
       apply IHd. apply extsR in H. easy.
       rewrite dpend_an in H. easy.
Qed.

Lemma extdpnR: forall {n p d} w, singleton ((merge_dp_contn p d w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply (@extdpR p d w).
       apply (IHn p d (merge_dp_cont p d w)).
       simpl in H.
       rewrite mcomm4. exact H.
Qed.

Lemma extbp: forall {p b} w, singleton w -> singleton ((merge_bp_cont p b w)).
Proof. induction b; intros.
       rewrite(siso_eq((merge_bp_cont p (bp_receivea s s0 s1) w))).
       simpl. apply extr. easy.
       rewrite(siso_eq((merge_bp_cont p (bp_send q n s s0) w))).
       simpl. pfold. constructor. unfold singleton in H.
       left. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) w)).
       simpl. pfold. constructor. left. 
       unfold singleton in IHb, H.
       apply IHb. easy.
       rewrite(siso_eq((merge_bp_cont p (bp_merge q n s s0 b) w))).
       simpl. pfold. constructor.
       unfold singleton in IHb, H. left.
       apply IHb. easy.
       rewrite bpend_an.
       easy.
Qed.

Lemma extbpR: forall {p b} w, singleton ((merge_bp_cont p b w)) -> singleton w.
Proof. intros p b.
       induction b; intros.
       rewrite(siso_eq((merge_bp_cont p (bp_receivea s s0 s1) w))) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) w)) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) w)) in H.
       simpl in H. apply extrR in H. apply IHb. easy.
       rewrite(siso_eq((merge_bp_cont p (bp_merge q n s s0 b) w))) in H.
       simpl in H.  apply extsR in H. apply IHb. easy.
       rewrite bpend_an in H. easy. 
Qed.

Lemma extbpn: forall {n p b} w, singleton w -> singleton ((merge_bp_contn p b w n)).
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply extbp.
       apply IHn. easy.
Qed.

Lemma extbpnR: forall {n p b} w, singleton ((merge_bp_contn p b w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       apply extbpR in H.
       apply (IHn p b). easy.
Qed.

Lemma extbpns: forall {n p l s b} w, singleton w -> singleton ((merge_bp_contn p b (st_send p [(l,s,w)]) n)).
Proof. intros.
       apply extbpn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extbpnr: forall {n p l s b} w, singleton w -> singleton ((merge_bp_contn p b (st_receive p [(l,s,w)]) n)).
Proof. intros.
       apply extbpn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapns: forall {n p l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_send p [(l,s,w)]) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapnr: forall {n p l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_receive p [(l,s,w)]) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapnspq: forall {n p q l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_send q [(l,s,w)]) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.


Fixpoint isInCp (p: participant) (c: Cp p): bool :=
  match c with
    | cp_send q l s       => true
    | cp_merge q l s c    => true
    | cp_mergea q H l s c => isInCp p c
    | _                   => false
  end.

Lemma cpap: forall p c w,
  isInCp p c = false ->
  exists a, merge_cp_cont p c w = merge_ap_cont p a w.
Proof. intros p c.
       induction c; intros.
       - simpl in *. 
         exists (ap_receive q n s s0).
         rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) w)).
         rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) w)).
         simpl. easy.
       - simpl in *.
         specialize(IHc w H).
         destruct IHc as (a,IHc).
         exists(ap_merge q n s s0 a).
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) w)).
         rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) w)).
         simpl.
         rewrite IHc. easy.
       - simpl in *. easy.
       - simpl in *. easy.
       - simpl in *. exists ap_end. 
         rewrite(siso_eq( merge_ap_cont p ap_end w)).
         rewrite(siso_eq(merge_cp_cont p cp_end w )).
         simpl. easy.
Qed.

Inductive nRefinementN: siso -> siso -> Prop :=
  | n_outN  : forall w w' p b l s P, 
              (CoInR (p,snd) (act (@und w')) -> False) -> 
              nRefinementN (mk_siso (merge_bp_cont p b (st_send p [(l,s,(@und w))])) P) w'
   | n_inpN  : forall w w' p c l s P, 
              (CoInR (p,rcv) (act (@und w')) -> False) -> 
              nRefinementN (mk_siso (merge_cp_cont p c (st_receive p [(l,s,(@und w))])) P) w'
  | n_out_rN: forall w w' p b l s P, 
              (CoInR (p,snd) (act (@und w)) -> False) -> 
              nRefinementN w (mk_siso (merge_bp_cont p b (st_send p [(l,s,(@und w'))])) P)
  | n_inp_rN: forall w w' p c l s P,
              (CoInR (p,rcv) (act (@und w)) -> False) -> 
              nRefinementN w (mk_siso (merge_cp_cont p c (st_receive p [(l,s,(@und w'))])) P)
  | n_a_lN  : forall w w' p l l' s s' a n P Q,
              l <> l' -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                      (mk_siso (merge_ap_contn p a (st_receive p [(l',s',(@und w'))]) n) Q)
  | n_a_sN  : forall w w' p l s s' a n P Q,
              nsubsort s' s -> 
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                           (mk_siso (merge_ap_contn p a (st_receive p [(l,s',(@und w'))]) n) Q)
  | n_a_wN  : forall w w' p l s s' a n P Q R,
              subsort s' s ->
              nRefinementN w (mk_siso (merge_ap_contn p a (@und w') n) P) ->
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) Q) 
                           (mk_siso (merge_ap_contn p a (st_receive p [(l,s',(@und w'))]) n) R)
  | n_i_o_1N: forall w w' p q l l' s s' P Q, nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                          (mk_siso (st_send q [(l',s',(@und w'))]) Q)
  | n_i_o_2N: forall w w' p l l' s s' c P Q, isInCp p c = true ->
                                             nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                          (mk_siso (merge_cp_cont p c (st_receive p [(l',s',(@und w'))])) Q)
  | n_b_lN  : forall w w' p l l' s s' b n P Q,
              l <> l' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                      (mk_siso (merge_bp_contn p b (st_send p [(l',s',(@und w'))]) n) Q)
  | n_b_sN  : forall w w' p l s s' b n P Q,
              nsubsort s s' -> 
              nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                           (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) Q)
  | n_b_wN  : forall w w' p l s s' b n P Q R,
              subsort s s' ->
              nRefinementN w (mk_siso (merge_bp_contn p b (@und w') n) P) ->
              nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) Q) 
                           (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) R).

Lemma n_inp_lN: forall w w' p l l' s s' P Q,
                l <> l' -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                (mk_siso (st_receive p [(l',s',(@und w'))]) Q).
Proof. intros.
       specialize(n_a_lN w w' p l l' s s' (ap_end) 1); intros Hnal.
       simpl in Hnal.
       rewrite apend_an in Hnal.
       apply Hnal.
       easy.
Qed.

Lemma n_inp_sN: forall w w' p l s s' P Q,
                nsubsort s' s -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P)
                                              (mk_siso (st_receive p [(l,s',(@und w'))]) Q).
Proof. intros.
       specialize(n_a_sN w w' p l s s' (ap_end) 1); intros Hnas.
       simpl in Hnas.
       rewrite apend_an in Hnas.
       apply Hnas.
       easy.
Qed.

Lemma n_inp_wN: forall w w' p l s s' P Q,
                subsort s' s -> nRefinementN w w' -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                                  (mk_siso (st_receive p [(l,s',(@und w'))]) Q).
Proof. intros.
       specialize(n_a_wN w w' p l s s' (ap_end) 1); intros Hnaw.
       simpl in Hnaw.
       rewrite apend_an in Hnaw.
       rewrite apend_an in Hnaw.
       destruct w'.
       apply Hnaw with (P := sprop).
       easy. easy.
Qed.

Lemma n_out_lN: forall w w' p l l' s s' P Q,
                l <> l' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                        (mk_siso (st_send p [(l',s',(@und w'))]) Q).
Proof. intros.
       specialize(n_b_lN w w' p l l' s s' (bp_end) 1); intros Hnbl.
       simpl in Hnbl.
       rewrite bpend_an in Hnbl.
       apply Hnbl.
       easy.
Qed.

Lemma n_out_sN: forall w w' p l s s' P Q,
                nsubsort s s' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                              (mk_siso (st_send p [(l,s',(@und w'))]) Q).
Proof. intros.
       specialize(n_b_sN w w' p l s s' (bp_end) 1); intros Hnbs.
       simpl in Hnbs.
       rewrite bpend_an in Hnbs.
       apply Hnbs.
       easy.
Qed.

Lemma n_out_wN: forall w w' p l s s' P Q,
                subsort s s' -> nRefinementN w w' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                                                 (mk_siso (st_send p [(l,s',(@und w'))]) Q).
Proof. intros.
       specialize(n_b_wN w w' p l s s' (bp_end) 1); intros Hnbw.
       simpl in Hnbw.
       rewrite bpend_an in Hnbw.
       rewrite bpend_an in Hnbw.
       destruct w'.
       apply Hnbw with (P := sprop).
       easy. easy.
Qed.

Definition eqbp (a b: (participant*string)) :=
  andb (eqb a.1 b.1) (eqb a.2 b.2).

Definition eqbp2 (a b: (participant*actT)) :=
  andb (eqb a.1 b.1) (actTeqb a.2 b.2).

Lemma eq0: forall l (a: (participant*actT)) xs, List.In a l \/ CoInR a xs ->
           CoInR a (appendL l xs).
Proof. intros l.
       induction l; intros.
       destruct H. easy.
       rewrite anl2. easy.
       destruct H.

       inversion H.
       subst.
       rewrite(coseq_eq(appendL (a0 :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       (Delay(cocons a0 (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       (Delay(cocons a (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       simpl in H2.
       apply act_eqb_eq in H2.
       inversion H1. inversion H2.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H1.
       rewrite Bool.andb_false_iff in H1.
       destruct H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       apply IHl. left. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       apply act_neqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       apply IHl. left. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp in H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       (Delay(cocons a (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       apply act_eqb_eq in H1.
       inversion H0. inversion H1.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H0.
       rewrite Bool.andb_false_iff in H0.
       destruct H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       apply IHl. right. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       apply act_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       apply IHl. right. easy.
Qed.

Lemma eq0A: forall l (a: (participant*actT)) xs, List.In a l \/ CoInRA (upaco2 CoInRA bot2) a xs ->
            CoInRA (upaco2 CoInRA bot2) a (appendL l xs).
Proof. intros l.
       induction l; intros.
       destruct H. easy.
       rewrite anl2. easy.
       destruct H.

       inversion H.
       subst.
       rewrite(coseq_eq(appendL (a0 :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp2 in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       apply act_eqb_eq in H2.
       inversion H1. inversion H2.
       simpl in *. subst.
       easy.

       unfold eqbp in H1.
       rewrite Bool.andb_false_iff in H1.
       destruct H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       unfold upaco2. left. pfold.
       apply IHl. left. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       apply act_neqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       unfold upaco2. left. pfold.
       apply IHl. left. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp2 in H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       apply act_eqb_eq in H1.
       inversion H0. inversion H1.
       simpl in *. subst.
       easy.

       unfold eqbp in H0.
       rewrite Bool.andb_false_iff in H0.
       destruct H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       unfold upaco2. left. pfold.
       apply IHl. right. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       apply act_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       unfold upaco2. left. pfold.
       apply IHl. right. easy.
Qed.

Lemma eq0Anew: forall l (a: (participant*actT)) xs, List.In a l \/ CoInR a xs ->
            CoInR a (appendL l xs).
Proof. intros l.
       induction l; intros.
       destruct H. easy.
       rewrite anl2. easy.
       destruct H.

       inversion H.
       subst.
       rewrite(coseq_eq(appendL (a0 :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := a0) (ys := (appendL l xs)). simpl. easy. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp2 in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := a0) (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       apply act_eqb_eq in H2.
       inversion H1. inversion H2.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H1.
       rewrite Bool.andb_false_iff in H1.
       destruct H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
(*        unfold upaco2. left. pfold. *)
       apply IHl. left. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := a) (ys := (appendL l xs)). simpl. easy. 
       apply act_neqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
(*        unfold upaco2. left. pfold. *)
       apply IHl. left. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp2 in H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := a) (ys := (appendL l xs)). simpl. easy.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       apply act_eqb_eq in H1.
       inversion H0. inversion H1.
       simpl in *. subst.
       easy.

       unfold eqbp in H0.
       rewrite Bool.andb_false_iff in H0.
       destruct H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
(*        unfold upaco2. left. pfold. *)
       apply IHl. right. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := a) (ys := (appendL l xs)). simpl. easy. 
       apply act_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
(*        unfold upaco2. left. pfold. *)
       apply IHl. right. easy.
Qed.

Lemma eq1b: forall n p b l s w,
CoInR (p, snd) (act (merge_bp_contn p b (p ! [(l, s, w)]) n)).
Proof. intros. rewrite h0.
       apply eq0.
       right.
       rewrite(coseq_eq(act (p ! [(l, s, w)]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 (p, snd)
       (Delay(cocons (p, snd) (act w)))
       (p, snd)
       (act w)
       ); intro Ha.
       apply Ha. simpl. easy. easy.
Qed.

Lemma act_rec: forall n p b l s s0 s1 s2 w,
(act (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) (n.+1)))
=
Delay (cocons (s, rcv) (act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) n)))).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)])))).
       unfold coseq_id. simpl. easy.
       simpl.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) n))))).
       unfold coseq_id. simpl.
       simpl in IHn.
       easy.
Qed.

Lemma merge_eq4: forall p b1 b2 l s w,
merge_bp_cont p b1 (p ! [(l, s, w)]) =
merge_bp_cont p b2 (p ! [(l, s, w)]) ->
merge_bp_cont p b1 w =
merge_bp_cont p b2 w.
Proof. intros p b1.
       induction b1; intros.
       case_eq b2; intros. subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l, s2, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 bp_end) w)).
       simpl.
       rewrite bpend_an. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H.
       rewrite(siso_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       inversion H.
       subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n s2 s3) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)).
       simpl.
       case_eq b; intros.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s4) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n1 s s0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s4 b0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       inversion H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       simpl. subst.
       specialize(IHb1 (bp_end) l s2 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s2 w).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) w)).
       simpl.
       rewrite IHb1. easy. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst. rewrite bpend_an in H. easy.

       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) w)).
       simpl.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq( merge_bp_cont p (bp_send q0 n0 s2 s3) w)).
       simpl.
       specialize(IHb1 (bp_end) l s1 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s1 w).
       rewrite IHb1. 
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)). simpl.
       easy.
       easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s0 s1) (p ! [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s0 s1 b) (p ! [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite bpend_an. easy.
Qed.

Lemma merge_eq2: forall p a1 a2 l s w,
merge_ap_cont p a1 (p & [(l, s, w)]) =
merge_ap_cont p a2 (p & [(l, s, w)]) ->
merge_ap_cont p a1 w =
merge_ap_cont p a2 w.
Proof. intros p a1.
       induction a1; intros.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq( merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a1; intros.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q n1 s s0 a) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a1) w)).
       simpl.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       rewrite (IHa1 a l s1 w). easy. easy.
       case_eq a2; intros.
       subst. easy. subst. easy. subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s0 s1 a) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       easy.
Qed.

Lemma merge_eq: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [(l1, s1, w1)]) =
  merge_ap_cont p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.
       case_eq a; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite apend_an in H. inversion H. subst. easy.
       subst. rewrite apend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (ap_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite apend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa a0 l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       destruct a2.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a2) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       easy.
Qed.

Lemma merge_eqc: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [(l1, s1, w1)]) =
  merge_cp_cont p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s5) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       
       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.
       inversion H. subst. easy.

       rewrite apend_an in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s3) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       easy.
Qed.

Lemma merge_eqc2: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_cp_cont p a1 (p & [(l1, s1, w1)]) =
  merge_cp_cont p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s5) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.

       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       inversion H. subst. easy.

       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst. easy.

       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.

       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4.
       subst.
       rewrite cpend_an in H4. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 a) (p & [(l1, s2, w1)]))) in H.
       simpl in H.

       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H. subst. rewrite H4.

       specialize (IHa (cp_end) l1 l2 s2 s3 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.

       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa c l1 l2 s2 s3 w1 w2).
       apply IHa. easy.

       subst.
       rewrite cpend_an in H. easy.
       rewrite cpend_an in H.

       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s3) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
Qed.

Lemma merge_eqac: forall p a c l s w,
 merge_ap_cont p a (p & [(l, s, w)]) =
 merge_cp_cont p c (p & [(l, s, w)]) ->
 merge_ap_cont p a w =
 merge_cp_cont p c w.
Proof. intros p a.
       induction a; intros.
       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       case_eq c0; intros.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s4) (p & [(l, s1, w)]))) in H4.
       simpl in H4.
       easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s4 c) (p & [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst. rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.

       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s2 s3 a) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl.
       subst.
       specialize(IHa (cp_end) l s1 w).
       rewrite IHa. rewrite cpend_an. easy.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s2 s3 a) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       specialize(IHa c0 l s1 w).
       rewrite IHa. easy. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq( merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.

       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s0 s1 c0) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (p & [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c0) (p & [(l, s, w)]))) in H. 
       simpl in H. easy.
       rewrite cpend_an. easy.
Qed.

Lemma merge_eq3: forall p b1 b2 l1 l2 s1 s2 w1 w2,
  merge_bp_cont p b1 (p ! [(l1, s1, w1)]) =
  merge_bp_cont p b2 (p ! [(l2, s2, w2)]) -> (p ! [(l1, s1, w1)]) = (p ! [(l2, s2, w2)]).
Proof. intros p b.
       induction b; intros.
       simpl.
       case_eq b2; intros.
       simpl.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(siso_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(siso_eq( merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite bpend_an in H4. easy.

       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq( merge_bp_cont p (bp_merge q n s4 s5 b) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite bpend_an in H. simpl in H. easy.

       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s5) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq( merge_bp_cont p (bp_send q n1 s s0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s5 b0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4.  inversion H4. easy.
       subst. rewrite bpend_an in H4. easy.

       subst. rewrite bpend_an in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]) )) in H.
       simpl in H. inversion H. subst. easy.

       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l1, s2, w1)]))) in H.
       simpl in H. inversion H.

       case_eq b2; intros.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H.
       rewrite H5.
       specialize(IHb (bp_end) l1 l2 s2 s3 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b0) (p ! [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHb b0 l1 l2 s2 s3 w1 w2).
       apply IHb. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s4 s5 b0) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H. easy.

       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. rewrite H4.
       specialize(IHb (bp_end) l1 l2 s1 s2 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H.
       specialize(IHb b0 l1 l2 s1 s2 w1 w2).
       apply IHb. easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.

       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s3) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s3 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite bpend_an in H. easy.
Qed.

Lemma case11: forall n p q a l l' s s' w w',
merge_ap_contn p a (p & [(l, s, w)]) n = q ! [(l', s', w')] -> False.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       subst.
       simpl in H.

       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1)
      (merge_ap_contn p (ap_receive q0 n0 s0 s1) (p & [(l, s, w)]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0)
      (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (p & [(l, s, w)]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite apend_ann in H.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       simpl in H. easy.
Qed.

Lemma case12_1: forall n p q a l l' s s' w w',
p & [(l, s, w)] = merge_ap_contn p a (q ! [(l', s', w')]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1) (merge_ap_contn p (ap_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0) (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite apend_ann in H.
       rewrite apend_an in H. easy.
Qed.

Lemma case12_2: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_ap_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n1 s s0 a0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite apend_an in H4. easy.
       subst. rewrite apend_an in H.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]) )) in H.
       simpl in H.
       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(siso_eq( merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (ap_end) l l' s1 s' w w').
       apply IHa1.
       rewrite apend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 a l l' s1 s' w w').
       apply IHa1. easy.
       subst. rewrite apend_an in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s0 s1 a) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite apend_an in H. easy.
Qed.

Lemma case12_1c2: forall p c l l' s s' w w',
isInCp p c = true ->
p & [(l, s, w)] = merge_cp_cont p c (p & [(l', s', w')]) ->  False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l', s', w')]))) in H0.
         simpl in H0.
         inversion H0. subst. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l', s', w')]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l', s', w')]))) in H0.
         simpl in H0. easy.
       - simpl in *. easy.
Qed.

Lemma case12_1c: forall n p q a l l' s s' w w',
p & [(l, s, w)] = merge_cp_contn p a (q ! [(l', s', w')]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s0 s1) (merge_cp_contn p (cp_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s0 s1 c) (merge_cp_contn p (cp_mergea q0 n0 s0 s1 c) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (merge_cp_contn p (cp_send s0 s1 s2) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (merge_cp_contn p (cp_merge s0 s1 s2 c) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy. 
       subst.
       rewrite cpend_ann in H.
       rewrite cpend_an in H. easy.
Qed.

Lemma case12_1d: forall n p q a l l' s s' w w',
p & [(l, s, w)] = merge_dp_contn p a (q ! [(l', s', w')]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q0 n0 s0 s1) (merge_dp_contn p (dp_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q0 n0 s0 s1 d) (merge_dp_contn p (dp_mergea q0 n0 s0 s1 d) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_send q0 n0 s0 s1) (merge_dp_contn p (dp_send q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q0 n0 s0 s1 d) (merge_dp_contn p (dp_merge q0 n0 s0 s1 d) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy. 
       subst.
       rewrite dpend_ann in H.
       rewrite dpend_an in H. easy.
Qed.

Lemma case12_2c2: forall p c a l1 s1 l2 s2 w1 w2,
isInCp p c = true ->
merge_ap_cont p a (p & [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) -> False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0.
         case_eq a; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H0.
           simpl in H0.
           inversion H0.
           subst.
           apply (IHc (ap_end) l1 s1 l2 s2 w1 w2).
           easy. rewrite apend_an. easy.
        + subst.
          rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l1, s1, w1)]))) in H0.
          simpl in H0.
          inversion H0.
          subst.
          apply (IHc a0 l1 s1 l2 s2 w1 w2).
          easy. easy.
        + subst.
          rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l1, s1, w1)]))) in H0.
          simpl in H0.
          inversion H0. subst. easy.
       - case_eq a; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
       - case_eq a; intros.
         + subst.
           rewrite(siso_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
       - simpl in *. easy.
Qed.

Lemma case12_2c: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_cp_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n1 s s0 c0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s4) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s4 c0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.

       subst.
       rewrite cpend_an in H4. easy.

       subst.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]) )) in H.
       simpl in H. easy.

       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (cp_end) l l' s1 s' w w').
       apply IHa1.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 c l l' s1 s' w w').
       apply IHa1. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.

       subst. rewrite cpend_an in H.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n s0 s1 c) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
Qed.

Lemma case12_2d: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_dp_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq d; intros.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_mergea q0 n1 s s0 d0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_send q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_merge q0 n1 s s0 d0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.

       subst.
       rewrite dpend_an in H4. easy.

       subst.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_send q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite dpend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.

       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (dp_end) l l' s1 s' w w').
       apply IHa1.
       rewrite dpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 d l l' s1 s' w w').
       apply IHa1. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_send q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.

       subst. rewrite dpend_an in H.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_dp_cont p (dp_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_mergea q0 n s0 s1 d) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_send q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_merge q0 n s0 s1 d) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite dpend_an in H. easy.
Qed. 

Lemma refact_eq1: forall p1 p2 l1 l2 s1 s2 w1 w2, upaco2 refinementR bot2 (p1 & [(l1,s1,w1)]) (p2 ! [(l2,s2,w2)]) -> False.
Proof. intros.
       unfold upaco2 in H.
       destruct H.
       punfold H.
       inversion H.
       subst.
       apply case11 in H5. easy.
       apply refinementR_mon.
       easy.
Qed.

Lemma das: forall n q,
(listAp q (napp n [])) = ap_end.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. easy.
Qed.

Lemma dbs: forall n q,
(listBp q (napp n [])) = bp_end.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. easy.
Qed.

Lemma dcs: forall n q,
(listCp q (napp n [])) = cp_end.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. easy.
Qed.

Lemma dsa: forall l p w,
CoInRA (upaco2 CoInRA bot2) (p, rcv)
       (appendL l (act w)) ->
In (p, rcv) l \/
CoInRA (upaco2 CoInRA bot2) (p, rcv) (act w).
Proof. intro l.
       induction l; intros.
       - simpl. right. rewrite anl2 in H. easy.
       - inversion H.
         subst. simpl in H0. inversion H0.
         subst.
         simpl.
         left. left. easy.
         subst. simpl.
         rewrite or_assoc.
         right. apply IHl.
         simpl in H0. inversion H0.
         subst.
         unfold upaco2 in H2.
         destruct H2.
         punfold H2.
         apply CoIn_mon.
         easy.
Qed.

Lemma dsanew: forall l p w,
CoInR (p, rcv) (appendL l (act w)) ->
In (p, rcv) l \/
CoInR (p, rcv) (act w).
Proof. intro l.
       induction l; intros.
       - simpl. right. rewrite anl2 in H. easy.
       - inversion H.
         subst. simpl in H0. inversion H0.
         subst.
         simpl.
         left. left. easy.
         subst. simpl.
         rewrite or_assoc.
         right. apply IHl.
         simpl in H0. inversion H0.
         subst.
         easy.
Qed.

Lemma dsb: forall l p w,
CoInRA (upaco2 CoInRA bot2) (p, snd)
       (appendL l (act w)) ->
In (p, snd) l \/
CoInRA (upaco2 CoInRA bot2) (p, snd) (act w).
Proof. intro l.
       induction l; intros.
       - simpl. right. rewrite anl2 in H. easy.
       - inversion H.
         subst. simpl in H0. inversion H0.
         subst.
         simpl.
         left. left. easy.
         subst. simpl.
         rewrite or_assoc.
         right. apply IHl.
         simpl in H0. inversion H0.
         subst.
         unfold upaco2 in H2.
         destruct H2.
         punfold H2.
         apply CoIn_mon.
         easy.
Qed.

Lemma dsbnew: forall l p w,
CoInR (p, snd) (appendL l (act w)) ->
In (p, snd) l \/
CoInR (p, snd) (act w).
Proof. intro l.
       induction l; intros.
       - simpl. right. rewrite anl2 in H. easy.
       - inversion H.
         subst. simpl in H0. inversion H0.
         subst.
         simpl.
         left. left. easy.
         subst. simpl.
         rewrite or_assoc.
         right. apply IHl.
         simpl in H0. inversion H0.
         subst.
         easy.
Qed.

Lemma notinA: forall q a p,
In (p, snd) (actA q a) -> False.
Proof. intros q a.
       induction a; intros.
       - simpl in H. destruct H; easy.
       - simpl in H. destruct H. easy. 
         apply (IHa p). easy.
       - simpl in H. easy.
Qed.

Lemma bsd2: forall n p q a w,
CoIn (p, snd) (act (merge_ap_cont q (ApnA q a n) w)) ->
CoInRA (upaco2 CoInRA bot2) (p, snd) (act w).
Proof. intro n.
       induction n; intros.
       - unfold ApnA in H. simpl in H.
         rewrite apend_an in H. 
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
       - unfold ApnA in H. simpl in H.
         simpl.
         case_eq a; intros.
         subst.
         rewrite mergeSw in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. 
         simpl in H0. inversion H0. subst.
         unfold upaco2 in H2.
         destruct H2.
         punfold H2.
         specialize(IHn p q (ap_receive q0 n0 s s0) w).
         apply IHn. unfold ApnA. simpl.
         pfold. easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.

         subst.
         simpl in H.
         unfold CoIn in H.
         unfold upaco2 in H.
         punfold H.
         rewrite(siso_eq((merge_ap_cont q (ap_merge q0 n0 s s0 (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0)))) w))) in H.
         simpl in H.
         rewrite(coseq_eq(act (q0 & [(s, s0, merge_ap_cont q (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w)]))) in H.
         unfold coseq_id in H. simpl in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         simpl in H0.
         inversion H0.
         subst.
         inversion H.
         subst.
         simpl in H3. inversion H3.
         subst. simpl in H3.
         inversion H3. subst.
         unfold upaco2 in H5.
         destruct H5. punfold H5.
         specialize(IHn p q (ap_merge q0 n0 s s0 a0) w).
         apply IHn.
         unfold ApnA. simpl.
         pfold.
         rewrite mergeSw in H5.
         rewrite hm1a in H5.
         apply dsb in H5.
         destruct H5.
         apply notinA in H5. easy.

         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.

         subst. simpl in *.
         rewrite das in H.
         rewrite apend_an in H.
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
Qed.

Lemma bsd2new: forall n p q a w,
CoInR (p, snd) (act (merge_ap_cont q (ApnA q a n) w)) ->
CoInR (p, snd) (act w).
Proof. intro n.
       induction n; intros.
       - unfold ApnA in H. simpl in H.
         rewrite apend_an in H. easy.
       - unfold ApnA in H. simpl in H.
         simpl.
         case_eq a; intros.
         subst.
         rewrite mergeSw in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. 
         simpl in H0. inversion H0. subst.
         specialize(IHn p q (ap_receive q0 n0 s s0) w).
         apply IHn. unfold ApnA. simpl. easy.

         subst.
         simpl in H.
         rewrite(siso_eq((merge_ap_cont q (ap_merge q0 n0 s s0 (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0)))) w))) in H.
         simpl in H.
         rewrite(coseq_eq(act (q0 & [(s, s0, merge_ap_cont q (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w)]))) in H.
         unfold coseq_id in H. simpl in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         simpl in H0.
         inversion H0.
         subst.
         inversion H.
         subst.
         simpl in H3. inversion H3.
         subst. simpl in H3.
         inversion H3. subst.
         specialize(IHn p q (ap_merge q0 n0 s s0 a0) w).
         apply IHn.
         unfold ApnA. simpl.
         rewrite mergeSw in H5.
         rewrite hm1a in H5.
         apply dsbnew in H5.
         destruct H5.
         apply notinA in H5. easy.
         easy.

         subst. simpl in *.
         rewrite das in H.
         rewrite apend_an in H. easy.
Qed.

Lemma bsd: forall n p q b w,
         CoIn (p, rcv) (act (merge_bp_cont q (BpnA q b n) w))
         ->
         In (p, rcv) (actBn q b n) \/
         CoInRA (upaco2 CoInRA bot2) (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - unfold BpnA in H. simpl in H.
         rewrite bpend_an in H. right. 
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
       - unfold BpnA in H. simpl in H.
         simpl.
         case_eq b; intros.
         subst.
         rewrite mergeSw3 in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold BpnA.
         simpl.

         unfold upaco2  in H2.
         destruct H2.
         pfold.
         punfold H2.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.

         (**)
         unfold BpnA in H. simpl in H.
         simpl.
         rewrite mergeSw3 in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H1.
         inversion H1. subst.
         rewrite or_assoc.
         right.
         apply IHn.
         simpl in H1.
         inversion H1.
         subst.
         unfold BpnA.
         pfold.
         simpl.
         unfold upaco2 in H3.
         destruct H3. 
         punfold H0.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
         (**)

         (*mergea*)
         subst.
         rewrite mergeSw3 in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.

         unfold upaco2  in H2.
         destruct H2.
         punfold H2.
         rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b0) (merge_bp_cont q (listBp q (napp n (bpList q (bp_mergea s s0 s1 b0)))) w))) in H.
         simpl in H.
         inversion H.
         subst.
         simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         inversion H3.
         subst.

         unfold BpnA.
         rewrite hm1 in H5.

         unfold upaco2  in H5.
         destruct H5.
         punfold H5.
         apply dsa in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold BpnA.
         pfold.
         simpl.
         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
        (*mergea*)

         (*merge*)
         subst.
         rewrite mergeSw3 in H.
         unfold CoIn in H.
         punfold H.
         unfold CpnA.
         rewrite hm1 in H.

         apply dsa in H.
         destruct H.
         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         simpl in H.
         destruct H. easy.
         right. left. left. easy.
         simpl.
         rewrite or_assoc.
         right.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold CpnA.
         pfold. easy.

         apply CoIn_mon.

         subst. simpl in *.
         simpl in H.
         rewrite dbs in H.
         rewrite bpend_an in H.
         right.
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
Qed.

Lemma bsdnew: forall n p q b w,
         CoInR (p, rcv) (act (merge_bp_cont q (BpnA q b n) w))
         ->
         In (p, rcv) (actBn q b n) \/
         CoInR (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - unfold BpnA in H. simpl in H.
         rewrite bpend_an in H. right. easy.
       - unfold BpnA in H. simpl in H.
         simpl.
         case_eq b; intros.
         subst.
         rewrite mergeSw3 in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold BpnA.
         simpl. easy.

         (**)
         unfold BpnA in H. simpl in H.
         simpl.
         rewrite mergeSw3 in H.
         inversion H.
         subst.
         simpl in H1.
         inversion H1. subst.
         rewrite or_assoc.
         right.
         apply IHn.
         simpl in H1.
         inversion H1.
         subst.
         unfold BpnA. easy.
         (**)

         (*mergea*)
         subst.
         rewrite mergeSw3 in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.

         rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b0) (merge_bp_cont q (listBp q (napp n (bpList q (bp_mergea s s0 s1 b0)))) w))) in H.
         simpl in H.
         inversion H.
         subst.
         simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         inversion H3.
         subst.

         unfold BpnA.
         rewrite hm1 in H5.

         apply dsanew in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold BpnA. easy.
        (*mergea*)

         (*merge*)
         subst.
         rewrite mergeSw3 in H.
         unfold CpnA.
         rewrite hm1 in H.

         apply dsanew in H.
         destruct H.
         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         simpl in H.
         destruct H. easy.
         right. left. left. easy.
         simpl.
         rewrite or_assoc.
         right.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold CpnA.
         easy.

         subst. simpl in *.
         simpl in H.
         rewrite dbs in H.
         rewrite bpend_an in H.
         right. easy.
Qed.

Lemma csd: forall n p q c w,
         CoIn (p, rcv) (act (merge_cp_cont q (CpnA q c n) w))
         ->
         In (p, rcv) (actCn q c n) \/
         CoInRA (upaco2 CoInRA bot2) (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - unfold CpnA in H. simpl in H.
         rewrite cpend_an in H. right. 
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
       - unfold CpnA in H. simpl in H.
         simpl.
         case_eq c; intros.
         subst.
         rewrite mergeSw4 in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold CpnA.
         simpl.

         unfold upaco2  in H2.
         destruct H2.
         pfold.
         punfold H2.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.

         (*mergea*)
         subst.
         rewrite mergeSw4 in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.

         unfold upaco2  in H2.
         destruct H2.
         punfold H2.
         rewrite(siso_eq(merge_cp_cont q (cp_mergea q0 n0 s s0 c0) (merge_cp_cont q (listCp q (napp n (cpList q (cp_mergea q0 n0 s s0 c0)))) w))) in H.
         simpl in H.
         inversion H.
         subst.
         simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         inversion H3.
         subst.

         unfold CpnA.
         rewrite hm1c in H5.

         unfold upaco2  in H5.
         destruct H5.
         punfold H5.
         apply dsa in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold CpnA.
         pfold.
         simpl.
         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
        (*mergea*)

         (**)
         unfold CpnA in H. simpl in H.
         simpl.
         rewrite mergeSw4 in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H1.
         inversion H1. subst.
         rewrite or_assoc.
         right.
         apply IHn.
         simpl in H1.
         inversion H1.
         subst.
         unfold CpnA.
         pfold.
         simpl.
         unfold upaco2 in H3.
         destruct H3. 
         punfold H0.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
         (**)

         (*merge*)
         subst.
         rewrite mergeSw4 in H.
         unfold CoIn in H.
         punfold H.
         unfold CpnA.
         rewrite hm1c in H.

         apply dsa in H.
         destruct H.
         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         simpl in H.
         destruct H. easy.
         right. left. left. easy.
         simpl.
         rewrite or_assoc.
         right.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold CpnA.
         pfold. easy.

         apply CoIn_mon.

         subst. simpl in *.
         simpl in H.
         rewrite dcs in H.
         rewrite cpend_an in H.
         right.
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
Qed.

Lemma csdnew: forall n p q c w,
         CoInR (p, rcv) (act (merge_cp_cont q (CpnA q c n) w))
         ->
         In (p, rcv) (actCn q c n) \/
         CoInR (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - unfold CpnA in H. simpl in H.
         rewrite cpend_an in H. right. easy.
       - unfold CpnA in H. simpl in H.
         simpl.
         case_eq c; intros.
         subst.
         rewrite mergeSw4 in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold CpnA.
         simpl. easy.

         (*mergea*)
         subst.
         rewrite mergeSw4 in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.

         rewrite(siso_eq(merge_cp_cont q (cp_mergea q0 n0 s s0 c0) (merge_cp_cont q (listCp q (napp n (cpList q (cp_mergea q0 n0 s s0 c0)))) w))) in H.
         simpl in H.
         inversion H.
         subst.
         simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         inversion H3.
         subst.

         unfold CpnA.
         rewrite hm1c in H5.

         apply dsanew in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold CpnA. easy.
        (*mergea*)

         (**)
         unfold CpnA in H. simpl in H.
         simpl.
         rewrite mergeSw4 in H.
         inversion H.
         subst.
         simpl in H1.
         inversion H1. subst.
         rewrite or_assoc.
         right.
         apply IHn.
         simpl in H1.
         inversion H1.
         subst.
         unfold CpnA. easy.
         (**)

         (*merge*)
         subst.
         rewrite mergeSw4 in H.
         unfold CpnA.
         rewrite hm1c in H.

         apply dsanew in H.
         destruct H.
         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         simpl in H.
         destruct H. easy.
         right. left. left. easy.
         simpl.
         rewrite or_assoc.
         right.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold CpnA.
         easy.

         subst. simpl in *.
         simpl in H.
         rewrite dcs in H.
         rewrite cpend_an in H.
         right. easy.
Qed.

Lemma asd: forall n p q a w,
         CoIn (p, rcv) (act (merge_ap_cont q (ApnA q a n) w))
         ->
         In (p, rcv) (actAn q a n) \/
         CoInRA (upaco2 CoInRA bot2) (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - simpl in H. unfold ApnA in H. simpl in H.
         rewrite apend_an in H. right. 
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
       - unfold ApnA in H. simpl in H.
         simpl.
         case_eq a; intros.
         subst.
         rewrite mergeSw in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold ApnA.
         simpl.

         unfold upaco2  in H2.
         destruct H2.
         pfold.
         punfold H2.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.

         subst.
         rewrite mergeSw in H.
         unfold CoIn in H.
         punfold H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.

         unfold upaco2  in H2.
         destruct H2.
         punfold H2.
         rewrite(siso_eq((merge_ap_cont q (ap_merge q0 n0 s s0 a0) (merge_ap_cont q (listAp q (napp n (apList q (ap_merge q0 n0 s s0 a0)))) w)))) in H.
         simpl in H.
         inversion H.
         subst.
         simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         inversion H3.
         subst.

         unfold ApnA.
         rewrite hm1a in H5.

         unfold upaco2  in H5.
         destruct H5.
         punfold H5.
         apply dsa in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold ApnA.
         pfold.
         simpl.
         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
         easy.
         apply CoIn_mon.
         subst. simpl in *.
         rewrite das in H.
         rewrite apend_an in H.
         right.
         unfold CoIn in H.
         punfold H.
         apply CoIn_mon.
Qed.

Lemma asdnew: forall n p q a w,
         CoInR (p, rcv) (act (merge_ap_cont q (ApnA q a n) w))
         ->
         In (p, rcv) (actAn q a n) \/
         CoInR (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - simpl in H. unfold ApnA in H. simpl in H.
         rewrite apend_an in H. right. easy.
       - unfold ApnA in H. simpl in H.
         simpl.
         case_eq a; intros.
         subst.
         rewrite mergeSw in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         right.
         apply IHn.
         unfold ApnA.
         simpl. easy.

         subst.
         rewrite mergeSw in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         inversion H0. subst.

         simpl.
         rewrite or_assoc.
         rewrite in_app_iff.
         rewrite or_assoc.
         right.

         rewrite(siso_eq((merge_ap_cont q (ap_merge q0 n0 s s0 a0) (merge_ap_cont q (listAp q (napp n (apList q (ap_merge q0 n0 s s0 a0)))) w)))) in H.
         simpl in H.
         inversion H.
         subst.
         simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         inversion H3.
         subst.

         unfold ApnA.
         rewrite hm1a in H5.
         apply dsanew in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold ApnA.
         easy.

         subst. simpl in *.
         rewrite das in H.
         rewrite apend_an in H.
         right. easy.
Qed.

Lemma helperAp: forall p a q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_ap_cont p a (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act w1).
Proof. intros p a.
       induction a; intros.
       - rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         pfold. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. rewrite hm1a. pfold. apply eq0A. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite apend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperApnew: forall p a q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_ap_cont p a (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p a.
       induction a; intros.
       - rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. rewrite hm1a. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite apend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperCp: forall p c q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         pfold. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. rewrite hm1c. pfold. apply eq0A. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq( merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite cpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperCpnew: forall p c q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. rewrite hm1c. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq( merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite cpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperBp: forall p b q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_bp_cont p b (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         pfold. 
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. 
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0.
         inversion H0. rewrite hm1. pfold. apply eq0A. right.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperBpnew: forall p b q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_bp_cont p b (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. 
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0.
         inversion H0. rewrite hm1. apply eq0Anew. right.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperBps: forall p b q l1 l2 s1 s2 w1 w2, 
q & [(l1, s1, w1)] = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoIn (p,snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst. 
         pfold. 
         rewrite(coseq_eq((act (p ! [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H.
         simpl in H.
         easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1. pfold. apply eq0A. right.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite bpend_an in H. easy.
Qed.

Lemma helperBpsnew: forall p b q l1 l2 s1 s2 w1 w2, 
q & [(l1, s1, w1)] = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoInR (p,snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst. 
         rewrite(coseq_eq((act (p ! [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H.
         simpl in H.
         easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1. apply eq0Anew. right.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite bpend_an in H. easy.
Qed.

Lemma helperCp2: forall p c q l1 l2 s1 s2 w1 w2, 
q ! [(l1, s1, w1)] = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H.
         simpl in H.
         inversion H. subst. 
         pfold. 
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1c. pfold. apply eq0A. right.
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite cpend_an in H. easy. 
Qed.

Lemma helperCp2new: forall p c q l1 l2 s1 s2 w1 w2, 
q ! [(l1, s1, w1)] = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H.
         simpl in H.
         inversion H. subst. 
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1c. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite cpend_an in H. easy. 
Qed.

Lemma helperBp2: forall p b q l1 l2 s1 s2 w1 w2, 
q ! [(l1, s1, w1)] = merge_bp_cont p b (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [(l2, s3, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p & [(l2, s2, w2)]))) in H.
         simpl in H.
         inversion H. subst. 
         pfold. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 c) (p & [(l2, s3, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 c) (p & [(l2, s2, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1. pfold. apply eq0A. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1A with (ys := (act w2)). simpl. easy.
       - rewrite bpend_an in H. easy. 
Qed.

Lemma helperBp2new: forall p b q l1 l2 s1 s2 w1 w2, 
q ! [(l1, s1, w1)] = merge_bp_cont p b (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [(l2, s3, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p & [(l2, s2, w2)]))) in H.
         simpl in H.
         inversion H. subst. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 c) (p & [(l2, s3, w2)]))) in H.
         simpl in H. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 c) (p & [(l2, s2, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite bpend_an in H. easy. 
Qed.

Lemma helperApCp: forall q a p c l1 l2 s1 s2 w1 w2, 
p <> q ->
merge_ap_cont q a (q & [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq c; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0.
           subst. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_receive q1 n s3 s4) w1))). simpl.
           apply helperCp in H5.
           rewrite(coseq_eq(act (q1 & [(s3, s4, w1)]))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (q1, rcv)) (ys := (act w1)). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. easy. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(siso_eq( merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0. 
           rewrite cpend_an in H0. simpl in H0.
           inversion H0. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_receive p n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s2, w1)]))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit1A with (ys := (act w1)). simpl. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           symmetry in H5.
           rewrite(siso_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq(act (q1 & [(s3, s4, merge_ap_cont q a w1)]))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. 
           intro Hb. apply n0. inversion Hb. easy.
           apply helperAp in H5.
           left.
           unfold CoIn in IHa.
           inversion H0. subst.
           specialize (IHa p (cp_end) l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           rewrite cpend_an. easy.
           easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq((act (q1 & [(s3, s4, merge_ap_cont q a w1)])))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left.
           specialize (IHa p c0 l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite cpend_an in H0. simpl in H0. inversion H0. subst. 
           rewrite(siso_eq((merge_ap_cont q (ap_merge p n l2 s2 a) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s2, merge_ap_cont q a w1)]))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit1A with (ys := (act (merge_ap_cont q a w1))). simpl. easy.
         + rewrite apend_an.
           rewrite apend_an in H0.
           apply helperCp in H0. easy. easy.
Qed.

Lemma helperApCpnew: forall q a p c l1 l2 s1 s2 w1 w2, 
p <> q ->
merge_ap_cont q a (q & [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq c; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0.
           subst. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_receive q1 n s3 s4) w1))). simpl.
           apply helperCpnew in H5.
           rewrite(coseq_eq(act (q1 & [(s3, s4, w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act w1)). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           easy. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(siso_eq( merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0. 
           rewrite cpend_an in H0. simpl in H0.
           inversion H0. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_receive p n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s2, w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w1)). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           symmetry in H5.
           rewrite(siso_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq(act (q1 & [(s3, s4, merge_ap_cont q a w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. 
           intro Hb. apply n0. inversion Hb. easy.
           apply helperApnew in H5.
           inversion H0. subst.
           specialize (IHa p (cp_end) l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           rewrite cpend_an. easy.
           easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq((act (q1 & [(s3, s4, merge_ap_cont q a w1)])))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize (IHa p c0 l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite cpend_an in H0. simpl in H0. inversion H0. subst. 
           rewrite(siso_eq((merge_ap_cont q (ap_merge p n l2 s2 a) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s2, merge_ap_cont q a w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
         + rewrite apend_an.
           rewrite apend_an in H0.
           apply helperCpnew in H0. easy. easy.
Qed.

Lemma helperBpCp: forall q b p c l1 l2 s1 s2 w1 w2, 
merge_bp_cont q b (q ! [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoIn (p,rcv) (act (merge_bp_cont q b w1)).
Proof. intros q b. 
       induction b; intros.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           apply helperCp2 in H4.
           rewrite(siso_eq((merge_bp_cont q (bp_receivea q0 s4 s5) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (q0, rcv)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n. inversion Hb. easy.
           left. easy. 
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_receivea p l2 s3) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s3, w1)]))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit1A with (ys := (act w1)). simpl. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           apply helperCp2 in H4.
           rewrite(siso_eq((merge_bp_cont q (bp_send s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (s3, snd)) (ys := (act (w1))). simpl. easy. easy.
           left. easy. 
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           left.
           specialize (IHb p (cp_end) l1 l2 s2 s3 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           left.
           specialize (IHb p c0 l1 l2 s2 s3 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]) )) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite cpend_an in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_mergea p l2 s3 b) w1))).
           simpl.
           rewrite(coseq_eq(act (p & [(l2, s3, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit1A with (ys := (act (merge_bp_cont q b w1))). simpl. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           left.
           specialize (IHb p (cp_end) l1 l2 s1 s2 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H.
           inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           left.
           specialize (IHb p c0 l1 l2 s1 s2 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - rewrite bpend_an in H.
         rewrite bpend_an.
         apply helperCp2 in H. easy.
Qed.

Lemma helperBpCpnew: forall q b p c l1 l2 s1 s2 w1 w2, 
merge_bp_cont q b (q ! [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act (merge_bp_cont q b w1)).
Proof. intros q b. 
       induction b; intros.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           apply helperCp2new in H4.
           rewrite(siso_eq((merge_bp_cont q (bp_receivea q0 s4 s5) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n. inversion Hb. easy.
           easy. 
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_receivea p l2 s3) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s3, w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w1)). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           apply helperCp2new in H4.
           rewrite(siso_eq((merge_bp_cont q (bp_send s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys := (act (w1))). simpl. easy. easy.
           easy. 
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           specialize (IHb p (cp_end) l1 l2 s2 s3 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           specialize (IHb p c0 l1 l2 s2 s3 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]) )) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite cpend_an in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_mergea p l2 s3 b) w1))).
           simpl.
           rewrite(coseq_eq(act (p & [(l2, s3, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           specialize (IHb p (cp_end) l1 l2 s1 s2 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H.
           inversion H. subst.
           rewrite(siso_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           specialize (IHb p c0 l1 l2 s1 s2 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - rewrite bpend_an in H.
         rewrite bpend_an.
         apply helperCp2new in H. easy.
Qed.

Lemma bsd3: forall p b q l1 l2 s1 s2 w1 w2,
p <> q ->
q ! [(l1, s1, w1)] = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoInRA (upaco2 CoInRA bot2) (p, snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0.
         subst. 
         rewrite(coseq_eq(act (p ! [(l2, s2, w2)]))). unfold coseq_id. simpl.
         apply CoInSplit1A with (ys :=(act (w2))). simpl. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. 
         subst.
         rewrite hm1. apply eq0A. right.
         apply CoInSplit1A with (ys :=(act (w2))). simpl. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma bsd3new: forall p b q l1 l2 s1 s2 w1 w2,
p <> q ->
q ! [(l1, s1, w1)] = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoInR (p, snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0.
         subst. 
         rewrite(coseq_eq(act (p ! [(l2, s2, w2)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w2))). simpl. easy. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. 
         subst.
         rewrite hm1. apply eq0Anew. right.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w2))). simpl. easy. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperApBp: forall q a p b l1 l2 s1 s2 w1 w2, 
merge_ap_cont q a (q & [(l1, s1, w1)]) = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoIn (p,snd) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq b; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
           subst.
           rewrite(siso_eq((merge_ap_cont q (ap_receive s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 & [(s4, s5, w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (s3, rcv)) (ys :=(act w1)). simpl. easy. easy.
           left. pfold.
           apply helperBps in H4. unfold CoIn in H4.
           punfold H4.
           apply CoIn_mon.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H. 
           rewrite bpend_an in H. simpl in H.
           easy.
       - case_eq b; intros.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 & [(s4, s5, merge_ap_cont q a w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           left.
           specialize(IHa p (bp_end) l1 l2 s1 s2 w1 w2).
           unfold CoIn in IHa.
           apply IHa.
           rewrite bpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H.
           inversion H. subst.
           specialize(IHa p b0 l1 l2 s1 s2 w1 w2).
           rewrite(siso_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))). simpl.
           rewrite(coseq_eq (act (s3 & [(s4, s5, merge_ap_cont q a w1)]))). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit2A with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           left.
           apply IHa. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite bpend_an in H. simpl in H. easy.
       - subst.
         rewrite apend_an in H.
         rewrite apend_an.
         apply helperBps in H. easy.
Qed.

Lemma helperApBpnew: forall q a p b l1 l2 s1 s2 w1 w2, 
merge_ap_cont q a (q & [(l1, s1, w1)]) = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoInR (p,snd) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq b; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
           subst.
           rewrite(siso_eq((merge_ap_cont q (ap_receive s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 & [(s4, s5, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys :=(act w1)). simpl. easy. easy.
           apply helperBpsnew in H4. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H. 
           rewrite bpend_an in H. simpl in H.
           easy.
       - case_eq b; intros.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(siso_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 & [(s4, s5, merge_ap_cont q a w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           specialize(IHa p (bp_end) l1 l2 s1 s2 w1 w2). 
           apply IHa.
           rewrite bpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H.
           inversion H. subst.
           specialize(IHa p b0 l1 l2 s1 s2 w1 w2).
           rewrite(siso_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))). simpl.
           rewrite(coseq_eq (act (s3 & [(s4, s5, merge_ap_cont q a w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           apply IHa. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite bpend_an in H. simpl in H. easy.
       - subst.
         rewrite apend_an in H.
         rewrite apend_an.
         apply helperBpsnew in H. easy.
Qed.

Lemma helperBpBp: forall p b1 q b2 l1 l2 s1 s2 w1 w2,
p <> q ->
merge_bp_cont p b1 (p ! [(l1, s1, w1)]) = merge_bp_cont q b2 (q ! [(l2, s2, w2)]) ->
CoInRA (upaco2 CoInRA bot2) (q, snd) (act (merge_bp_cont p b1 w1)).
Proof. intros p b1.
       induction b1; intros.
       - case_eq b2; intros.
         + subst.
           rewrite(siso_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3 in H5.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s4 s5 s6) w1)). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (s4, rcv)) (ys := (act (w1))). simpl. easy. easy.
           left. pfold. easy. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. easy.
       - case_eq b2; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3 in H5.
           rewrite(siso_eq(merge_bp_cont p (bp_send q1 n s3 s4) w1)). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (q1, snd)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. pfold. easy. easy.
         + subst. 
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(siso_eq((merge_bp_cont p (bp_send q0 n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1A with (ys := (act (w1))). simpl. easy.
       - case_eq b2; intros.
         + subst. 
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q (bp_end) l1 l2 s2 s3 w1 w2).
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1)). simpl.
           rewrite(coseq_eq (act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           left. pfold.
           apply IHb1. easy.
           rewrite bpend_an. easy. 
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q b l1 l2 s2 s3 w1 w2).
           rewrite(siso_eq((merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1))). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           left. pfold.
           apply IHb1. easy. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0.
           easy.
       - case_eq b2; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(siso_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. pfold.
           specialize(IHb1 q0 (bp_end) l1 l2 s1 s2 w1 w2).
           apply IHb1. easy.
           rewrite bpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(siso_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. pfold.
           specialize(IHb1 q0 b l1 l2 s1 s2 w1 w2).
           apply IHb1. easy. easy.
         + subst. 
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(siso_eq( (merge_bp_cont p (bp_merge q0 n l2 s2 b1) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1A with (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
       - rewrite bpend_an in H0.
         rewrite bpend_an.
         apply bsd3 in H0. easy. easy.
Qed.

Lemma helperBpBpnew: forall p b1 q b2 l1 l2 s1 s2 w1 w2,
p <> q ->
merge_bp_cont p b1 (p ! [(l1, s1, w1)]) = merge_bp_cont q b2 (q ! [(l2, s2, w2)]) ->
CoInR (q, snd) (act (merge_bp_cont p b1 w1)).
Proof. intros p b1.
       induction b1; intros.
       - case_eq b2; intros.
         + subst.
           rewrite(siso_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3new in H5.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s4 s5 s6) w1)). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act (w1))). simpl. easy. easy.
           easy. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. easy.
       - case_eq b2; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3new in H5.
           rewrite(siso_eq(merge_bp_cont p (bp_send q1 n s3 s4) w1)). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           easy. easy.
         + subst. 
           rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(siso_eq((merge_bp_cont p (bp_send q0 n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (q0, snd)) (ys := (act (w1))). simpl. easy. easy.
       - case_eq b2; intros.
         + subst. 
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q (bp_end) l1 l2 s2 s3 w1 w2).
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1)). simpl.
           rewrite(coseq_eq (act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           apply IHb1. easy.
           rewrite bpend_an. easy. 
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q b l1 l2 s2 s3 w1 w2).
           rewrite(siso_eq((merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1))). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           apply IHb1. easy. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0.
           easy.
       - case_eq b2; intros.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(siso_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize(IHb1 q0 (bp_end) l1 l2 s1 s2 w1 w2).
           apply IHb1. easy.
           rewrite bpend_an. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(siso_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(siso_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize(IHb1 q0 b l1 l2 s1 s2 w1 w2).
           apply IHb1. easy. easy.
         + subst. 
           rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(siso_eq( (merge_bp_cont p (bp_merge q0 n l2 s2 b1) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (q0, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
       - rewrite bpend_an in H0.
         rewrite bpend_an.
         apply bsd3new in H0. easy. easy.
Qed.

Lemma nrefNL: forall w w',  (@und w) ~< (@und w') -> (nRefinementN w w' -> False).
Proof. intros w w' H.
       unfold refinement in H.
       punfold H; [ | apply refinementR_mon].
       intro Ha.
       induction Ha; intros.
       {
         inversion H.
         subst. apply H0.
         rewrite <- H2. 
         apply helperBpsnew in H1.
         unfold act_eq in H5.
         specialize(H5(p,snd)).
         destruct H5 as (H5a,H5b).
         apply H5a in H1.
         rewrite <- mergeeq.
         rewrite hm1a.
         apply eq0Anew.

         rewrite <- mergeeq in H1.
         apply bsd2new in H1.
         right.
         rewrite(coseq_eq(act (p0 & [(l0, s0, w'0)]))). unfold coseq_id.
         simpl.
         apply CoInSplit2 with (y := (p0, rcv)) (ys :=(act (w'0))). simpl. easy. easy.
         easy.

         apply H0.
         rewrite <- H2. 
         case_eq(eqb p0 p); intros.
         rewrite eqb_eq in H6. subst.
         rewrite <- mergeeq3.
         rewrite hm1.
         apply eq0Anew.
         right.
         rewrite(coseq_eq(act (p ! [(l0, s', w'0)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w'0))). simpl. easy. easy.

         rewrite eqb_neq in H6.
         apply bsd3new in H1.
         unfold act_eq in H5.
         specialize(H5(p,snd)).
         destruct H5 as (H5a,H5b).
         rewrite <- mergeeq3.
         rewrite hm1.
         apply eq0Anew.

         assert(CoInR (p, snd) (act w0)).
         { easy. }
         apply H5a in H5.

         rewrite <- mergeeq3 in H5.
         rewrite hm1 in H5.
         apply dsbnew in H5.
         destruct H5.
         left. easy.
         right.
         rewrite(coseq_eq(act (p0 ! [(l0, s', w'0)]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p0, snd)) (ys :=(act (w'0))). simpl. easy.
         intro Hb. apply H6. inversion Hb. easy. easy. easy.

         case_eq b; intros.
         subst.
         rewrite(siso_eq(merge_bp_cont p (bp_receivea s0 s1 s2) (p ! [(l, s, und)]))) in H2.
         simpl in H2. easy.
         subst.
         rewrite(siso_eq(merge_bp_cont p (bp_send q n s0 s1) (p ! [(l, s, und)]))) in H2.
         simpl in H2. easy.
         subst.
         rewrite(siso_eq(merge_bp_cont p (bp_mergea s0 s1 s2 b0) (p ! [(l, s, und)]))) in H2.
         simpl in H2. easy.
         subst.
         rewrite(siso_eq(merge_bp_cont p (bp_merge q n s0 s1 b0) (p ! [(l, s, und)]))) in H2.
         simpl in H2. easy.
         subst.
         rewrite bpend_an in H2. easy.
       }
       { inversion H.
         subst.
         apply H0.
         rewrite <- H2.
         case_eq(eqb p p0); intros.
         rewrite eqb_eq in H6. subst.
         rewrite h1.
         apply eq0Anew.
         right.

         rewrite(coseq_eq((act (p0 & [(l0, s0, w'0)])))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p0, rcv)) (ys := (act w'0)). easy. easy.

         rewrite eqb_neq in H6.
         unfold act_eq in H5.
         specialize(H5(p,rcv)).
         destruct H5 as (H5a, H5b).
         rewrite h1.
         apply eq0Anew.
         rewrite <- mergeeq in H5a.
         apply helperCpnew in H1.
         apply H5a in H1.
         apply asdnew in H1.
         destruct H1.
         left. easy.

         right.
         rewrite(coseq_eq((act (p0 & [(l0, s0, w'0)])))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p0, rcv)) (ys := (act w'0)). simpl. easy.
         unfold not. intro Hn.
         apply H6. inversion Hn. easy. easy. easy.

         apply H0.
         rewrite <- H2.
         apply helperCp2new in H1.
         unfold act_eq in H5.
         specialize(H5(p,rcv)).
         destruct H5 as (H5a, H5b).
         apply H5a in H1.
         rewrite <- mergeeq3 in H1.
         apply bsdnew in H1.
         destruct H1.
         rewrite h0.
         apply eq0Anew.
         left. easy.
         rewrite h0.
         apply eq0Anew.
         right.
         rewrite(coseq_eq((act (p0 ! [(l0, s', w'0)])))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p0, snd)) (ys := (act w'0)). easy. easy.
         easy.

         destruct c. 
         rewrite(siso_eq(merge_cp_cont p (cp_receive q n s0 s1) (p & [(l, s, und)]))) in H2.
         simpl in H2. easy.
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s0 s1 c) (p & [(l, s, und)]))) in H2.
         subst. easy.
         rewrite(siso_eq( merge_cp_cont p (cp_send s0 s1 s2) (p & [(l, s, und)]))) in H2.
         simpl in H2. easy.
         rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (p & [(l, s, und)]))) in H2.
         simpl in H2. easy.
         rewrite cpend_an in H2. easy. 
       }
       { inversion H.
         subst.
         apply H0. rewrite <- H1.
         rewrite <- mergeeq2 in H2.
         apply helperApBpnew in H2.
         unfold act_eq in H5.
         specialize(H5(p,snd)).
         rewrite <- mergeeq2 in H5.
         apply H5 in H2.
         rewrite(coseq_eq(act (p0 & [(l0, s', w0)]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p0, rcv)) (ys := (act w0)). simpl. easy. easy.
         easy.

         apply H0. rewrite <- H1.
         case_eq(eqb p p0); intros.
         rewrite eqb_eq in H6.
         subst.
         rewrite(coseq_eq(act (p0 ! [(l0, s0, w0)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p0, snd)) (ys := (act w0)). simpl. easy. easy.
         rewrite eqb_neq in H6.
         rewrite <- mergeeq3 in H2.
         apply helperBpBpnew in H2.
         unfold act_eq in H5.
         specialize(H5(p,snd)).
         rewrite <- mergeeq3 in H5.
         rewrite(coseq_eq(act (p0 ! [(l0, s0, w0)]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p0, snd)) (ys := (act w0)). simpl. easy.
         intro Hb. apply H6. inversion Hb. easy.
         apply H5. easy. easy.

         destruct b.
         subst. rewrite(siso_eq(merge_bp_cont p (bp_receivea s0 s1 s2) (p ! [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst. rewrite(siso_eq(merge_bp_cont p (bp_send q n s0 s1) (p ! [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst. rewrite(siso_eq(merge_bp_cont p (bp_mergea s0 s1 s2 b) (p ! [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst. rewrite(siso_eq(merge_bp_cont p (bp_merge q n s0 s1 b) (p ! [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst. rewrite(siso_eq(merge_bp_cont p bp_end (p ! [(l, s, und)]))) in H3.
         simpl in H3. easy.
       }
       { inversion H.
         subst.
         apply H0. rewrite <- H1.

         unfold act_eq in H5.
         rewrite <- H1 in H0.
         case_eq(eqb p p0); intro Heq.

         rewrite(coseq_eq(act (p0 & [(l0, s', w0)]))). unfold coseq_id. simpl.
         rewrite eqb_eq in Heq. subst.
         apply CoInSplit1 with (y := (p0, rcv)) (ys := (act w0)). easy. easy.

         rewrite eqb_neq in Heq.

         (****)
         rewrite <- mergeeq2 in H2, H5.
         specialize(H5(p,rcv)).
         destruct H5 as (H5a,H5b).
         apply helperApCpnew in H2.
         apply H5b in H2.
         rewrite(coseq_eq((act (p0 & [(l0, s', w0)])))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p0, rcv)) (ys := (act w0)). simpl. easy.
         intro Hb. apply Heq. inversion Hb. easy.
         exact H2.
         easy.

         rewrite <- mergeeq3 in H2.
         specialize(H5(p,rcv)).
         destruct H5 as (H5a,H5b).
         rewrite <- H1 in H0.
         apply H0.
         apply helperBpCpnew in H2.
         apply bsdnew in H2.
         apply eq0Anew in H2.
         rewrite <- h0 in H2.
         apply CoInSplit2 with (y := (p0, snd)) (ys := (act w0)). simpl. easy. easy.
         apply H5b. easy.

         apply H0.
         case_eq c; intros.
         subst.
         rewrite(siso_eq(merge_cp_cont p (cp_receive q n s0 s1) (p & [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst.
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s0 s1 c0) (p & [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst.
         rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (p & [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst.
         rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c0) (p & [(l, s, und)]))) in H3.
         simpl in H3. easy.
         subst. rewrite cpend_an in H3. easy.
       }
       {
         inversion H.
         subst.

         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         subst.
         rewrite <- mergeeq in H6.
         rewrite <- mergeeq in H6.
         apply merge_eq in H6.
         inversion H6. subst. easy.
         apply refinementR_mon.
         easy.
       }
       { inversion H.
         subst.

         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         subst.
         rewrite <- mergeeq in H6.
         rewrite <- mergeeq in H6.
         apply merge_eq in H6.
         inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         apply refinementR_mon.
         easy.
       }
       { apply IHHa.
         inversion H. subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1. simpl.

         subst.
         rewrite <- mergeeq2 in H6.
         rewrite <- mergeeq2 in H6.
         pose proof H6.
         apply merge_eq in H6.
         rewrite <- mergeeq2 in H8.

         inversion H6. subst.
         apply merge_eq2 in H2.
         rewrite <- mergeeq2.
         rewrite <- mergeeq2 in H1.
         rewrite <- H2.
         easy.
         apply refinementR_mon.
         easy.
       }
       { inversion H.
         subst.
         specialize(case11 n p q a l l' s0 s' w'0 und H5); intros H11.
         easy.
       }
       { inversion H.
         subst. 
         subst.
         rewrite <- mergeeq2 in H6.
         apply case12_2c2 in H6. easy.
         easy.
       } 
       {
         inversion H.
         subst.

         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         subst.
         rewrite <- mergeeq3 in H6.
         rewrite <- mergeeq3 in H6.
         apply merge_eq3 in H6.
         inversion H6. subst. easy.
         apply refinementR_mon.
         easy.
       }
       { inversion H.
         subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         subst.
         rewrite <- mergeeq3 in H6.
         rewrite <- mergeeq3 in H6.
         apply merge_eq3 in H6.
         inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         apply refinementR_mon.
         easy.
       }
       { apply IHHa.
         inversion H. subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.
         simpl.

         subst.
         rewrite <- mergeeq3 in H6.
         rewrite <- mergeeq3 in H6.
         pose proof H6.
         apply merge_eq3 in H6.
         rewrite <- mergeeq3 in H8.

         inversion H6. subst.
         apply merge_eq4 in H2.

         rewrite <- mergeeq3.
         rewrite <- mergeeq3 in H1.
         rewrite <- H2.
         easy.
         apply refinementR_mon.
         easy.
       }
Qed.

Lemma invsingl: forall p l, singleton (p & l) -> exists (l': label) (s: st.sort) (w: st), l = [((l',s),w)].
Proof. intros.
       induction l; intros.
       unfold singleton in H. punfold H. inversion H. 
       apply sI_mon.
       unfold singleton in H. punfold H. inversion H.
       subst. simpl in *.
       exists l0. exists s. exists w. easy. 
       apply sI_mon.
Qed.

Lemma invsingl2: forall p l, singleton (p ! l) -> exists (l': label) (s: st.sort) (w: st), l = [((l',s),w)].
Proof. intros.
       induction l; intros.
       unfold singleton in H. punfold H. inversion H. 
       apply sI_mon.
       unfold singleton in H. punfold H. inversion H.
       subst. simpl in *.
       exists l0. exists s. exists w. easy. 
       apply sI_mon.
Qed.

Lemma sinv: forall w, singleton w ->
                      (exists p l s w', w = st_send p [(l,s,w')] /\ singleton w') \/
                      (exists p l s w', w = st_receive p [(l,s,w')] /\ singleton w') \/
                      (w = st_end).
Proof. intros.
       case_eq w; intros.
       subst. right. right. (*  left.  *) easy.
       subst. right. left.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists s. exists l0. exists s0. exists w.
       split. easy. unfold singleton.
       inversion H1. easy. easy.
       apply sI_mon.
       subst. left.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists s. exists l0. exists s0. exists w.
       split. easy. unfold singleton.
       inversion H1. easy. easy.
       apply sI_mon.
Qed.

Lemma casen1: forall p l s1 s2 w1 w2 P Q,
subsort s2 s1 ->
(nRefinementN (mk_siso (st_receive p [(l, s1, (@und w1))]) P) 
              (mk_siso (st_receive p [(l, s2, (@und w2))]) Q) -> False) ->
(nRefinementN w1 w2 -> False).
Proof. intros.
       apply H0.
       apply n_inp_wN.
       easy.
       easy.
Qed.

Lemma casen2: forall p l s1 s2 w1 w2 P Q,
  subsort s1 s2 ->
  (nRefinementN (mk_siso (st_send p [(l, s1, (@und w1))]) P)
                (mk_siso (st_send p [(l, s2, (@und w2))]) Q) -> False) ->
  (nRefinementN w1 w2 -> False).
Proof. intros.
       apply H0.
       apply n_out_wN.
       easy.
       easy.
Qed.

Lemma hhact: forall p w ys, singleton w -> acts w = coconss (p, rcv) ys ->
  exists l s w', w = (p & [(l,s,w')]).
Proof. intros.
       specialize(sinv w H); intro Hw.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst. 
       rewrite(stream_eq(acts (q ! [(l, s, w')]))) in H0.
       unfold stream_id in H0. simpl in H0.
       inversion H0.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst. 
       rewrite(stream_eq(acts (q & [(l, s, w')]))) in H0.
       unfold stream_id in H0. simpl in H0.
       inversion H0.
       subst.
       exists l. exists s. exists w'. easy.
       subst.
       rewrite(stream_eq(acts (end))) in H0.
       unfold stream_id in H0. simpl in H0.
       easy.
Qed.

Lemma ninReceive: forall w p (Hs: singleton w) (Hnin: CoNInR (p, rcv) (act w)),
  exists c w2, w = merge_cp_cont p c w2 /\ CoNInR (p, rcv) (act w2).
Proof. intros.
       remember (p, rcv) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hnin; intros.
       specialize(sinv w Hs); intro Hw.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst.
       rewrite(coseq_eq(act (q ! [(l, s, w')]))) in Hequ.
       unfold coseq_id in Hequ.
       easy.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst.
       rewrite(coseq_eq(act (q & [(l, s, w')]))) in Hequ.
       unfold coseq_id in Hequ.
       easy.
       exists cp_end. exists st_end.
       rewrite(siso_eq(merge_cp_cont p cp_end (end))). simpl.
       split. easy.
       rewrite(coseq_eq((act (end)))).
       unfold coseq_id. simpl.
       constructor.

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       simpl in H.
       inversion H.
       subst.
       assert((p, rcv) = (p, rcv)) as Ha1 by easy.
       assert(singleton w1) as Ha2.
       { apply extrR in Hs. easy. }
       assert(act w1 = act w1) as Ha3 by easy.
       specialize(IHHnin Ha1 w1 Ha2 Ha3).
       destruct IHHnin as (c1,(w2,(IHN1, IHN2))).
       assert(p <> s) as Ha4.
       { unfold not. intro Hb. apply H0. subst. easy. }
       subst.
       exists (cp_mergea s Ha4 l1 s1 c1). exists w2.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea s Ha4 l1 s1 c1) w2)).
       simpl. split. easy. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       simpl in H. inversion H. subst.
       assert((p, rcv) = (p, rcv)) as Ha1 by easy.
       assert(singleton w1) as Ha2.
       { apply extsR in Hs. easy. }
       assert(act w1 = act w1) as Ha3 by easy.
       specialize(IHHnin Ha1 w1 Ha2 Ha3).
       destruct IHHnin as (c1,(w2,(IHN1, IHN2))).
       exists (cp_merge s l1 s1 c1). exists w2.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s l1 s1 c1) w2)).
       simpl. subst. split; easy.
Qed.

Lemma inReceive: forall w p (Hs: singleton w) (Hin: CoInR (p, rcv) (act w)),
  exists c l s w2, w = merge_cp_cont p c (p & [(l,s,w2)]).
Proof. intros.
       remember (p, rcv) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.
       subst.
       exists cp_end. exists l1. exists s1. exists w1. 
       rewrite cpend_an. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H. 

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H1 w1 H2 H3).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. }
       exists (cp_mergea s H4 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea s H4 l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hs.
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       rewrite Heqw1 in H. simpl in H.
       inversion H.
       symmetry in H6.
       specialize(IHHin H1 w1 H2 H6).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       subst.
       exists (cp_merge s l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.
Qed.

Lemma inSend: forall w p (Hs: singleton w) (Hin: CoInR (p, snd) (act w)),
  exists b l s w2, w = merge_bp_cont p b (p ! [(l,s,w2)]).
Proof. intros.
       remember (p, snd) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       easy.
       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H. subst. 
       exists (bp_end). (* exists 1. *) exists l1. exists s1. exists w1. simpl.
       rewrite bpend_an. easy.
       rewrite Heqv in H0. rewrite Hequ in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H1 w1 H2 H3).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_mergea s l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s l1 s1 b) (p ! [(l2, s2, w3)]))).
       simpl. easy.
       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert (p <> s). unfold not in *. intros. apply H0. subst. easy.
       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy. }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H2 w1 H3 H4).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_merge s H1 l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_bp_cont p (bp_merge s H1 l1 s1 b) (p ! [(l2, s2, w3)]))). simpl. easy.
Qed.

Lemma inReceive_wos: forall w p (Hs: singleton w) (Hin: CoInR (p, rcv) (act w)),
  (forall q, CoInR (q, snd) (act w) -> False) ->
  exists a l s w2, w = merge_ap_cont p a (p & [(l,s,w2)]).
Proof. intros w p Hs Hin Hout.
       remember (p, rcv) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.
       subst.
       exists ap_end. exists l1. exists s1. exists w1. 
       rewrite apend_an. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       assert((forall q : participant, CoInR (q, snd) (act w1) -> False)).
       { intros. apply (Hout q). 
         rewrite(coseq_eq((act (s & [(l1, s1, w1)])))).
         unfold coseq_id. simpl. 
         specialize (CoInSplit2 (q, snd) (Delay(cocons (s, rcv) (act w1))) (s, rcv)  ((act w1))); intros.
         apply H5.
         simpl. easy. easy. easy.
       } 
       specialize(IHHin H1 H4 w1 H2 H3).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. 
       }
       exists (ap_merge s H5 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_ap_cont p (ap_merge s H5 l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(Hout s).
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       subst.
       assert(CoInR (s, snd) (act (s ! [(l1, s1, w1)]))).
       { apply CoInSplit1 with (y := (s, snd)) (ys := (act w1)).
         simpl. easy. easy.
       }
       specialize (Hout H1). easy.
Qed.

Lemma act_eq_neq: forall w w', (act_eq w w' -> False) -> act_neq w w'.
Proof. intros.
       unfold act_eq, act_neq in *.
       apply not_all_ex_not in H.
       destruct H as (a, H).
       exists a.
       unfold iff in H.
       apply not_and_or in H.
       destruct H as [H | H].
       apply imply_to_and in H.
       left. easy.
       apply imply_to_and in H.
       right. easy.
Qed.

Lemma n_a_actNH2: forall p b q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoInR (p,snd) (act (merge_ap_cont q a w2)) -> False),
  nRefinementN (mk_siso (merge_bp_cont p b (p ! [(l,s,w1)])) P)
               (mk_siso (merge_ap_cont q a w2) Q).
Proof. intros.
       specialize (n_outN {| und := w1; sprop := Hw1 |} {| und :=  merge_ap_cont q a w2; sprop := Q |} p b l s ); intros HH.
       apply HH. simpl. easy.
Qed.

Lemma n_a_actNH4: forall p b q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoInR (p,snd) (act (merge_ap_cont q a w2)) -> False),
  nRefinementN (mk_siso (merge_ap_cont q a w2) Q)
               (mk_siso (merge_bp_cont p b (p ! [(l,s,w1)])) P).
Proof. intros.
       specialize (n_out_rN {| und :=  merge_ap_cont q a w2; sprop := Q |}  {| und := w1; sprop := Hw1 |} p b l s ); intros HH.
       apply HH. simpl. easy.
Qed.

Lemma n_a_actNH1: forall p c q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoInR (p,rcv) (act (merge_ap_cont q a w2)) -> False),
  nRefinementN (mk_siso (merge_cp_cont p c (p & [(l,s,w1)])) P)
               (mk_siso (merge_ap_cont q a w2) Q).
Proof. intros.
       specialize (n_inpN {| und := w1; sprop := Hw1 |} {| und :=  merge_ap_cont q a w2; sprop := Q |} p c l s ); intros HH.
       apply HH. simpl. easy.
Qed.

Lemma n_a_actNH3: forall q a p c l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) 
                         (Hw2a: CoInR (p,rcv) (act (merge_ap_cont q a w2)) -> False),
nRefinementN (mk_siso (merge_ap_cont q a w2) Q)
             (mk_siso (merge_cp_cont p c (p & [(l,s,w1)])) P).
Proof. intros.
       specialize (n_inp_rN {| und :=  merge_ap_cont q a w2; sprop := Q |}  {| und := w1; sprop := Hw1 |} p c l s ); intros HH.
       apply HH. simpl. easy.
Qed.

Lemma n_b_actN: forall p l s s' w w' b P Q,
  subsort s s' ->
  (act_neq w (merge_bp_cont p b w')) ->
  nRefinementN (mk_siso (p ! [(l,s,w)]) P)
               (mk_siso (merge_bp_cont p b (p ! [(l,s',w')])) Q).
Proof. intros.
       unfold act_neq in H0.
       destruct H0 as (a1, H0).
       destruct H0 as [H0 | H0].
       destruct a1 as (q,ac).
       destruct H0 as (Ha,Hb).
       case_eq ac; intros.
       + subst.
         assert(singleton w) as Hw.
         { apply extsR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extbpR, extsR in Q. easy. }
         assert(singleton (merge_bp_cont p b w')) as Hpw'.
         { apply extbp. easy. }
         specialize(n_b_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' b 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl.
         specialize(inReceive w q Hw Ha); intros.
         destruct H0 as (c1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hw.
         subst.
         intros Hw Hn.
         assert(singleton w1) as Hw1.
         { clear Hn. apply extsR, extcpR, extrR in P. easy. }
         specialize(n_inpN (mk_siso w1 Hw1) (mk_siso (merge_bp_cont p b w') Hpw') q c1 l1 s1); intro HNI.
         apply HNI.
         simpl. easy.
       + subst.
         assert(singleton w) as Hw.
         { apply extsR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extbpR, extsR in Q. easy. }
         assert(singleton (merge_bp_cont p b w')) as Hpw'.
         { apply extbp. easy. }
         specialize(n_b_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' b 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl.
         specialize(inSend w q Hw Ha); intros.
         destruct H0 as (b1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hw.
         subst.
         intros Hw Hn.
         assert(singleton w1) as Hw1.
         { clear Hn. apply extsR, extbpR, extsR in P. easy. }
         specialize(n_outN (mk_siso w1 Hw1) (mk_siso (merge_bp_cont p b w') Hpw') q b1 l1 s1); intro HNI.
         apply HNI.
         simpl. easy.
       destruct a1 as (q,ac).
       destruct H0 as (Ha,Hb).
       case_eq ac; intros.
       + subst.
         assert(singleton w) as Hw.
         { apply extsR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extbpR, extsR in Q. easy. }
         assert(singleton (merge_bp_cont p b w')) as Hpw'.
         { apply extbp. easy. }
         specialize(n_b_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' b 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl.
         specialize(inReceive (merge_bp_cont p b w') q Hpw' Ha); intros.
         destruct H0 as (c1,(l1,(s1,(w1,IHw1)))).
         simpl in Hn.
         generalize dependent Hpw'.
         rewrite IHw1.
         intros Hpw' Hn.
         assert(singleton w1) as Hw1.
         { clear Hn. apply extcpR, extrR in Hpw'. easy. }
         specialize(n_inp_rN (mk_siso w Hw) (mk_siso w1 Hw1) q c1 l1 s1 ); intro HNI.
         apply HNI. easy.
       + subst.
         assert(singleton w) as Hw.
         { apply extsR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extbpR, extsR in Q. easy. }
         assert(singleton (merge_bp_cont p b w')) as Hpw'.
         { apply extbp. easy. }
         specialize(n_b_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' b 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl.
         specialize(inSend (merge_bp_cont p b w') q Hpw' Ha); intros.
         destruct H0 as (b1,(l1,(s1,(w1,IHw1)))).
         simpl in Hn.
         generalize dependent Hpw'.
         rewrite IHw1.
         intros Hpw' Hn.
         assert(singleton w1) as Hw1.
         { clear Hn. apply extbpR, extsR in Hpw'. easy. }
         specialize(n_out_rN (mk_siso w Hw) (mk_siso w1 Hw1) q b1 l1 s1 ); intro HNI.
         apply HNI.
         simpl. easy.
Qed.

Lemma n_a_actN: forall p a l s s' w w' P Q,
  subsort s' s ->
  (act_neq w (merge_ap_cont p a w')) ->
  nRefinementN (mk_siso (p & [(l,s,w)]) P)
               (mk_siso (merge_ap_cont p a (p & [(l,s',w')])) Q).
Proof. intros.
       unfold act_neq in H0.
       destruct H0 as (a1, H0).
       destruct H0 as [H0 | H0].
       destruct a1 as (q,ac).
       destruct H0 as (Ha,Hb).
       case_eq ac; intros.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inReceive w q Hw Ha); intros.
         destruct H0 as (c1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hw.
         subst.
         intros Hw Hn.
         apply n_a_actNH1.
         assert(singleton w1) as Hw1.
         { clear Hn. apply extrR, extcpR, extrR in P. easy. }
         easy. easy. easy.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inSend w q Hw Ha); intros.
         destruct H0 as (b1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hw.
         subst.
         intros Hw Hn.
         apply n_a_actNH2.
         assert(singleton w1) as Hw1.
         {  clear Hn. apply extrR, extbpR, extsR in P. easy. }
         easy. easy. easy.
       destruct a1 as (q,ac).
       destruct H0 as (Ha,Hb).
       case_eq ac; intros.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inReceive (merge_ap_cont p a w') q Hpw' Ha); intros.
         destruct H0 as (c1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hpw'.
         rewrite IHw1.
         intros IHw' Hn.
         specialize (n_a_actNH3 p (ap_end) q c1 l1 s1 w1 w); intros IHn3.
         simpl in IHn3.
         rewrite apend_an in IHn3.
         apply IHn3.
         assert(singleton w1) as Hw1.
         {  clear IHn3 Hn. apply extcpR, extrR in IHw'. easy. }
         easy. easy. easy.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inSend (merge_ap_cont p a w') q Hpw' Ha); intros.
         destruct H0 as (b1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hpw'.
         rewrite IHw1.
         intros IHw' Hn.
         specialize (n_a_actNH4 q b1 p (ap_end) l1 s1 w1 w IHw'); intros IHn3.
         simpl in IHn3.
         rewrite apend_an in IHn3.
         apply IHn3.
         assert(singleton w1) as Hw1.
         {  clear IHn3 Hn. apply extbpR, extsR in IHw'. easy. }
         easy. easy. easy.
Qed.

Lemma nrefNRS: forall w w', (nRefinementN w w' -> False) -> (@und w) ~< (@und w').
Proof. destruct w as (w, Pw).
       destruct w' as (w', Pw').
       intro H.
       generalize dependent w.
       generalize dependent w'.
       simpl. pcofix CIH.
       intros.
       specialize(sinv w Pw); intros Hpw.
       destruct Hpw as [Hpw | Hpw].
       destruct Hpw as (p, (l, (s, (w1, (Heq1, Hs1))))).
       {
         specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         case_eq(eqb p q); intro Heq.
         rewrite eqb_eq in Heq.
         case_eq(eqb l l'); intro Heq2.
         rewrite eqb_eq in Heq2.
         specialize(sort_dec s s'); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         subst.
         pfold.

         specialize(classic(act_eq w1 w2)); intros Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_b (upaco2 refinementR r) w1 w2 q l' s s' (bp_end) 1 Heq3); intros HSR.
         rewrite bpend_ann in HSR.
         rewrite bpend_ann in HSR.
         simpl in HSR.
         apply HSR.

         right.
         specialize (CIH w2 Hs2 w1 Hs1). apply CIH.
         simpl.
         specialize (casen2 q l' s s' ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} Pw Pw'); intros Hp.
         intros Hp2.
         apply Hp. easy. simpl. exact H0.
         exact Hp2. easy.
         subst.

         specialize(n_b_actN q l' s s' w1 w2 (bp_end) Pw ); intros HBN.
         rewrite bpend_an in HBN.
         destruct H0.
         apply HBN. easy. rewrite bpend_an. 
         apply act_eq_neq. intro Ha. apply Hact. easy.
         subst.

         specialize (n_out_sN ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} q l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn. easy.
         subst.
         rewrite eqb_neq in Heq2.
         specialize (n_out_lN ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} q l l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn. easy.
         rewrite eqb_neq in Heq.

         specialize(classic (CoInR (p, snd) (act (q ! [(l', s', w2)])) -> False)); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outN {| und := w1; sprop := Hs1 |} {| und := q ! [(l', s', w2)]; sprop := Pw' |} p (bp_end) l s ); intros HH.
         rewrite bpend_an in HH.
         simpl in HH. apply HH. easy.
         unfold not in Hclass.
         apply NNPP in Hclass.

         specialize(inSend (q ! [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (b,(l1,(s1,(w3,IHw3)))).
         rewrite IHw3.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s s1); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(classic (act_eq w1 ((merge_bp_cont p b w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_b (upaco2 refinementR r) w1 w3 p l1 s s1 b 1 Heq3); intro Hrb.
         simpl in Hrb. 
         apply Hrb.

         assert(singleton w3) as Hs3.
         { revert Pw' H0.
           rewrite IHw3.
           intros Pw'' H0.
           specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw''); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         assert(singleton (merge_bp_cont p b w3)) as Pw''.
         { specialize(@extbp p b w3 Hs3); intros Hss. easy. }
         specialize(CIH (merge_bp_cont p b w3) Pw'' w1 Hs1).
         right.
         apply CIH.
         intro h.
         apply H0.
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.
         specialize(n_b_wN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         apply act_eq_neq in Hact.
         specialize(n_b_actN p l1 s s1 w1 w3 b Pw Pw''); intros HN.
         apply HN. easy. easy.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw''); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_sN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw Pw'' Heq3); intros Hn.
         apply Hn.

         rewrite eqb_neq in Heq2.
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw''); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 b 1 Pw Pw''); intros Hn.
         apply Hn. easy.

         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.

         specialize(classic (CoInR (p, snd) (act (q & [(l', s', w2)])) -> False)); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outN {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p (bp_end) l s ); intros HH.
         rewrite bpend_an in HH.
         simpl in HH. apply HH. easy.

         apply NNPP in Hclass.
         specialize(inSend (q & [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (b,(l1,(s1,(w3,IHw3)))).
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s s1); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(classic (act_eq w1 ((merge_bp_cont p b w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_b (upaco2 refinementR r) w1 w3 p l1 s s1 b 1 Heq3); intro Hrb.
         simpl in Hrb.
         apply Hrb.

         assert(singleton w3) as Hs3.
         { 
            specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss2.
            specialize (@extsR p l1 s1 w3 Hss2); intros Hss3. easy.
         }
         assert(singleton (merge_bp_cont p b w3)) as Pw''.
         { specialize(@extbp p b w3 Hs3); intros Hss. easy. }
         specialize(CIH (merge_bp_cont p b w3) Pw'' w1 Hs1).
         right.
         apply CIH.
         intro h.
         apply H0.

         specialize(n_b_wN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         destruct H0.
         apply act_eq_neq in Hact.
         specialize(n_b_actN p l1 s s1 w1 w3 b Pw Pw'); intros HN.
         apply HN. easy. easy.

         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_sN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw Pw' Heq3); intros Hn.
         apply Hn.

         rewrite eqb_neq in Heq2.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 b 1 Pw Pw'); intros Hn.
         apply Hn. easy.

         subst.
         destruct H0.
         specialize(n_outN {| und := w1; sprop := Hs1 |} {| und := end; sprop := Pw' |} p (bp_end) l s); intro Hn.
         rewrite bpend_an in Hn.
         simpl in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         intro Hf.
         inversion Hf. subst. easy.
         subst. easy.
       }
       destruct Hpw as [Hpw | Hpw].
       destruct Hpw as (p, (l, (s, (w1, (Heq1, Hs1))))).
       { subst.
         specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         specialize(n_i_o_1N {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} p q l l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn.

         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         case_eq(eqb p q); intro Heq.
         rewrite eqb_eq in Heq.
         case_eq(eqb l l'); intro Heq2.
         rewrite eqb_eq in Heq2.
         specialize(sort_dec s' s); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         subst.
         pfold.

         specialize(classic(act_eq w1 w2)); intros Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_a (upaco2 refinementR r) w1 w2 q l' s' s (ap_end) 1 Heq3); intros HSR.
         rewrite apend_ann in HSR.
         rewrite apend_ann in HSR.
         simpl in HSR.
         apply HSR.

         right. 
         apply (CIH w2 Hs2 w1 Hs1).
         intro Hs.
         specialize(casen1 q l' s s' {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} Pw Pw'); intro Hn.
         apply Hn. easy. exact H0. exact Hs.
         subst. easy.

         specialize(n_a_actN q (ap_end) l' s s' w1 w2); intros HNA.
         destruct H0.
         rewrite apend_an in HNA.
         apply HNA.
         easy. rewrite apend_an.
         apply act_eq_neq.
         intro Hb. apply Hact. easy.

         subst.
         destruct H0.
         specialize(n_inp_sN {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} q l' s s' Pw Pw'); intro Hn.
         apply Hn. easy.
         subst.
         rewrite eqb_neq in Heq2.
         destruct H0.
         specialize(n_inp_lN {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} q l l' s s' Pw Pw'); intro Hn.
         apply Hn. easy.

         rewrite eqb_neq in Heq.

         specialize(classic (CoInR (p, rcv) (act (q & [(l', s', w2)])) -> False)); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_inpN {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p (cp_end) l s ); intros HH.
         simpl in HH. rewrite cpend_an in HH. apply HH. easy.

         apply NNPP in Hclass.

         specialize(inReceive (q & [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (c,(l1,(s1,(w3,IHw3)))).
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.

         case_eq(isInCp p c); intros.
         destruct H0.
         assert(singleton w3) as Hs3.
         { apply extcpR, extrR in Pw'.
           easy.
         }
         specialize(n_i_o_2N (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 c Pw Pw'); intros HN2.
         apply HN2. easy.

         specialize(cpap p c (p & [(l1, s1, w3)]) H); intros Hpc.
         destruct Hpc as (a, Hpc).
         generalize dependent Pw'.
         rewrite Hpc.
         intros Pw' H0.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s1 s); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(classic (act_eq w1 ((merge_ap_cont p a w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_a (upaco2 refinementR r) w1 w3 p l1 s1 s a 1 Heq3); intro Hrb.
         simpl in Hrb.
         apply Hrb.

         assert(singleton (merge_ap_cont p a w3)) as Pw''.
         { specialize(@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize(@extrR p l1 s1 w3 Hss); intros Hss2.
           apply extap. easy.
         }
         specialize(CIH (merge_ap_cont p a w3) Pw'' w1 Hs1).
         right.
         apply CIH.
         intro h.
         apply H0.

         assert(singleton w3) as Hs3.
         { specialize(@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize(@extrR p l1 s1 w3 Hss); intros Hss2.
           easy.
         }

         specialize(n_a_wN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 a 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         destruct H0.
         apply act_eq_neq in Hact.
         specialize(n_a_actN p a l1 s s1 w1 w3 Pw Pw'); intros HN.
         apply HN. easy. easy.

         assert(singleton w3) as Hs3.
         { specialize(@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize(@extrR p l1 s1 w3 Hss); intros Hss2.
           easy.
         }

         specialize (n_a_sN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 a 1 Pw Pw' Heq3); intros Hn.
         destruct H0.
         apply Hn.

         rewrite eqb_neq in Heq2.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extrR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_a_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 a 1 Pw Pw'); intros Hn.
         apply Hn. easy.

         subst.
         destruct H0.
         specialize(n_inpN {| und := w1; sprop := Hs1 |} {| und := end; sprop := Pw' |} p (cp_end) l s); intro Hn.
         simpl in Hn. rewrite cpend_an in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         intro Hf. inversion Hf; subst; easy. 
       }
       subst.
       { specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         destruct H0.
         specialize(n_out_rN {| und := end; sprop := Pw |} {| und := w2; sprop := Hs2 |} q (bp_end) l' s'); intro Hn.
         rewrite bpend_an in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         intro Hf. inversion Hf; subst; easy. 
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.

         specialize(n_inp_rN {| und := end; sprop := Pw |} {| und := w2; sprop := Hs2 |} q (cp_end) l' s'); intro Hn.
         destruct H0.
         rewrite cpend_an in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         intro Hf. inversion Hf; subst; easy. 
         subst.
         pfold. constructor.
       }
Qed.

Lemma contrpositive: forall (a b: Prop), (a -> b) <-> ((b -> False) -> (a -> False)).
Proof. split.
       - intros.
         apply H0, H, H1.
       - intros.
         specialize (classic b); intros.
         destruct H1 as [H1 | H1].
         + easy.
         + specialize(H H1 H0). easy.
Qed.

Lemma nrefNR: forall w w', ((@und w) ~< (@und w') -> False) -> nRefinementN w w'.
Proof. intros.
       specialize(nrefNRS w w'); intro HS.
       rewrite contrpositive in HS.
       intros Hb Hc.
       specialize(Hc Hb). easy.
Qed.

Definition subtype (T T': st): Prop :=
  forall U, st2soC T U /\ 
  forall V', st2siC T' V' /\
  exists (W: siso), st2sisoC U  (@und W) /\
  exists (W':siso), st2sisoC V' (@und W') /\ (@und W) ~< (@und W').

Definition nsubtype (T T': st): Prop :=
  exists U,  (st2soC T U -> False) \/
  exists V', (st2siC T' V' -> False) \/
  forall W, (st2sisoC U (@und W) -> False) \/ 
  forall W', (st2sisoC V' (@und W') -> False) \/ nRefinementN W W'.

Lemma subneqL: forall T T', subtype T T' -> nsubtype T T' -> False.
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H0 as (U, H0).
       specialize(H U).
       destruct H0 as [H0 | H0].
       destruct H as (H, Ha).
       easy.
       destruct H as (Ha, H).
       destruct H0 as (V', H0).
       specialize(H V').
       destruct H as (Hb, H).
       destruct H0 as [H0 | H0].
       easy.
       destruct H as (W, H).
       specialize(H0 W).
       destruct H as (Hc, H).
       destruct H0 as [H0 | H0].
       easy.
       destruct H as (W', H).
       destruct H as (Hd, H).
       specialize(H0 W').
       destruct H0 as [H0 | H0].
       easy.
       apply (nrefNL W W'); easy.
Qed.

Lemma subneqR: forall T T', (subtype T T' -> False) -> nsubtype T T'.
Proof. intros.
       unfold subtype, nsubtype in *.
       apply not_all_ex_not in H.
       destruct H as (U, H).
       exists U.
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       apply not_all_ex_not in H.
       destruct H as (V', H).
       right. exists V'. 
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       right. intro W.
       apply not_ex_all_not with (n := W) in H.
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       right. intro W'.
       apply not_ex_all_not with (n := W') in H.
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       right. apply nrefNR. easy.
Qed.

Theorem completeness: forall T T', (subtype T T' -> False) <-> nsubtype T T'.
Proof. split.
       apply (subneqR T T').
       intros. apply (subneqL T T'); easy.
Qed.

(* Print DependGraph completeness. *)

