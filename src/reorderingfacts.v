Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.

Lemma bpend_ann: forall n p w, merge_bp_contn p (bp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(st_eq(merge_bp_cont p bp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma apend_ann: forall n p w, merge_ap_contn p (ap_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(st_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
Qed.

Lemma apend_an: forall p w, merge_ap_cont p (ap_end) w = w.
Proof. intros.
       rewrite(st_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
Qed.

Lemma bpend_an: forall p w, merge_bp_cont p (bp_end) w = w.
Proof. intros.
       rewrite(st_eq(merge_bp_cont p bp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma cpend_ann: forall n p w, merge_cp_contn p (cp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(st_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma cpend_an: forall p w, merge_cp_cont p (cp_end) w = w.
Proof. intros.
       rewrite(st_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma mcomm: forall n p b w,
             merge_bp_contn p b (merge_bp_cont p b w) n =
             merge_bp_cont p b (merge_bp_contn p b w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mcomm2: forall n p a w,
             merge_ap_contn p a (merge_ap_cont p a w) n =
             merge_ap_cont p a (merge_ap_contn p a w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mcomm3: forall n p c w,
             merge_cp_contn p c (merge_cp_cont p c w) n =
             merge_cp_cont p c (merge_cp_contn p c w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mergeSw: forall p a l w,
merge_ap_cont p (listAp p (apList p a ++ l)) w =
merge_ap_cont p a (merge_ap_cont p (listAp p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(st_eq((merge_ap_cont p ap_end w))). simpl.
       destruct w; easy.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p (listAp p (a :: l0)) w))).
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 (listAp p (a :: l0))) w)).
       simpl. easy.
       simpl.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 (listAp p (apList p a ++ l))) w)).
       simpl. rewrite IHa.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (merge_ap_cont p (listAp p l) w))).
       simpl. easy.
       simpl.
       rewrite apend_an.
       easy.
Qed.

Lemma mergeSw2: forall p a l w,
merge_ap_cont p (listApA p (apListA p a ++ l)) w =
merge_ap_cont p a (merge_ap_cont p (listApA p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 ap_end) w)). simpl.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p ap_end w))).
       simpl. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 (listApA p (a :: l0))) w)).
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p (listApA p (a :: l0)) w))).
       simpl. easy.
       rewrite(st_eq(merge_ap_cont p (listApA p (apListA p (ap_merge q n s s0 a) ++ l)) w)).
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (merge_ap_cont p (listApA p l) w))).
       simpl.
       rewrite IHa. easy.
       setoid_rewrite(st_eq(merge_ap_cont p (listApA p (apListA p ap_end ++ l)) w)) at 1.
       rewrite(st_eq(merge_ap_cont p ap_end (merge_ap_cont p (listApA p l) w))).
       simpl. easy.
Qed. 

Lemma mergeSw3: forall p b l w,
merge_bp_cont p (listBp p (bpList p b ++ l)) w =
merge_bp_cont p b (merge_bp_cont p (listBp p l) w).
Proof. intros p b.
       induction b; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 bp_end) w)). simpl.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (merge_bp_cont p bp_end w))).
       simpl. easy.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 (listBp p (b :: l0))) w )).
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (merge_bp_cont p (listBp p (b :: l0)) w))).
       simpl. easy.
       rewrite(st_eq(merge_bp_cont p (listBp p (bpList p (bp_send q n s s0) ++ l)) w)).
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (merge_bp_cont p (listBp p l) w))).
       simpl. easy.
       rewrite(st_eq(merge_bp_cont p (listBp p (bpList p (bp_mergea s s0 s1 b) ++ l)) w)).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_cont p (listBp p l) w))).
       simpl.
       rewrite IHb. easy.
       rewrite(st_eq(merge_bp_cont p (listBp p (bpList p (bp_merge q n s s0 b) ++ l)) w)).
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (merge_bp_cont p (listBp p l) w))).
       simpl. rewrite IHb. easy.
       simpl. rewrite bpend_an. easy.
Qed.

Lemma mergeSw4: forall p a l w,
merge_cp_cont p (listCp p (cpList p a ++ l)) w =
merge_cp_cont p a (merge_cp_cont p (listCp p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 cp_end) w)). simpl.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (merge_cp_cont p cp_end w))).
       simpl. rewrite cpend_an. easy.

       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 (listCp p (c :: l0))) w)).
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (merge_cp_cont p (listCp p (c :: l0)) w))).
       simpl. easy.

       rewrite(st_eq(merge_cp_cont p (listCp p (cpList p (cp_mergea q n s s0 a) ++ l)) w)).
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 a) (merge_cp_cont p (listCp p l) w))).
       simpl. rewrite IHa. easy.

       rewrite(st_eq(merge_cp_cont p (listCp p (cpList p (cp_send s s0 s1) ++ l)) w)).
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (merge_cp_cont p (listCp p l) w))).
       simpl. easy.

       setoid_rewrite(st_eq(merge_cp_cont p (listCp p (cpList p (cp_merge s s0 s1 a) ++ l)) w)) at 1.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 a) (merge_cp_cont p (listCp p l) w))).
       simpl. rewrite IHa. easy.
       simpl.
       rewrite cpend_an.
       easy.
Qed.

Lemma mergeeq: forall n p a w,
  merge_ap_cont p (ApnA p a n) w = merge_ap_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold ApnA. simpl.
       rewrite(st_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold ApnA. simpl.
       rewrite mergeSw. 
       easy.
Qed.

Lemma mergeeq2: forall n p a w,
  merge_ap_cont p (ApnA2 p a n) w = merge_ap_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold ApnA2. simpl.
       rewrite(st_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold ApnA2. simpl.
       rewrite mergeSw2. 
       easy.
Qed.

Lemma mergeeq3: forall n p b w,
  merge_bp_cont p (BpnA p b n) w = merge_bp_contn p b w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold BpnA. simpl.
       rewrite bpend_an. easy.
       simpl.
       rewrite <- IHn.

       unfold BpnA. simpl.
       rewrite mergeSw3. 
       easy.
Qed.

Lemma mergeeq4: forall n p a w,
  merge_cp_cont p (CpnA p a n) w = merge_cp_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold CpnA. simpl.
       rewrite(st_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold CpnA. simpl.
       rewrite mergeSw4. 
       easy.
Qed.

Lemma hm1: forall p b w, act (merge_bp_cont p b w) = appendL (actB p b) (act w).
Proof. intros p b.
       induction b; intros.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_receivea s s0 s1) w))).
       rewrite(coseq_eq( appendL (actB p (bp_receivea s s0 s1)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_send q n s s0) w))).
       unfold coseq_id. simpl.
       rewrite(coseq_eq(appendL [(q, snd)] (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) w) )).
       rewrite(coseq_eq(appendL (actB p (bp_mergea s s0 s1 b)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHb. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_merge q n s s0 b) w))).
       rewrite(coseq_eq(appendL (actB p (bp_merge q n s s0 b)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHb. easy.

       rewrite(st_eq(merge_bp_cont p bp_end w)).
       simpl. rewrite anl2.
       destruct w; easy.
Qed.

Lemma hm1a: forall p a w, act (merge_ap_cont p a w) = appendL (actA p a) (act w).
Proof. intros p a.
       induction a; intros.
       rewrite(coseq_eq(act(merge_ap_cont p (ap_receive q n s s0) w))).
       rewrite(coseq_eq( appendL (actA p (ap_receive q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_ap_cont p (ap_merge q n s s0 a) w))).
       rewrite(coseq_eq(appendL (actA p (ap_merge q n s s0 a)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHa. easy.

       rewrite(st_eq(merge_ap_cont p ap_end w)).
       simpl. rewrite anl2.
       destruct w; easy.
Qed.

Lemma hm1c: forall p c w, act (merge_cp_cont p c w) = appendL (actC p c) (act w).
Proof. intros p c.
       induction c; intros.
       rewrite(coseq_eq(act (merge_cp_cont p (cp_receive q n s s0) w))).
       rewrite(coseq_eq(appendL (actC p (cp_receive q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_cp_cont p (cp_mergea q n s s0 c) w))).
       rewrite(coseq_eq(appendL (actC p (cp_mergea q n s s0 c)) (act w))).
       unfold coseq_id.
       simpl. rewrite IHc. easy.
       
       rewrite(coseq_eq(act (merge_cp_cont p (cp_send s s0 s1) w))).
       rewrite(coseq_eq(appendL (actC p (cp_send s s0 s1)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_cp_cont p (cp_merge s s0 s1 c) w))).
       rewrite(coseq_eq(appendL (actC p (cp_merge s s0 s1 c)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHc. easy.

       rewrite cpend_an. simpl. rewrite anl2.
       easy.
Qed.

Lemma unfcs: forall n p b, (actBn p b n ++ actB p b) = (actBn p b n.+1).
Proof. intro n.
       induction n; intros.
       destruct b; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p b).
       simpl in *.
       destruct b.
       simpl in *. rewrite IHn. easy.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl. easy.
Qed.

Lemma unfcsa: forall n p a, (actAn p a n ++ actA p a) = (actAn p a n.+1).
Proof. intro n.
       induction n; intros.
       destruct a; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p a).
       simpl in *.
       destruct a.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.
       simpl. easy.
Qed.

Lemma unfcsc: forall n p c, (actCn p c n ++ actC p c) = (actCn p c n.+1).
Proof. intro n.
       induction n; intros.
       destruct c; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p c).
       simpl in *.
       destruct c.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       rewrite <- app_comm_cons.
       rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl. easy.
Qed.

Lemma hm2: forall n p, actBn p bp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma hm2a: forall n p, actAn p ap_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma hm2c: forall n p, actCn p cp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma h0: forall (n: nat) p b w, 
act (merge_bp_contn p b w n) = appendL (actBn p b n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p b (merge_bp_contn p b w 1)).
       simpl in IHn.
       rewrite mcomm in IHn.
       rewrite IHn.
       rewrite hm1.
       rewrite stream.app_assoc.
       f_equal.
       destruct b; try easy.
       rewrite unfcs.
       simpl. easy.

       rewrite unfcs.
       simpl. easy.

       rewrite unfcs.
       simpl. easy.

       rewrite unfcs.
       simpl. easy.

       simpl.
       rewrite hm2.
       easy. 
Qed.

Lemma h1: forall (n: nat) p a w, 
act (merge_ap_contn p a w n) = appendL (actAn p a n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p a (merge_ap_contn p a w 1)).
       simpl in IHn.
       rewrite mcomm2 in IHn.
       rewrite IHn.
       rewrite hm1a.
       rewrite stream.app_assoc.
       f_equal.
       destruct a; try easy.
       rewrite unfcsa.
       simpl. easy.

       rewrite unfcsa.
       simpl. easy.

       simpl.
       rewrite hm2a.
       easy. 
Qed.

Lemma hh2: forall n p s s0 s1, actCn p (cp_send s s0 s1) n ++ actC p (cp_send s s0 s1) = ((s, snd) :: actCn p (cp_send s s0 s1) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. f_equal.
       rewrite IHn. easy.
Qed.

Lemma hh3: forall n p c s s0 s1, 
actCn p (cp_merge s s0 s1 c) n ++ ((s, snd) :: actC p c)%SEQ =
((s, snd) :: actC p c)%SEQ ++ actCn p (cp_merge s s0 s1 c) n.
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite app_nil_r. easy.

       simpl. f_equal.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       f_equal.
       rewrite IHn. easy.
Qed.

Lemma h2: forall (n: nat) p c w, 
act (merge_cp_contn p c w n) = appendL (actCn p c n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p c (merge_cp_contn p c w 1)).
       simpl in IHn.
       rewrite mcomm3 in IHn.
       rewrite IHn.
       rewrite hm1c.
       rewrite stream.app_assoc.
       f_equal.
       destruct c; try easy.
       rewrite unfcsc.
       simpl. easy.

       rewrite unfcsc.
       simpl. easy.

       simpl.
       rewrite hh2. easy.

       rewrite hh3. simpl.
       rewrite app_comm_cons.
       easy.

       simpl.
       rewrite hm2c.
       easy. 
Qed.

(* siso facts*)

Lemma extap: forall {p a} w, singleton w -> singleton ((merge_ap_cont p a w)).
Proof. induction a; intros.
       rewrite(st_eq((merge_ap_cont p (ap_receive q n s s0) w))).
       simpl. apply extr. easy.
       rewrite(st_eq((merge_ap_cont p (ap_merge q n s s0 a) w))).
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) w)) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) w)) in H.
       simpl in H.
       apply IHa. apply extrR in H. easy.
       rewrite apend_an in H. easy.
Qed.

Lemma extcpR: forall {p c} w, singleton (merge_cp_cont p c w) -> singleton w.
Proof. intros p c.
       induction c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) w)) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(st_eq((merge_cp_cont p (cp_mergea q n s s0 c) w))) in H.
       simpl in H.
       apply IHc. apply extrR in H. easy.
       rewrite(st_eq((merge_cp_cont p (cp_send s s0 s1) w))) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(st_eq((merge_cp_cont p (cp_merge s s0 s1 c) w))) in H.
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

Lemma extbp: forall {p b} w, singleton w -> singleton ((merge_bp_cont p b w)).
Proof. induction b; intros.
       rewrite(st_eq((merge_bp_cont p (bp_receivea s s0 s1) w))).
       simpl. apply extr. easy.
       rewrite(st_eq((merge_bp_cont p (bp_send q n s s0) w))).
       simpl. pfold. constructor. unfold singleton in H.
       left. easy.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) w)).
       simpl. pfold. constructor. left. 
       unfold singleton in IHb, H.
       apply IHb. easy.
       rewrite(st_eq((merge_bp_cont p (bp_merge q n s s0 b) w))).
       simpl. pfold. constructor.
       unfold singleton in IHb, H. left.
       apply IHb. easy.
       rewrite bpend_an.
       easy.
Qed.

Lemma extbpR: forall {p b} w, singleton ((merge_bp_cont p b w)) -> singleton w.
Proof. intros p b.
       induction b; intros.
       rewrite(st_eq((merge_bp_cont p (bp_receivea s s0 s1) w))) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) w)) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) w)) in H.
       simpl in H. apply extrR in H. apply IHb. easy.
       rewrite(st_eq((merge_bp_cont p (bp_merge q n s s0 b) w))) in H.
       simpl in H.  apply extsR in H. apply IHb. easy.
       rewrite bpend_an in H. easy. 
Qed.

Lemma Ap2CpCont: forall p a w, merge_ap_cont p a w = merge_cp_cont p (Ap2Cp p a) w.
Proof. intros.
       induction a; intros.
       simpl.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) w)).
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) w)). simpl. easy.
       simpl.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) w)).
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 (Ap2Cp p a)) w)). 
       simpl. rewrite IHa. easy.
       simpl.
       rewrite(st_eq(merge_ap_cont p ap_end w)).
       rewrite(st_eq(merge_cp_cont p cp_end w)).
       simpl. easy.
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

(*shapes of terms wrt membership*)

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
       rewrite(st_eq(merge_cp_cont p cp_end (end))). simpl.
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
       rewrite(st_eq( merge_cp_cont p (cp_mergea s Ha4 l1 s1 c1) w2)).
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
       rewrite(st_eq(merge_cp_cont p (cp_merge s l1 s1 c1) w2)).
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
       rewrite(st_eq( merge_cp_cont p (cp_mergea s H4 l1 s1 c) (p & [(l2, s2, w3)]))).
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
       rewrite(st_eq(merge_cp_cont p (cp_merge s l1 s1 c) (p & [(l2, s2, w3)]))).
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
       rewrite(st_eq(merge_bp_cont p (bp_mergea s l1 s1 b) (p ! [(l2, s2, w3)]))).
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
       rewrite(st_eq(merge_bp_cont p (bp_merge s H1 l1 s1 b) (p ! [(l2, s2, w3)]))). simpl. easy.
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
       rewrite(st_eq(merge_ap_cont p (ap_merge s H5 l1 s1 c) (p & [(l2, s2, w3)]))).
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

(* useful lemmata *)

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
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l, s2, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 bp_end) w)).
       simpl.
       rewrite bpend_an. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H.
       rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       inversion H.
       subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n s2 s3) w)).
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)).
       simpl.
       case_eq b; intros.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s4) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n1 s s0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s4 b0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       inversion H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       simpl. subst.
       specialize(IHb1 (bp_end) l s2 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s2 w).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) w)).
       simpl.
       rewrite IHb1. easy. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst. rewrite bpend_an in H. easy.

       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) w)).
       simpl.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(st_eq( merge_bp_cont p (bp_send q0 n0 s2 s3) w)).
       simpl.
       specialize(IHb1 (bp_end) l s1 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s1 w).
       rewrite IHb1. 
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)). simpl.
       easy.
       easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s0 s1) (p ! [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s0 s1 b) (p ! [(l, s, w)]))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq( merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) w)). simpl.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) w)). simpl.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a1; intros.
       subst. rewrite(st_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q n1 s s0 a) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a1) w)).
       simpl.
       rewrite(st_eq( merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       rewrite (IHa1 a l s1 w). easy. easy.
       case_eq a2; intros.
       subst. easy. subst. easy. subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s0 s1 a) (p & [(l, s, w)]))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.
       case_eq a; intros.
       subst.
       inversion H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(st_eq( merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite apend_an in H. inversion H. subst. easy.
       subst. rewrite apend_an in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (ap_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite apend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa a0 l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       destruct a2.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a2) (p & [(l2, s2, w2)]))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s s0 s5) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       
       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(st_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(st_eq( merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.
       inversion H. subst. easy.

       rewrite apend_an in H.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq( merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s3) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [(l2, s2, w2)]))) in H.
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
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s s0 s5) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.

       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(st_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(st_eq( merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       inversion H. subst. easy.

       case_eq a2; intros. subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst. easy.

       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.

       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4.
       subst.
       rewrite cpend_an in H4. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       simpl in H. easy.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 a) (p & [(l1, s2, w1)]))) in H.
       simpl in H.

       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H. subst. rewrite H4.

       specialize (IHa (cp_end) l1 l2 s2 s3 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.

       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa c l1 l2 s2 s3 w1 w2).
       apply IHa. easy.

       subst.
       rewrite cpend_an in H. easy.
       rewrite cpend_an in H.

       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s3) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [(l2, s2, w2)]))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       case_eq c0; intros.
       subst.
       rewrite(st_eq( merge_cp_cont p (cp_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n1 s s0 c) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s4) (p & [(l, s1, w)]))) in H4.
       simpl in H4.
       easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s4 c) (p & [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst. rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.

       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s2 s3 a) w)).
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl.
       subst.
       specialize(IHa (cp_end) l s1 w).
       rewrite IHa. rewrite cpend_an. easy.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s2 s3 a) w)).
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       specialize(IHa c0 l s1 w).
       rewrite IHa. easy. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq( merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.

       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s0 s1 c0) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s0 s1 s2) (p & [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s0 s1 s2 c0) (p & [(l, s, w)]))) in H. 
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
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(st_eq( merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite bpend_an in H4. easy.

       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       simpl in H.
       rewrite(st_eq( merge_bp_cont p (bp_merge q n s4 s5 b) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite bpend_an in H. simpl in H. easy.

       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s5) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq( merge_bp_cont p (bp_send q n1 s s0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s5 b0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4.  inversion H4. easy.
       subst. rewrite bpend_an in H4. easy.

       subst. rewrite bpend_an in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]) )) in H.
       simpl in H. inversion H. subst. easy.

       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l1, s2, w1)]))) in H.
       simpl in H. inversion H.

       case_eq b2; intros.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H.
       rewrite H5.
       specialize(IHb (bp_end) l1 l2 s2 s3 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b0) (p ! [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHb b0 l1 l2 s2 s3 w1 w2).
       apply IHb. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s4 s5 b0) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H. easy.

       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. rewrite H4.
       specialize(IHb (bp_end) l1 l2 s1 s2 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H.
       specialize(IHb b0 l1 l2 s1 s2 w1 w2).
       apply IHb. easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.

       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s3) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s3 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1)
      (merge_ap_contn p (ap_receive q0 n0 s0 s1) (p & [(l, s, w)]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0)
      (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (p & [(l, s, w)]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite apend_ann in H.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1) (merge_ap_contn p (ap_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0) (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (q ! [(l', s', w')]) n))) in H.
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
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q0 n1 s s0 a0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite apend_an in H4. easy.
       subst. rewrite apend_an in H.
       rewrite(st_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]) )) in H.
       simpl in H.
       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(st_eq( merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (ap_end) l l' s1 s' w w').
       apply IHa1.
       rewrite apend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 a l l' s1 s' w w').
       apply IHa1. easy.
       subst. rewrite apend_an in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s0 s1 a) (q ! [(l', s', w')]))) in H.
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
         rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l', s', w')]))) in H0.
         simpl in H0.
         inversion H0. subst. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l', s', w')]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l', s', w')]))) in H0.
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
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s0 s1) (merge_cp_contn p (cp_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s0 s1 c) (merge_cp_contn p (cp_mergea q0 n0 s0 s1 c) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s0 s1 s2) (merge_cp_contn p (cp_send s0 s1 s2) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (merge_cp_contn p (cp_merge s0 s1 s2 c) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy. 
       subst.
       rewrite cpend_ann in H.
       rewrite cpend_an in H. easy.
Qed.


Lemma case12_2c2: forall p c a l1 s1 l2 s2 w1 w2,
isInCp p c = true ->
merge_ap_cont p a (p & [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) -> False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0.
         case_eq a; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H0.
           simpl in H0.
           inversion H0.
           subst.
           apply (IHc (ap_end) l1 s1 l2 s2 w1 w2).
           easy. rewrite apend_an. easy.
        + subst.
          rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l1, s1, w1)]))) in H0.
          simpl in H0.
          inversion H0.
          subst.
          apply (IHc a0 l1 s1 l2 s2 w1 w2).
          easy. easy.
        + subst.
          rewrite(st_eq(merge_ap_cont p ap_end (p & [(l1, s1, w1)]))) in H0.
          simpl in H0.
          inversion H0. subst. easy.
       - case_eq a; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
       - case_eq a; intros.
         + subst.
           rewrite(st_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
       - simpl in *. easy.
Qed.

Lemma case12_2c: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_cp_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n1 s s0 c0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s s0 s4) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s4 c0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.

       subst.
       rewrite cpend_an in H4. easy.

       subst.
       rewrite(st_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]) )) in H.
       simpl in H. easy.

       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (cp_end) l l' s1 s' w w').
       apply IHa1.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq( merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 c l l' s1 s' w w').
       apply IHa1. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.

       subst. rewrite cpend_an in H.
       rewrite(st_eq( merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n s0 s1 c) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s0 s1 s2) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
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
         rewrite(st_eq((merge_ap_cont q (ap_merge q0 n0 s s0 (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0)))) w))) in H.
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

         rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b0) (merge_bp_cont q (listBp q (napp n (bpList q (bp_mergea s s0 s1 b0)))) w))) in H.
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

         rewrite(st_eq(merge_cp_cont q (cp_mergea q0 n0 s s0 c0) (merge_cp_cont q (listCp q (napp n (cpList q (cp_mergea q0 n0 s s0 c0)))) w))) in H.
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

         rewrite(st_eq((merge_ap_cont q (ap_merge q0 n0 s s0 a0) (merge_ap_cont q (listAp q (napp n (apList q (ap_merge q0 n0 s s0 a0)))) w)))) in H.
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

Lemma helperApnew: forall p a q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_ap_cont p a (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p a.
       induction a; intros.
       - rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. rewrite hm1a. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite apend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperCpnew: forall p c q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. rewrite hm1c. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq( merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite cpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperBpnew: forall p b q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [(l1, s1, w1)] = merge_bp_cont p b (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. 
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p & [(l2, s3, w2)]))) in H0.
         simpl in H0.
         inversion H0. rewrite hm1. apply eq0Anew. right.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperBpsnew: forall p b q l1 l2 s1 s2 w1 w2, 
q & [(l1, s1, w1)] = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoInR (p,snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst. 
         rewrite(coseq_eq((act (p ! [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H.
         simpl in H.
         easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1. apply eq0Anew. right.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite bpend_an in H. easy.
Qed.

Lemma helperCp2new: forall p c q l1 l2 s1 s2 w1 w2, 
q ! [(l1, s1, w1)] = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H.
         simpl in H.
         inversion H. subst. 
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1c. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s3, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite cpend_an in H. easy. 
Qed.

Lemma helperBp2new: forall p b q l1 l2 s1 s2 w1 w2, 
q ! [(l1, s1, w1)] = merge_bp_cont p b (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [(l2, s3, w2)]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p & [(l2, s2, w2)]))) in H.
         simpl in H.
         inversion H. subst. 
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 c) (p & [(l2, s3, w2)]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 c) (p & [(l2, s2, w2)]))) in H.
         simpl in H. inversion H. subst.
         rewrite hm1. apply eq0Anew. right.
         rewrite(coseq_eq((act (p & [(l2, s2, w2)])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite bpend_an in H. easy. 
Qed.

Lemma helperApCpnew: forall q a p c l1 l2 s1 s2 w1 w2, 
p <> q ->
merge_ap_cont q a (q & [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq c; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0.
           subst. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_ap_cont q (ap_receive q1 n s3 s4) w1))). simpl.
           apply helperCpnew in H5.
           rewrite(coseq_eq(act (q1 & [(s3, s4, w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act w1)). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           easy. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(st_eq( merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H0. 
           rewrite cpend_an in H0. simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_ap_cont q (ap_receive p n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s2, w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w1)). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           symmetry in H5.
           rewrite(st_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
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
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq((act (q1 & [(s3, s4, merge_ap_cont q a w1)])))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize (IHa p c0 l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H0.
           rewrite cpend_an in H0. simpl in H0. inversion H0. subst. 
           rewrite(st_eq((merge_ap_cont q (ap_merge p n l2 s2 a) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s2, merge_ap_cont q a w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
         + rewrite apend_an.
           rewrite apend_an in H0.
           apply helperCpnew in H0. easy. easy.
Qed.

Lemma helperBpCpnew: forall q b p c l1 l2 s1 s2 w1 w2, 
merge_bp_cont q b (q ! [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) ->
CoInR (p,rcv) (act (merge_bp_cont q b w1)).
Proof. intros q b. 
       induction b; intros.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           apply helperCp2new in H4.
           rewrite(st_eq((merge_bp_cont q (bp_receivea q0 s4 s5) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n. inversion Hb. easy.
           easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [(l1, s2, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_receivea p l2 s3) w1))). simpl.
           rewrite(coseq_eq(act (p & [(l2, s3, w1)]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w1)). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           apply helperCp2new in H4.
           rewrite(st_eq((merge_bp_cont q (bp_send s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys := (act (w1))). simpl. easy. easy.
           easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [(l1, s1, w1)]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           specialize (IHb p (cp_end) l1 l2 s2 s3 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           specialize (IHb p c0 l1 l2 s2 s3 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]) )) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [(l2, s3, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [(l1, s2, w1)]))) in H.
           rewrite cpend_an in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_mergea p l2 s3 b) w1))).
           simpl.
           rewrite(coseq_eq(act (p & [(l2, s3, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           specialize (IHb p (cp_end) l1 l2 s1 s2 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [(l2, s2, w2)]))) in H.
           simpl in H.
           inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [(s4, s5, merge_bp_cont q b w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           specialize (IHb p c0 l1 l2 s1 s2 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [(l1, s1, w1)]))) in H.
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
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0.
         subst. 
         rewrite(coseq_eq(act (p ! [(l2, s2, w2)]))). unfold coseq_id. simpl.
         apply CoInSplit1A with (ys :=(act (w2))). simpl. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H0.
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
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0.
         subst. 
         rewrite(coseq_eq(act (p ! [(l2, s2, w2)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w2))). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l2, s3, w2)]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H0.
         simpl in H0. inversion H0. 
         subst.
         rewrite hm1. apply eq0Anew. right.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w2))). simpl. easy. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma helperApBpnew: forall q a p b l1 l2 s1 s2 w1 w2, 
merge_ap_cont q a (q & [(l1, s1, w1)]) = merge_bp_cont p b (p ! [(l2, s2, w2)]) ->
CoInR (p,snd) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq b; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H.
           subst.
           rewrite(st_eq((merge_ap_cont q (ap_receive s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 & [(s4, s5, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys :=(act w1)). simpl. easy. easy.
           apply helperBpsnew in H4. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [(l1, s1, w1)]))) in H. 
           rewrite bpend_an in H. simpl in H.
           easy.
       - case_eq b; intros.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 & [(s4, s5, merge_ap_cont q a w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           specialize(IHa p (bp_end) l1 l2 s1 s2 w1 w2). 
           apply IHa.
           rewrite bpend_an. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H.
           inversion H. subst.
           specialize(IHa p b0 l1 l2 s1 s2 w1 w2).
           rewrite(st_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))). simpl.
           rewrite(coseq_eq (act (s3 & [(s4, s5, merge_ap_cont q a w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           apply IHa. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [(l1, s1, w1)]))) in H.
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
           rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3 in H5.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) w1)). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (s4, rcv)) (ys := (act (w1))). simpl. easy. easy.
           left. pfold. easy. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. easy.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3 in H5.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n s3 s4) w1)). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (q1, snd)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. pfold. easy. easy.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_send q0 n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1A with (ys := (act (w1))). simpl. easy.
       - case_eq b2; intros.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q (bp_end) l1 l2 s2 s3 w1 w2).
           rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1)). simpl.
           rewrite(coseq_eq (act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           left. pfold.
           apply IHb1. easy.
           rewrite bpend_an. easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q b l1 l2 s2 s3 w1 w2).
           rewrite(st_eq((merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1))). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           left. pfold.
           apply IHb1. easy. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0.
           easy.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. pfold.
           specialize(IHb1 q0 (bp_end) l1 l2 s1 s2 w1 w2).
           apply IHb1. easy.
           rewrite bpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2A with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           left. pfold.
           specialize(IHb1 q0 b l1 l2 s1 s2 w1 w2).
           apply IHb1. easy. easy.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(st_eq( (merge_bp_cont p (bp_merge q0 n l2 s2 b1) w1))). simpl.
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
           rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3new in H5.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) w1)). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act (w1))). simpl. easy. easy.
           easy. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. easy.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           apply bsd3new in H5.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n s3 s4) w1)). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           easy. easy.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_send q0 n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (q0, snd)) (ys := (act (w1))). simpl. easy. easy.
       - case_eq b2; intros.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q (bp_end) l1 l2 s2 s3 w1 w2).
           rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1)). simpl.
           rewrite(coseq_eq (act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           apply IHb1. easy.
           rewrite bpend_an. easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q b l1 l2 s2 s3 w1 w2).
           rewrite(st_eq((merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1))). simpl.
           rewrite(coseq_eq(act (s4 & [(s5, s6, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           apply IHb1. easy. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l1, s2, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0.
           easy.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize(IHb1 q0 (bp_end) l1 l2 s1 s2 w1 w2).
           apply IHb1. easy.
           rewrite bpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [(l2, s2, w2)]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [(s3, s4, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize(IHb1 q0 b l1 l2 s1 s2 w1 w2).
           apply IHb1. easy. easy.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l1, s1, w1)]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(st_eq( (merge_bp_cont p (bp_merge q0 n l2 s2 b1) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [(l2, s2, merge_bp_cont p b1 w1)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (q0, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
       - rewrite bpend_an in H0.
         rewrite bpend_an.
         apply bsd3new in H0. easy. easy.
Qed.



