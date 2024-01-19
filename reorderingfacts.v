From ST Require Import stream st so si reordering siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

Lemma Ap2CpCont: forall p a w, merge_ap_cont p a w = merge_cp_cont p (Ap2Cp p a) w.
Proof. intros.
       induction a; intros.
       simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) w)). simpl. easy.
       simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 (Ap2Cp p a)) w)). 
       simpl. rewrite IHa. easy.
       simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)).
       rewrite(siso_eq(merge_cp_cont p cp_end w)).
       simpl. easy.
Qed.

Lemma bpend_ann: forall n p w, merge_bp_contn p (bp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_bp_cont p bp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma apend_ann: forall n p w, merge_ap_contn p (ap_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
Qed.

Lemma apend_an: forall p w, merge_ap_cont p (ap_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
Qed.

Lemma bpend_an: forall p w, merge_bp_cont p (bp_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_bp_cont p bp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma cpend_ann: forall n p w, merge_cp_contn p (cp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma cpend_an: forall p w, merge_cp_cont p (cp_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma dpend_ann: forall n p w, merge_dp_contn p (dp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_dp_cont p dp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma dpend_an: forall p w, merge_dp_cont p (dp_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_dp_cont p dp_end w)). simpl.
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

Lemma mcomm4: forall n p d w,
             merge_dp_contn p d (merge_dp_cont p d w) n =
             merge_dp_cont p d (merge_dp_contn p d w n).
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
       rewrite(siso_eq((merge_ap_cont p ap_end w))). simpl.
       destruct w; easy.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p (listAp p (a :: l0)) w))).
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 (listAp p (a :: l0))) w)).
       simpl. easy.
       simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 (listAp p (apList p a ++ l))) w)).
       simpl. rewrite IHa.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (merge_ap_cont p (listAp p l) w))).
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
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 ap_end) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p ap_end w))).
       simpl. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 (listApA p (a :: l0))) w)).
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p (listApA p (a :: l0)) w))).
       simpl. easy.
       rewrite(siso_eq(merge_ap_cont p (listApA p (apListA p (ap_merge q n s s0 a) ++ l)) w)).
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (merge_ap_cont p (listApA p l) w))).
       simpl.
       rewrite IHa. easy.
       setoid_rewrite(siso_eq(merge_ap_cont p (listApA p (apListA p ap_end ++ l)) w)) at 1.
       rewrite(siso_eq(merge_ap_cont p ap_end (merge_ap_cont p (listApA p l) w))).
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
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 bp_end) w)). simpl.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (merge_bp_cont p bp_end w))).
       simpl. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 (listBp p (b :: l0))) w )).
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (merge_bp_cont p (listBp p (b :: l0)) w))).
       simpl. easy.
       rewrite(siso_eq(merge_bp_cont p (listBp p (bpList p (bp_send q n s s0) ++ l)) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (merge_bp_cont p (listBp p l) w))).
       simpl. easy.
       rewrite(siso_eq(merge_bp_cont p (listBp p (bpList p (bp_mergea s s0 s1 b) ++ l)) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_cont p (listBp p l) w))).
       simpl.
       rewrite IHb. easy.
       rewrite(siso_eq(merge_bp_cont p (listBp p (bpList p (bp_merge q n s s0 b) ++ l)) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (merge_bp_cont p (listBp p l) w))).
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
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 cp_end) w)). simpl.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (merge_cp_cont p cp_end w))).
       simpl. rewrite cpend_an. easy.

       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 (listCp p (c :: l0))) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (merge_cp_cont p (listCp p (c :: l0)) w))).
       simpl. easy.

       rewrite(siso_eq(merge_cp_cont p (listCp p (cpList p (cp_mergea q n s s0 a) ++ l)) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 a) (merge_cp_cont p (listCp p l) w))).
       simpl. rewrite IHa. easy.

       rewrite(siso_eq(merge_cp_cont p (listCp p (cpList p (cp_send s s0 s1) ++ l)) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (merge_cp_cont p (listCp p l) w))).
       simpl. easy.

       setoid_rewrite(siso_eq(merge_cp_cont p (listCp p (cpList p (cp_merge s s0 s1 a) ++ l)) w)) at 1.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 a) (merge_cp_cont p (listCp p l) w))).
       simpl. rewrite IHa. easy.
       simpl.
       rewrite cpend_an.
       easy.
Qed.

Lemma mergeSw5: forall p a l w,
merge_dp_cont p (listDp p (dpList p a ++ l)) w =
merge_dp_cont p a (merge_dp_cont p (listDp p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q n s s0 dp_end) w)). simpl.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q n s s0) (merge_dp_cont p dp_end w))).
       simpl. rewrite dpend_an. easy.

       rewrite(siso_eq(merge_dp_cont p (dp_mergea q n s s0 (listDp p (d :: l0))) w)).
       rewrite(siso_eq(merge_dp_cont p (dp_receive q n s s0) (merge_dp_cont p (listDp p (d :: l0)) w))).
       simpl. easy.

       rewrite(siso_eq(merge_dp_cont p (listDp p (dpList p (dp_mergea q n s s0 a) ++ l)) w )).
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q n s s0 a) (merge_dp_cont p (listDp p l) w))).
       simpl. rewrite IHa. easy.

       rewrite(siso_eq(merge_dp_cont p (listDp p (dpList p (dp_send q n s s0) ++ l)) w )).
       rewrite(siso_eq(merge_dp_cont p (dp_send q n s s0) (merge_dp_cont p (listDp p l) w))).
       simpl. easy.

       setoid_rewrite(siso_eq(merge_dp_cont p (listDp p (dpList p (dp_merge q n s s0 a) ++ l)) w)) at 1.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q n s s0 a) (merge_dp_cont p (listDp p l) w))).
       simpl. rewrite IHa. easy.
       simpl.
       rewrite dpend_an.
       easy.
Qed.


Lemma mergeeq: forall n p a w,
  merge_ap_cont p (ApnA p a n) w = merge_ap_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold ApnA. simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
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
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
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
       rewrite(siso_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold CpnA. simpl.
       rewrite mergeSw4. 
       easy.
Qed.

Lemma mergeeq5: forall n p a w,
  merge_dp_cont p (DpnA p a n) w = merge_dp_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold DpnA. simpl.
       rewrite(siso_eq(merge_dp_cont p dp_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold DpnA. simpl.
       rewrite mergeSw5. 
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
       rewrite(coseq_eq(appendL [(q, "!"%string)] (act w))).
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

       rewrite(siso_eq(merge_bp_cont p bp_end w)).
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

       rewrite(siso_eq(merge_ap_cont p ap_end w)).
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

Lemma hm1d: forall p c w, act (merge_dp_cont p c w) = appendL (actD p c) (act w).
Proof. intros p c.
       induction c; intros.
       rewrite(coseq_eq(act (merge_dp_cont p (dp_receive q n s s0) w) )).
       rewrite(coseq_eq(appendL (actD p (dp_receive q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_dp_cont p (dp_mergea q n s s0 c) w))).
       rewrite(coseq_eq(appendL (actD p (dp_mergea q n s s0 c)) (act w))).
       unfold coseq_id.
       simpl. rewrite IHc. easy.
       
       rewrite(coseq_eq(act (merge_dp_cont p (dp_send q n s s0) w))).
       rewrite(coseq_eq(appendL (actD p (dp_send q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_dp_cont p (dp_merge q n s s0 c) w))).
       rewrite(coseq_eq(appendL (actD p (dp_merge q n s s0 c)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHc. easy.

       rewrite dpend_an. simpl. rewrite anl2.
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

Lemma unfcsd: forall n p c, (actDn p c n ++ actD p c) = (actDn p c n.+1).
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

Lemma hm2d: forall n p, actDn p dp_end n = [].
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

Lemma hh2: forall n p s s0 s1, actCn p (cp_send s s0 s1) n ++ actC p (cp_send s s0 s1) = ((s, "!"%string) :: actCn p (cp_send s s0 s1) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. f_equal.
       rewrite IHn. easy.
Qed.

Lemma hh2d: forall n p q s s0 n0, actDn p (dp_send q n0 s s0) n ++ [(q, "!"%string)] = ((q, "!"%string) :: actDn p (dp_send q n0 s s0) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. f_equal.
       rewrite IHn. easy.
Qed.

Lemma hh3: forall n p c s s0 s1, 
actCn p (cp_merge s s0 s1 c) n ++ ((s, "!"%string) :: actC p c)%SEQ =
((s, "!"%string) :: actC p c)%SEQ ++ actCn p (cp_merge s s0 s1 c) n.
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

Lemma hh3d: forall n p q c s s0 n0, 
actDn p (dp_merge q n0 s s0 c) n ++ actD p (dp_merge q n0 s s0 c) =
((q, "!"%string) :: actD p c ++ actDn p (dp_merge q n0 s s0 c) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       simpl. f_equal.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       f_equal.
       rewrite IHn. easy.

       rewrite <- app_comm_cons.
       rewrite <- IHn.
       simpl. easy.
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

Lemma h3: forall (n: nat) p c w, 
act (merge_dp_contn p c w n) = appendL (actDn p c n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p c (merge_dp_contn p c w 1)).
       simpl in IHn.
       rewrite mcomm4 in IHn.
       rewrite IHn.
       rewrite hm1d.
       rewrite stream.app_assoc.
       f_equal.
       destruct c; try easy.
       rewrite unfcsd.
       simpl. easy.

       rewrite unfcsd.
       simpl. easy.

       simpl.
       rewrite hh2d. easy.

       rewrite hh3d. simpl.
       rewrite app_comm_cons.
       easy.

       simpl.
       rewrite hm2d.
       easy. 
Qed.

Definition merge_bp_contnA (p: participant) (b: Bp p) (w: st) (n: nat): st :=
merge_bp_cont p (Bpn p b n) w.

Inductive cosetIncL (R: coseq (participant * string) -> list (participant * string) -> Prop):
                        coseq (participant * string) -> list (participant * string) -> Prop :=
  | c_nil : forall ys, cosetIncL R (Delay conil) ys
  | c_incl: forall x xs ys,
            List.In x ys ->
            R xs ys ->
            cosetIncL R (Delay (cocons x xs)) ys.

Definition cosetIncLC := fun s1 s2 => paco2 cosetIncL bot2 s1 s2.

Lemma cosetIncL_mon: monotone2 cosetIncL.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - specialize (c_incl r'); intro HS.
         apply HS.
         apply H.
         apply LE, H0.
Qed.

Inductive cosetIncR: list (participant * string) -> coseq (participant * string) -> Prop :=
  | l_nil : forall ys, cosetIncR nil ys
  | l_incl: forall x xs ys,
            CoInR x ys ->
            cosetIncR xs ys ->
            cosetIncR (x::xs) ys.

Definition act_eq (w w': st) := forall a, CoIn a (act w) <-> CoIn a (act w').
Definition act_eqA (w w': st) := forall a, CoInR a (act w) <-> CoInR a (act w').

Definition act_neq (w w': st) := (exists a, CoIn a (act w) -> CoNInR a (act w')) \/ (exists a, CoIn a (act w') -> CoNInR a (act w)).
