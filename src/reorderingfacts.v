Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local ST.subtyping.refinement.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.
Import CoListNotations.

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

Lemma unfactCp: forall n p c s s0 s1, 
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

Lemma meqAp2: forall n p a w,
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

Lemma meqAp: forall n p a w,
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

Lemma meqBp: forall n p b w,
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

Lemma meqCp: forall n p a w,
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

Lemma actBpL: forall p b w, act (merge_bp_cont p b w) = appendL (actB p b) (act w).
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

Lemma actApL: forall p a w, act (merge_ap_cont p a w) = appendL (actA p a) (act w).
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

Lemma actCpL: forall p c w, act (merge_cp_cont p c w) = appendL (actC p c) (act w).
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

Lemma actBpnil: forall n p, actBn p bp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma actApnil: forall n p, actAn p ap_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma actCpnil: forall n p, actCn p cp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma actBpLcomb: forall (n: nat) p b w, 
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
       rewrite actBpL.
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
       rewrite actBpnil.
       easy. 
Qed.

Lemma actApLcomb: forall (n: nat) p a w, 
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
       rewrite actApL.
       rewrite stream.app_assoc.
       f_equal.
       destruct a; try easy.
       rewrite unfcsa.
       simpl. easy.

       rewrite unfcsa.
       simpl. easy.

       simpl.
       rewrite actApnil.
       easy. 
Qed.

Lemma hactCpLcomb: forall n p s s0 s1, actCn p (cp_send s s0 s1) n ++ actC p (cp_send s s0 s1) = ((s, snd) :: actCn p (cp_send s s0 s1) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. f_equal.
       rewrite IHn. easy.
Qed.

Lemma actCpLcomb: forall (n: nat) p c w, 
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
       rewrite actCpL.
       rewrite stream.app_assoc.
       f_equal.
       destruct c; try easy.
       rewrite unfcsc.
       simpl. easy.

       rewrite unfcsc.
       simpl. easy.

       simpl.
       rewrite hactCpLcomb. easy.

       rewrite unfactCp. simpl.
       rewrite app_comm_cons.
       easy.

       simpl.
       rewrite actCpnil.
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


Lemma extbpns: forall {n p l s b} w, singleton w -> singleton ((merge_bp_contn p b (st_send p (cocons (l,s,w) conil)) n)).
Proof. intros.
       apply extbpn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extbpnr: forall {n p l s b} w, singleton w -> singleton ((merge_bp_contn p b (st_receive p (cocons (l,s,w) conil)) n)).
Proof. intros.
       apply extbpn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapns: forall {n p l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_send p (cocons (l,s,w) conil)) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapnr: forall {n p l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_receive p (cocons (l,s,w) conil)) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapnspq: forall {n p q l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_send q (cocons (l,s,w) conil)) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

(*shapes of terms wrt membership*)

Lemma invsingl: forall p l, singleton (p & l) -> exists (l': label) (s: local.sort) (w: st), l = (cocons ((l',s),w) conil).
Proof. intros.
       pinversion H.
       subst. exists l0. exists s. exists w. easy.
       
(*        induction l; intros.
       unfold singleton in H. punfold H. inversion H. 
       apply sI_mon.
       unfold singleton in H. punfold H. inversion H.
       subst. simpl in *.
       exists l0. exists s. exists w. easy.  *)
       apply sI_mon.
Qed.

Lemma invsingl2: forall p l, singleton (p ! l) -> exists (l': label) (s: local.sort) (w: st), l = (cocons ((l',s),w) conil).
Proof. intros.
       pinversion H. subst.
       subst. exists l0. exists s. exists w. easy.
(*        induction l; intros.
       unfold singleton in H. punfold H. inversion H. 
       apply sI_mon.
       unfold singleton in H. punfold H. inversion H.
       subst. simpl in *.
       exists l0. exists s. exists w. easy.  *)
       apply sI_mon.
Qed.

Lemma sinv: forall w, singleton w ->
                      (exists p l s w', w = st_send p (cocons (l,s,w') conil) /\ singleton w') \/
                      (exists p l s w', w = st_receive p (cocons (l,s,w') conil) /\ singleton w') \/
                      (w = st_end).
Proof. intros.
       case_eq w; intros.
       subst. right. right. (*  left.  *) easy.
       subst. right. left.
       pinversion H.
       subst.
       exists s. exists l. exists s0. exists w. split. easy. easy.
       apply sI_mon.
       subst.
       pinversion H.
       subst. left. 
       exists s. exists l. exists s0. exists w. split. easy. easy.
       apply sI_mon.
(*        
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
       apply sI_mon. *)
Qed.

(* Lemma ninReceive: forall w p (Hs: singleton w) (Hnin: CoNInR (p, rcv) (act w)),
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
 *)

Lemma inReceive: forall w p (Hs: singleton w) (Hin: coseqIn (p, rcv) (act w)),
  exists c l s w2, w = merge_cp_cont p c (p & (cocons (l,s,w2) conil)).
Proof. intros.
       remember (p, rcv) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst.
       rewrite(coseq_eq(act (end))) in Hequ. simpl in Hequ. easy.
       subst.
       specialize(invsingl s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       rewrite(coseq_eq(act (s & cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.
       exists cp_end. exists l1. exists s1. exists w1. 
       rewrite cpend_an. easy.

       subst.
       specialize(invsingl2 s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       inversion Hequ.
       rewrite(coseq_eq(act (s ! cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.

       case_eq w; intros. subst.
       rewrite(coseq_eq(act (end))) in Hequ. simpl in Hequ. easy.
       subst.
       specialize(invsingl s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       subst.
       rewrite(coseq_eq(act (s & cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H w1 H1 H2).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. }
       exists (cp_mergea s H3 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(st_eq( merge_cp_cont p (cp_mergea s H3 l1 s1 c) (p & (cocons (l2, s2, w3) conil)))).
       simpl. easy.

       subst.
       specialize(invsingl2 s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hs.
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       rewrite Heqw1 in Hequ.
       rewrite(coseq_eq(act (s ! cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.
       specialize(IHHin H w1 H1 H2).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       subst.
       exists (cp_merge s l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(st_eq(merge_cp_cont p (cp_merge s l1 s1 c) (p & (cocons (l2, s2, w3) conil)))).
       simpl. easy.
Qed.

Lemma inSend: forall w p (Hs: singleton w) (Hin: coseqIn (p, snd) (act w)),
  exists b l s w2, w = merge_bp_cont p b (p ! (cocons (l,s,w2) conil)).
Proof. intros.
       remember (p, snd) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst.
       rewrite(coseq_eq(act (end))) in Hequ. simpl in Hequ. easy.
       subst.
       specialize(invsingl s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       rewrite(coseq_eq(act (s & cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.
       specialize(invsingl2 s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       rewrite(coseq_eq(act (s ! cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.
       exists (bp_end). (* exists 1. *) exists l1. exists s1. exists w1. simpl.
       rewrite bpend_an. easy.
       rewrite Heqv in H0. rewrite Hequ in H.
       subst. simpl in *.
       case_eq w; intros. subst.
       rewrite(coseq_eq(act (end))) in H. simpl in H. easy.
       subst.
       specialize(invsingl s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst.
       rewrite(coseq_eq(act (s & cocons (l1, s1, w1) conil))) in H. simpl in H.
       inversion H. subst.
       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H1 w1 H2 H3).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_mergea s l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s l1 s1 b) (p ! (cocons (l2, s2, w3) conil)))).
       simpl. easy.
       subst.
       specialize(invsingl2 s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       rewrite(coseq_eq(act (s ! cocons (l1, s1, w1) conil))) in H. simpl in H.
       inversion H. subst.
       assert (p <> s). unfold not in *. intros. apply H0. subst. easy.
       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy. }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H2 w1 H3 H4).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_merge s H1 l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(st_eq(merge_bp_cont p (bp_merge s H1 l1 s1 b) (p ! (cocons (l2, s2, w3) conil)))). simpl. easy.
Qed.

Lemma inReceive_wos: forall w p (Hs: singleton w) (Hin: coseqIn (p, rcv) (act w)),
  (forall q, coseqIn (q, snd) (act w) -> False) ->
  exists a l s w2, w = merge_ap_cont p a (p & (cocons (l,s,w2) conil)).
Proof. intros w p Hs Hin Hout.
       remember (p, rcv) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst.
       rewrite(coseq_eq(act (end))) in Hequ. simpl in Hequ. easy.
       subst.
       specialize(invsingl s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       rewrite(coseq_eq(act (s & cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.
       subst.
       exists ap_end. exists l1. exists s1. exists w1. 
       rewrite apend_an. easy.

       subst.
       specialize(invsingl2 s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       rewrite(coseq_eq(act (s ! cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ.

       case_eq w; intros. subst.
       rewrite(coseq_eq(act (end))) in Hequ. simpl in Hequ. easy.
       subst.
       specialize(invsingl s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hequ.
       subst. 
       rewrite(coseq_eq(act (s & cocons (l1, s1, w1) conil))) in Hequ. simpl in Hequ.
       inversion Hequ. subst.
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       assert((forall q : participant, coseqIn (q, snd) (act w1) -> False)).
       { intros. apply (Hout q). 
         specialize (CoInSplit2 (q, snd) ((cocons (s, rcv) (act w1))) (s, rcv)  ((act w1))); intros.
         apply H4.
         simpl. easy. easy. easy.
       } 
       specialize(IHHin H H3 w1 H1 H2).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. 
       }
       exists (ap_merge s H4 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(st_eq(merge_ap_cont p (ap_merge s H4 l1 s1 c) (p & (cocons (l2, s2, w3) conil)))).
       simpl. easy.

       subst.
       specialize(Hout s).
       specialize(invsingl2 s c Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       subst.
       assert(coseqIn (s, snd) (act (s ! (cocons (l1, s1, w1) conil)))).
       { rewrite(coseq_eq(act (s ! cocons (l1, s1, w1) conil))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (s, snd)) (ys := (act w1)).
         simpl. easy. easy.
       }
       rewrite Hequ in Hout.
       specialize (Hout H). easy.
Qed.

(* useful lemmata *)

Definition eqbp (a b: (participant*string)) :=
  andb (eqb a.1 b.1) (eqb a.2 b.2).

Definition eqbp2 (a b: (participant*dir)) :=
  andb (eqb a.1 b.1) (direqb a.2 b.2).

Lemma eq0: forall l (a: (participant*dir)) xs, List.In a l \/ coseqIn a xs ->
           coseqIn a (appendL l xs).
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
       ((cocons a0 (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       ((cocons a (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       simpl in H2.
       apply dir_eqb_eq in H2.
       inversion H1. inversion H2.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H1.
       rewrite Bool.andb_false_iff in H1.
       destruct H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       ((cocons a (appendL l xs)))
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
       ((cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       apply dir_neqb_neq in H1.
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
       ((cocons a (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       apply dir_eqb_eq in H1.
       inversion H0. inversion H1.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H0.
       rewrite Bool.andb_false_iff in H0.
       destruct H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       ((cocons a (appendL l xs)))
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
       ((cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       apply dir_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       apply IHl. right. easy.
Qed.

Lemma eqscs: forall l (a: (participant*dir)) xs, List.In a l \/ coseqIn a xs ->
            coseqIn a (appendL l xs).
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
       apply dir_eqb_eq in H2.
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
       apply dir_neqb_neq in H1.
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
       apply dir_eqb_eq in H1.
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
       apply dir_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
(*        unfold upaco2. left. pfold. *)
       apply IHl. right. easy.
Qed.

Lemma eqInBp: forall n p b l s w,
coseqIn (p, snd) (act (merge_bp_contn p b (p ! (cocons (l, s, w) conil)) n)).
Proof. intros. rewrite actBpLcomb.
       apply eq0.
       right.
       rewrite(coseq_eq(act (p ! (cocons (l, s, w) conil)))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 (p, snd)
       ((cocons (p, snd) (act w)))
       (p, snd)
       (act w)
       ); intro Ha.
       apply Ha. simpl. easy. easy.
Qed.

Lemma act_rec: forall n p b l s s0 s1 s2 w,
(act (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! (cocons (l, s2, w) conil)) (n.+1)))
=
(cocons (s, rcv) (act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! (cocons (l, s2, w) conil)) n)))).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) (p ! (cocons (l, s2, w) conil))))).
       unfold coseq_id. simpl. easy.
       simpl.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! (cocons (l, s2, w) conil)) n))))).
       unfold coseq_id. simpl.
       simpl in IHn.
       easy.
Qed.

Lemma BpBpeqInv: forall p b1 b2 l s w,
merge_bp_cont p b1 (p ! (cocons (l, s, w) conil)) =
merge_bp_cont p b2 (p ! (cocons (l, s, w) conil)) ->
merge_bp_cont p b1 w =
merge_bp_cont p b2 w.
Proof. intros p b1.
       induction b1; intros.
       case_eq b2; intros. subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! (cocons (l, s2, w) conil)))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! (cocons (l, s2, w) conil)))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! (cocons (l, s2, w) conil)))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H.
       inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! (cocons (l, s2, w) conil)))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! (cocons (l, s2, w) conil)))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! (cocons (l, s2, w) conil)))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! (cocons (l, s2, w) conil)))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 bp_end) w)).
       simpl.
       rewrite bpend_an. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! (cocons (l, s2, w) conil)))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H.
       rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. easy.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! cocons (l, s1, w) conil))) in H.
       simpl in H.
       inversion H.
       subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H.
       easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! (cocons  (l, s1, w) conil)))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n s2 s3) w)).
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)).
       simpl.
       case_eq b; intros.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s4) (p ! (cocons (l, s1, w) conil)))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n1 s s0) (p ! (cocons (l, s1, w) conil)))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s4 b0) (p ! (cocons (l, s1, w) conil)))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! (cocons (l, s1, w) conil)))) in H4.
       simpl in H4. inversion H4. subst. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H.
       inversion H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       simpl. subst.
       specialize(IHb1 (bp_end) l s2 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s2 w).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) w)).
       simpl.
       rewrite IHb1. easy. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! (cocons (l, s2, w) conil)))) in H.
       simpl in H. easy.
       subst. rewrite bpend_an in H. easy.

       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) w)).
       simpl.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H. inversion H. subst.
       rewrite(st_eq( merge_bp_cont p (bp_send q0 n0 s2 s3) w)).
       simpl.
       specialize(IHb1 (bp_end) l s1 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! (cocons (l, s1, w) conil)))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! (cocons (l, s1, w) conil)))) in H.
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
       rewrite(st_eq(merge_bp_cont p (bp_receivea s0 s1 s2) (p ! (cocons (l, s, w) conil)))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s0 s1) (p ! (cocons (l, s, w) conil)))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s0 s1 s2 b) (p ! (cocons (l, s, w) conil)))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s0 s1 b) (p ! (cocons (l, s, w) conil)))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite bpend_an. easy.
Qed.

Lemma lApnil: forall n q,
(listAp q (napp n [])) = ap_end.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. easy.
Qed.

Lemma lBpnil: forall n q,
(listBp q (napp n [])) = bp_end.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. easy.
Qed.

Lemma lCpnil: forall n q,
(listCp q (napp n [])) = cp_end.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. easy.
Qed.

Lemma eqscsrcv: forall l p w,
coseqIn (p, rcv) (appendL l (act w)) ->
In (p, rcv) l \/
coseqIn (p, rcv) (act w).
Proof. intro l.
       induction l; intros.
       - simpl. right. rewrite anl2 in H. easy.
       - inversion H.
         subst. simpl in H0.
         rewrite(coseq_eq(appendL (a :: l) (act w))) in H0.
         simpl in H0.
         inversion H0.
         subst.
         simpl.
         left. left. easy.
         subst. simpl.
         rewrite or_assoc.
         right. apply IHl.
         rewrite(coseq_eq(appendL (a :: l) (act w))) in H0.
         simpl in H0.
         inversion H0.
         subst.
         easy.
Qed.

Lemma eqscssnd: forall l p w,
coseqIn (p, snd) (appendL l (act w)) ->
In (p, snd) l \/
coseqIn (p, snd) (act w).
Proof. intro l.
       induction l; intros.
       - simpl. right. rewrite anl2 in H. easy.
       - inversion H.
         subst. simpl in H0.
         rewrite(coseq_eq(appendL (a :: l) (act w))) in H0.
         simpl in H0.
         inversion H0.
         subst.
         simpl.
         left. left. easy.
         subst. simpl.
         rewrite or_assoc.
         right. apply IHl.
         rewrite(coseq_eq(appendL (a :: l) (act w))) in H0.
         simpl in H0.
         inversion H0.
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

Lemma ApApeqInv2: forall p a1 a2 l s w,
merge_ap_cont p a1 (p & [|(l, s, w)|]) =
merge_ap_cont p a2 (p & [|(l, s, w)|]) ->
merge_ap_cont p a1 w =
merge_ap_cont p a2 w.
Proof. intros p a1.
       induction a1; intros.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [|(l, s1, w)|]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [|(l, s1, w)|]))) in H.
       simpl in H. inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq( merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H. inversion H. subst. easy.
       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) w)). simpl.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) w)). simpl.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a1; intros.
       subst. rewrite(st_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q n1 s s0 a) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [|(l, s1, w)|]))) in H.
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
       rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       inversion H. subst. easy.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l, s, w)|]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s0 s1) (p & [|(l, s, w)|]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l, s, w)|]))) in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s0 s1 a) (p & [|(l, s, w)|]))) in H.
       simpl in H.
       inversion H. subst. easy.
       easy.
Qed.

Lemma ApApeqInv: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [|(l1, s1, w1)|]) =
  merge_ap_cont p a2 (p & [|(l2, s2, w2)|]) -> (p & [|(l1, s1, w1)|]) = (p & [|(l2, s2, w2)|]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H.
       subst.
       case_eq a; intros.
       subst.
       inversion H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [|(l2, s2, w2)|]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(st_eq( merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [|(l2, s2, w2)|]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite apend_an in H. inversion H. subst. easy.
       subst. rewrite apend_an in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (ap_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite apend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa a0 l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       destruct a2.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a2) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       easy.
Qed.

Lemma ApCpeqInv: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [|(l1, s1, w1)|]) =
  merge_cp_cont p a2 (p & [|(l2, s2, w2)|]) -> (p & [|(l1, s1, w1)|]) = (p & [|(l2, s2, w2)|]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [|(l2, s2, w2)|]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [|(l2, s2, w2)|]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s s0 s5) (p & [|(l2, s2, w2)|]))) in H4.
       simpl in H4. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [|(l2, s2, w2)|]))) in H4.
       simpl in H4. easy.
       
       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(st_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(st_eq( merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.
       inversion H. subst. easy.

       rewrite apend_an in H.
       case_eq a2; intros. subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq( merge_cp_cont p (cp_mergea q n s s0 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s3) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       easy.
Qed.

Lemma CpCpeqInv: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_cp_cont p a1 (p & [|(l1, s1, w1)|]) =
  merge_cp_cont p a2 (p & [|(l2, s2, w2)|]) -> (p & [|(l1, s1, w1)|]) = (p & [|(l2, s2, w2)|]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [|(l2, s2, w2)|]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [|(l2, s2, w2)|]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s s0 s5) (p & [|(l2, s2, w2)|]))) in H4.
       simpl in H4. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [|(l2, s2, w2)|]))) in H4.
       simpl in H4. easy.

       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 a) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(st_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(st_eq( merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 a) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 a) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       inversion H. subst. easy.

       case_eq a2; intros. subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l1, s2, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. inversion H.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l1, s2, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l1, s2, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.

       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l1, s2, w1)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. inversion H. subst.

       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c0) (p & [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c0) (p & [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4.
       subst.
       rewrite cpend_an in H4. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l1, s2, w1)|]))) in H.
       simpl in H. easy.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 a) (p & [|(l1, s2, w1)|]))) in H.
       simpl in H.

       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H.
       inversion H. subst. rewrite H4.

       specialize (IHa (cp_end) l1 l2 s2 s3 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.

       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [|(l2, s3, w2)|]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa c l1 l2 s2 s3 w1 w2).
       apply IHa. easy.

       subst.
       rewrite cpend_an in H. easy.
       rewrite cpend_an in H.

       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s3) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
Qed.

Lemma ApApeqInvac: forall p a c l s w,
 merge_ap_cont p a (p & [|(l, s, w)|]) =
 merge_cp_cont p c (p & [|(l, s, w)|]) ->
 merge_ap_cont p a w =
 merge_cp_cont p c w.
Proof. intros p a.
       induction a; intros.
       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [|(l, s1, w)|]))) in H.
       simpl in H. inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       case_eq c0; intros.
       subst.
       rewrite(st_eq( merge_cp_cont p (cp_receive q n1 s s0) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n1 s s0 c) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s s0 s4) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4.
       easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s4 c) (p & [|(l, s1, w)|]))) in H4.
       simpl in H4. easy.
       subst. rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [|(l, s1, w)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [|(l, s1, w)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.

       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [|(l, s1, w)|]))) in H.
       simpl in H. inversion H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s2 s3 a) w)).
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl.
       subst.
       specialize(IHa (cp_end) l s1 w).
       rewrite IHa. rewrite cpend_an. easy.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s2 s3 a) w)).
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       specialize(IHa c0 l s1 w).
       rewrite IHa. easy. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [|(l, s1, w)|]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(st_eq( merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [|(l, s1, w)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l, s1, w)|]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.

       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q n s0 s1) (p & [|(l, s, w)|]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q n s0 s1 c0) (p & [|(l, s, w)|]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s0 s1 s2) (p & [|(l, s, w)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s0 s1 s2 c0) (p & [|(l, s, w)|]))) in H. 
       simpl in H. easy.
       rewrite cpend_an. easy.
Qed.

Lemma BpBpeqInv2: forall p b1 b2 l1 l2 s1 s2 w1 w2,
  merge_bp_cont p b1 (p ! [|(l1, s1, w1)|]) =
  merge_bp_cont p b2 (p ! [|(l2, s2, w2)|]) -> (p ! [|(l1, s1, w1)|]) = (p ! [|(l2, s2, w2)|]).
Proof. intros p b.
       induction b; intros.
       simpl.
       case_eq b2; intros.
       simpl.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(st_eq( merge_bp_cont p (bp_send q n s s0) (p ! [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [|(l2, s3, w2)|]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [|(l2, s3, w2)|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite bpend_an in H4. easy.

       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H.
       simpl in H.
       rewrite(st_eq( merge_bp_cont p (bp_merge q n s4 s5 b) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H.
       rewrite bpend_an in H. simpl in H. easy.

       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H.
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s5) (p ! [|(l2, s2, w2)|]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq( merge_bp_cont p (bp_send q n1 s s0) (p ! [|(l2, s2, w2)|]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s5 b0) (p ! [|(l2, s2, w2)|]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [|(l2, s2, w2)|]))) in H4.
       simpl in H4.  inversion H4. easy.
       subst. rewrite bpend_an in H4. easy.

       subst. rewrite bpend_an in H.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]) )) in H.
       simpl in H. inversion H. subst. easy.

       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [|(l1, s2, w1)|]))) in H.
       simpl in H. inversion H.

       case_eq b2; intros.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H.
       inversion H.
       rewrite H5.
       specialize(IHb (bp_end) l1 l2 s2 s3 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b0) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H.
       inversion H.
       specialize(IHb b0 l1 l2 s2 s3 w1 w2).
       apply IHb. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s4 s5 b0) (p ! [|(l2, s3, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H. easy.

       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [|(l1, s1, w1)|]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. rewrite H4.
       specialize(IHb (bp_end) l1 l2 s1 s2 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b0) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H.
       specialize(IHb b0 l1 l2 s1 s2 w1 w2).
       apply IHb. easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.

       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s3) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s3 b) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [|(l2, s2, w2)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite bpend_an in H. easy.
Qed.

Lemma case11: forall n p q a l l' s s' w w',
merge_ap_contn p a (p & [|(l, s, w)|]) n = q ! [|(l', s', w')|] -> False.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       subst.
       simpl in H.

       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1)
      (merge_ap_contn p (ap_receive q0 n0 s0 s1) (p & [|(l, s, w)|]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0)
      (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (p & [|(l, s, w)|]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite apend_ann in H.
       rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l, s, w)|]))) in H.
       simpl in H. easy.
Qed.

Lemma case12_1: forall n p q a l l' s s' w w',
p & [|(l, s, w)|] = merge_ap_contn p a (q ! [|(l', s', w')|]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1) (merge_ap_contn p (ap_receive q0 n0 s0 s1) (q ! [|(l', s', w')|]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0) (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (q ! [|(l', s', w')|]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite apend_ann in H.
       rewrite apend_an in H. easy.
Qed.

Lemma case12_2: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [|(l, s, w)|]) = merge_ap_cont p a2 (q ! [|(l', s', w')|]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [|(l', s', w')|]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [|(l', s', w')|]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n1 s s0) (q ! [|(l', s', w')|]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q0 n1 s s0 a0) (q ! [|(l', s', w')|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite apend_an in H4. easy.
       subst. rewrite apend_an in H.
       rewrite(st_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H. easy.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [|(l, s1, w)|]) )) in H.
       simpl in H.
       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(st_eq( merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (ap_end) l l' s1 s' w w').
       apply IHa1.
       rewrite apend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 a l l' s1 s' w w').
       apply IHa1. easy.
       subst. rewrite apend_an in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s0 s1) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s0 s1 a) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite apend_an in H. easy.
Qed.

Lemma case12_1c2: forall p c l l' s s' w w',
isInCp p c = true ->
p & [|(l, s, w)|] = merge_cp_cont p c (p & [|(l', s', w')|]) ->  False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [|(l', s', w')|]))) in H0.
         simpl in H0.
         inversion H0. subst. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l', s', w')|]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [|(l', s', w')|]))) in H0.
         simpl in H0. easy.
       - simpl in *. easy.
Qed.

Lemma case12_1c: forall n p q a l l' s s' w w',
p & [|(l, s, w)|] = merge_cp_contn p a (q ! [|(l', s', w')|]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n0 s0 s1) (merge_cp_contn p (cp_receive q0 n0 s0 s1) (q ! [|(l', s', w')|]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n0 s0 s1 c) (merge_cp_contn p (cp_mergea q0 n0 s0 s1 c) (q ! [|(l', s', w')|]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_send s0 s1 s2) (merge_cp_contn p (cp_send s0 s1 s2) (q ! [|(l', s', w')|]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (merge_cp_contn p (cp_merge s0 s1 s2 c) (q ! [|(l', s', w')|]) n))) in H.
       simpl in H. easy. 
       subst.
       rewrite cpend_ann in H.
       rewrite cpend_an in H. easy.
Qed.


Lemma case12_2c2: forall p c a l1 s1 l2 s2 w1 w2,
isInCp p c = true ->
merge_ap_cont p a (p & [|(l1, s1, w1)|]) = merge_cp_cont p c (p & [|(l2, s2, w2)|]) -> False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0.
         case_eq a; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [|(l1, s1, w1)|]))) in H0.
           simpl in H0.
           inversion H0.
           subst.
           apply (IHc (ap_end) l1 s1 l2 s2 w1 w2).
           easy. rewrite apend_an. easy.
        + subst.
          rewrite(st_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [|(l1, s1, w1)|]))) in H0.
          simpl in H0.
          inversion H0.
          subst.
          apply (IHc a0 l1 s1 l2 s2 w1 w2).
          easy. easy.
        + subst.
          rewrite(st_eq(merge_ap_cont p ap_end (p & [|(l1, s1, w1)|]))) in H0.
          simpl in H0.
          inversion H0. subst. easy.
       - case_eq a; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
       - case_eq a; intros.
         + subst.
           rewrite(st_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
       - simpl in *. easy.
Qed.

Lemma case12_2c: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [|(l, s, w)|]) = merge_cp_cont p a2 (q ! [|(l', s', w')|]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [|(l', s', w')|]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       simpl in H.
       rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [|(l', s', w')|]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq c; intros.
       subst.
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n1 s s0) (q ! [|(l', s', w')|]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n1 s s0 c0) (q ! [|(l', s', w')|]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s s0 s4) (q ! [|(l', s', w')|]))) in H4.
       simpl in H4. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s4 c0) (q ! [|(l', s', w')|]))) in H4.
       simpl in H4. easy.

       subst.
       rewrite cpend_an in H4. easy.

       subst.
       rewrite(st_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [|(l', s', w')|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [|(l', s', w')|]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [|(l, s1, w)|]) )) in H.
       simpl in H. easy.

       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (cp_end) l l' s1 s' w w').
       apply IHa1.
       rewrite cpend_an. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq( merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 c l l' s1 s' w w').
       apply IHa1. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [|(l', s', w')|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       rewrite(st_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [|(l', s', w')|]))) in H.
       simpl in H. easy.

       subst. rewrite cpend_an in H.
       rewrite(st_eq( merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [|(l, s1, w)|]))) in H.
       simpl in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(st_eq(merge_cp_cont p (cp_receive q0 n s0 s1) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n s0 s1 c) (q ! [|(l', s', w')|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_send s0 s1 s2) (q ! [|(l', s', w')|]))) in H.
       simpl in H. easy.
       subst. rewrite(st_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (q ! [|(l', s', w')|]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
Qed.

Lemma insndAp: forall n p q a w,
coseqIn (p, snd) (act (merge_ap_cont q (ApnA q a n) w)) ->
coseqIn (p, snd) (act w).
Proof. intro n.
       induction n; intros.
       - unfold ApnA in H. simpl in H.
         rewrite apend_an in H. easy.
       - unfold ApnA in H. simpl in H.
         simpl.
         case_eq a; intros.
         subst.
         rewrite mergeSw in H.
         rewrite(coseq_eq((act (merge_ap_cont q (ap_receive q0 n0 s s0) (merge_ap_cont q (listAp q (napp n (apList q (ap_receive q0 n0 s s0)))) w))))) in H. simpl in H.
         inversion H.
         subst.
         simpl in H0.
         rewrite(coseq_eq((act (merge_ap_cont q (listAp q (napp n [ap_receive q0 n0 s s0])) w)))) in H0. simpl in H0.
         inversion H0. subst. 
         inversion H0. subst.
         simpl in H0.
         specialize(IHn p q (ap_receive q0 n0 s s0) w).
         apply IHn. unfold ApnA. simpl. easy.

         subst.
         simpl in H.
         rewrite(st_eq((merge_ap_cont q (ap_merge q0 n0 s s0 (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0)))) w))) in H.
         simpl in H.
         rewrite(coseq_eq(act (q0 & [|(s, s0, merge_ap_cont q (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w)|]))) in H.
         unfold coseq_id in H. simpl in H.
         rewrite(coseq_eq((cocons (q0, rcv) (act (merge_ap_cont q (listAp q (apList q a0 ++ napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w))))) in H. simpl in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst.
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
         rewrite actApL in H5.
         apply eqscssnd in H5.
         destruct H5.
         apply notinA in H5. easy.
         easy.

         subst. simpl in *.
         rewrite lApnil in H.
         rewrite apend_an in H. easy.
Qed.

Lemma inrcvBp: forall n p q b w,
         coseqIn (p, rcv) (act (merge_bp_cont q (BpnA q b n) w))
         ->
         In (p, rcv) (actBn q b n) \/
         coseqIn (p, rcv) (act w).
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
         rewrite(coseq_eq(act (merge_bp_cont q (bp_receivea s s0 s1) (merge_bp_cont q (listBp q (napp n [bp_receivea s s0 s1])) w)))) in H0. simpl in H0.
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         rewrite(coseq_eq(act (merge_bp_cont q (bp_receivea s s0 s1) (merge_bp_cont q (listBp q (napp n [bp_receivea s s0 s1])) w)))) in H0. simpl in H0.
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
         rewrite(coseq_eq(act (merge_bp_cont q (bp_send q0 n0 s s0) (merge_bp_cont q (listBp q (napp n [bp_send q0 n0 s s0])) w)))) in H1. simpl in H1.
         inversion H1. subst.
         rewrite or_assoc.
         right.
         apply IHn.
         simpl in H1.
         rewrite(coseq_eq(act (merge_bp_cont q (bp_send q0 n0 s s0) (merge_bp_cont q (listBp q (napp n [bp_send q0 n0 s s0])) w)))) in H1. simpl in H1.
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
         rewrite(coseq_eq(act (merge_bp_cont q (bp_mergea s s0 s1 b0) (merge_bp_cont q (listBp q (napp n (bp_receivea s s0 s1 :: bpList q b0))) w)))) in H0. simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         rewrite(coseq_eq(act (merge_bp_cont q (bp_mergea s s0 s1 b0) (merge_bp_cont q (listBp q (napp n (bp_receivea s s0 s1 :: bpList q b0))) w)))) in H0. simpl in H0.
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
         rewrite(coseq_eq(act (s & [|(s0, s1, merge_bp_cont q b0 (merge_bp_cont q (listBp q (napp n (bp_receivea s s0 s1 :: bpList q b0))) w))|]))) in H3. simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         rewrite(coseq_eq(act (s & [|(s0, s1, merge_bp_cont q b0 (merge_bp_cont q (listBp q (napp n (bp_receivea s s0 s1 :: bpList q b0))) w))|]))) in H3. simpl in H3.
         inversion H3.
         subst.

         unfold BpnA.
         rewrite actBpL in H5.

         apply eqscsrcv in H5.
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
         rewrite actBpL in H.

         apply eqscsrcv in H.
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
         rewrite lBpnil in H.
         rewrite bpend_an in H.
         right. easy.
Qed.

Lemma inrcvCp: forall n p q c w,
         coseqIn (p, rcv) (act (merge_cp_cont q (CpnA q c n) w))
         ->
         In (p, rcv) (actCn q c n) \/
         coseqIn (p, rcv) (act w).
Proof. intro n.
       induction n; intros.
       - unfold CpnA in H. simpl in H.
         rewrite cpend_an in H. right. easy.
       - unfold CpnA in H. simpl in H.
         simpl.
         case_eq c; intros.
         subst.
         rewrite mergeSw4 in H.
         rewrite(coseq_eq((act (merge_cp_cont q (cp_receive q0 n0 s s0) (merge_cp_cont q (listCp q (napp n (cpList q (cp_receive q0 n0 s s0)))) w))))) in H. simpl in H.
         inversion H.
         subst.
         simpl in H0.
         inversion H0. subst. simpl. left. left. 
         
         easy.
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
         rewrite(coseq_eq(act (merge_cp_cont q (cp_mergea q0 n0 s s0 c0) (merge_cp_cont q (listCp q (napp n (cp_receive q0 n0 s s0 :: cpList q c0))) w)))) in H0. simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         rewrite(coseq_eq(act (merge_cp_cont q (cp_mergea q0 n0 s s0 c0) (merge_cp_cont q (listCp q (napp n (cp_receive q0 n0 s s0 :: cpList q c0))) w)))) in H0. simpl in H0.
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
         rewrite(coseq_eq(act (q0 & [|(s, s0, merge_cp_cont q c0 (merge_cp_cont q (listCp q (napp n (cp_receive q0 n0 s s0 :: cpList q c0))) w))|]))) in H3. simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         rewrite(coseq_eq(act (q0 & [|(s, s0, merge_cp_cont q c0 (merge_cp_cont q (listCp q (napp n (cp_receive q0 n0 s s0 :: cpList q c0))) w))|]))) in H3. simpl in H3.
         inversion H3.
         subst.

         unfold CpnA.
         rewrite actCpL in H5.

         apply eqscsrcv in H5.
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
         rewrite(coseq_eq(act (merge_cp_cont q (cp_send s s0 s1) (merge_cp_cont q (listCp q (napp n [cp_send s s0 s1])) w)))) in H1. simpl in H1.
         inversion H1. subst.
         rewrite or_assoc.
         right.
         apply IHn.
         simpl in H1.
         rewrite(coseq_eq(act (merge_cp_cont q (cp_send s s0 s1) (merge_cp_cont q (listCp q (napp n [cp_send s s0 s1])) w)))) in H1. simpl in H1.
         inversion H1.
         subst.
         unfold CpnA. easy.
         (**)

         (*merge*)
         subst.
         rewrite mergeSw4 in H.
         unfold CpnA.
         rewrite actCpL in H.

         apply eqscsrcv in H.
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
         rewrite lCpnil in H.
         rewrite cpend_an in H.
         right. easy.
Qed.

Lemma inrcvAp: forall n p q a w,
         coseqIn (p, rcv) (act (merge_ap_cont q (ApnA q a n) w))
         ->
         In (p, rcv) (actAn q a n) \/
         coseqIn (p, rcv) (act w).
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
         rewrite(coseq_eq(act (merge_ap_cont q (ap_receive q0 n0 s s0) (merge_ap_cont q (listAp q (napp n [ap_receive q0 n0 s s0])) w)))) in H0. simpl in H0. 
         inversion H0. subst. simpl. left. left. easy.
         subst.
         simpl in H0.
         rewrite(coseq_eq(act (merge_ap_cont q (ap_receive q0 n0 s s0) (merge_ap_cont q (listAp q (napp n [ap_receive q0 n0 s s0])) w)))) in H0. simpl in H0.
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
         rewrite(coseq_eq(act (merge_ap_cont q (ap_merge q0 n0 s s0 a0) (merge_ap_cont q (listAp q (napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w)))) in H0. simpl in H0.
         inversion H0.
         subst. left. left. easy.
         subst.
         simpl in H0.
         rewrite(coseq_eq(act (merge_ap_cont q (ap_merge q0 n0 s s0 a0) (merge_ap_cont q (listAp q (napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w)))) in H0. simpl in H0.
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
         rewrite(coseq_eq(act (q0 & [|(s, s0, merge_ap_cont q a0 (merge_ap_cont q (listAp q (napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w))|]))) in H3. simpl in H3.
         inversion H3.
         subst. easy.
         subst.
         simpl in H3.
         rewrite(coseq_eq(act (q0 & [|(s, s0, merge_ap_cont q a0 (merge_ap_cont q (listAp q (napp n (ap_merge q0 n0 s s0 ap_end :: apList q a0))) w))|]))) in H3. simpl in H3.
         inversion H3.
         subst.

         unfold ApnA.
         rewrite actApL in H5.
         apply eqscsrcv in H5.
         destruct H5.
         left. easy.
         right.
         apply IHn.
         unfold ApnA.
         easy.

         subst. simpl in *.
         rewrite lApnil in H.
         rewrite apend_an in H.
         right. easy.
Qed.

Lemma nApeqrcv: forall p a q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [|(l1, s1, w1)|] = merge_ap_cont p a (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act w1).
Proof. intros p a.
       induction a; intros.
       - rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [|(l2, s2, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0. rewrite actApL. apply eqscs. right.
         rewrite(coseq_eq((act (p & [|(l2, s2, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite apend_an in H0. inversion H0. subst. easy.
Qed.

Lemma nCpeqrcv: forall p c q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [|(l1, s1, w1)|] = merge_cp_cont p c (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [|(l2, s2, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0. rewrite actCpL. apply eqscs. right.
         rewrite(coseq_eq((act (p & [|(l2, s2, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq( merge_cp_cont p (cp_send s s0 s1) (p & [|(l2, s3, w2)|]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [|(l2, s3, w2)|]))) in H0.
         simpl in H0. easy.
       - rewrite cpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma nBpeqrcv: forall p b q l1 l2 s1 s2 w1 w2, 
p <> q ->
q & [|(l1, s1, w1)|] = merge_bp_cont p b (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [|(l2, s3, w2)|]))) in H0.
         simpl in H0. inversion H0. subst. 
         rewrite(coseq_eq((act (p & [|(l2, s3, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0. 
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p & [|(l2, s3, w2)|]))) in H0.
         simpl in H0.
         inversion H0. rewrite actBpL. apply eqscs. right.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl.
         rewrite(coseq_eq(act (p & [|(l2, s3, w2)|]))). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p & [|(l2, s2, w2)|]))) in H0.
         simpl in H0. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma nBpeqsnd: forall p b q l1 l2 s1 s2 w1 w2, 
q & [|(l1, s1, w1)|] = merge_bp_cont p b (p ! [|(l2, s2, w2)|]) ->
coseqIn (p,snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l2, s3, w2)|]))) in H.
         simpl in H. inversion H. subst. 
         rewrite(coseq_eq((act (p ! [|(l2, s3, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l2, s2, w2)|]))) in H.
         simpl in H.
         easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [|(l2, s3, w2)|]))) in H.
         simpl in H. inversion H. subst.
         rewrite actBpL. apply eqscs. right.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w2)). simpl. 
         rewrite(coseq_eq(act (p ! [|(l2, s3, w2)|]))). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [|(l2, s2, w2)|]))) in H.
         simpl in H. easy.
       - rewrite bpend_an in H. easy.
Qed.

Lemma Cpeqrcv: forall p c q l1 l2 s1 s2 w1 w2, 
q ! [|(l1, s1, w1)|] = merge_cp_cont p c (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) (p & [|(l2, s2, w2)|]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [|(l2, s2, w2)|]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_send s s0 s1) (p & [|(l2, s3, w2)|]))) in H.
         simpl in H.
         inversion H. subst. 
         rewrite(coseq_eq((act (p & [|(l2, s3, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [|(l2, s3, w2)|]))) in H.
         simpl in H. inversion H. subst.
         rewrite actCpL. apply eqscs. right.
         rewrite(coseq_eq((act (p & [|(l2, s3, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite cpend_an in H. easy. 
Qed.

(*here*)
Lemma Bpeqrcv: forall p b q l1 l2 s1 s2 w1 w2, 
q ! [|(l1, s1, w1)|] = merge_bp_cont p b (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act w1).
Proof. intros p c.
       induction c; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p & [|(l2, s3, w2)|]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p & [|(l2, s2, w2)|]))) in H.
         simpl in H.
         inversion H. subst. 
         rewrite(coseq_eq((act (p & [|(l2, s2, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 c) (p & [|(l2, s3, w2)|]))) in H.
         simpl in H. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 c) (p & [|(l2, s2, w2)|]))) in H.
         simpl in H. inversion H. subst.
         rewrite actBpL. apply eqscs. right.
         rewrite(coseq_eq((act (p & [|(l2, s2, w2)|])))).
         unfold coseq_id.
         simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w2)). simpl. easy. easy.
       - rewrite bpend_an in H. easy. 
Qed.

Lemma nApCpeqrcv: forall q a p c l1 l2 s1 s2 w1 w2, 
p <> q ->
merge_ap_cont q a (q & [|(l1, s1, w1)|]) = merge_cp_cont p c (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq c; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0. inversion H0.
           subst. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_ap_cont q (ap_receive q1 n s3 s4) w1))). simpl.
           apply nCpeqrcv in H5.
           rewrite(coseq_eq(act (q1 & [|(s3, s4, w1)|]))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act w1)). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           easy. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(st_eq( merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H0. 
           rewrite cpend_an in H0. simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_ap_cont q (ap_receive p n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (p & [|(l2, s2, w1)|]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w1)). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0.
           inversion H0. subst.
           symmetry in H5.
           rewrite(st_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq(act (q1 & [|(s3, s4, merge_ap_cont q a w1)|]))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. 
           intro Hb. apply n0. inversion Hb. easy.
           apply nApeqrcv in H5.
           inversion H0. subst.
           specialize (IHa p (cp_end) l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           rewrite cpend_an. easy.
           easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_ap_cont q (ap_merge q1 n s3 s4 a) w1))).
           simpl.
           rewrite(coseq_eq((act (q1 & [|(s3, s4, merge_ap_cont q a w1)|])))).
           unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize (IHa p c0 l1 l2 s1 s2 w1 w2 H).
           apply IHa.
           easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [|(l2, s2, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H0.
           rewrite cpend_an in H0. simpl in H0. inversion H0. subst. 
           rewrite(st_eq((merge_ap_cont q (ap_merge p n l2 s2 a) w1))). simpl.
           rewrite(coseq_eq(act (p & [|(l2, s2, merge_ap_cont q a w1)|]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
         + rewrite apend_an.
           rewrite apend_an in H0.
           apply nCpeqrcv in H0. easy. easy.
Qed.

Lemma eqBpCprcv: forall q b p c l1 l2 s1 s2 w1 w2, 
merge_bp_cont q b (q ! [|(l1, s1, w1)|]) = merge_cp_cont p c (p & [|(l2, s2, w2)|]) ->
coseqIn (p,rcv) (act (merge_bp_cont q b w1)).
Proof. intros q b. 
       induction b; intros.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. inversion H. subst.
           apply Cpeqrcv in H4.
           rewrite(st_eq((merge_bp_cont q (bp_receivea q0 s4 s5) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [|(s4, s5, w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n. inversion Hb. easy.
           easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s s0 s1) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite cpend_an in H. simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_receivea p l2 s3) w1))). simpl.
           rewrite(coseq_eq(act (p & [|(l2, s3, w1)|]))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w1)). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. inversion H. subst.
           apply Cpeqrcv in H4.
           rewrite(st_eq((merge_bp_cont q (bp_send s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [|(s4, s5, w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys := (act (w1))). simpl. easy. easy.
           easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s s0) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q0 n s4 s5) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (q0 & [|(s4, s5, merge_bp_cont q b w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           specialize (IHb p (cp_end) l1 l2 s2 s3 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q0 n s4 s5 c0) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_mergea q0 s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (q0 & [|(s4, s5, merge_bp_cont q b w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb. easy.
           specialize (IHb p c0 l1 l2 s2 s3 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [|(l1, s2, w1)|]) )) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s4 s5 s6 c0) (p & [|(l2, s3, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s s0 s1 b) (q ! [|(l1, s2, w1)|]))) in H.
           rewrite cpend_an in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_mergea p l2 s3 b) w1))).
           simpl.
           rewrite(coseq_eq(act (p & [|(l2, s3, merge_bp_cont q b w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act (merge_bp_cont q b w1))). simpl. easy. easy.
       - case_eq c; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_receive q1 n0 s3 s4) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_mergea q1 n0 s3 s4 c0) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 ! [|(s4, s5, merge_bp_cont q b w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           specialize (IHb p (cp_end) l1 l2 s1 s2 w1 w2).
           apply IHb.
           rewrite cpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_cp_cont p (cp_merge s3 s4 s5 c0) (p & [|(l2, s2, w2)|]))) in H.
           simpl in H.
           inversion H. subst.
           rewrite(st_eq((merge_bp_cont q (bp_merge s3 n s4 s5 b) w1))). simpl.
           rewrite(coseq_eq(act (s3 ! [|(s4, s5, merge_bp_cont q b w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, snd)) (ys :=(act (merge_bp_cont q b w1))). simpl. easy. 
           intro Hb. apply n. inversion Hb.
           specialize (IHb p c0 l1 l2 s1 s2 w1 w2).
           apply IHb. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s s0 b) (q ! [|(l1, s1, w1)|]))) in H.
           rewrite cpend_an in H. simpl in H. easy.
       - rewrite bpend_an in H.
         rewrite bpend_an.
         apply Cpeqrcv in H. easy.
Qed.

Lemma insndBp: forall p b q l1 l2 s1 s2 w1 w2,
p <> q ->
q ! [|(l1, s1, w1)|] = merge_bp_cont p b (p ! [|(l2, s2, w2)|]) ->
coseqIn (p, snd) (act w1).
Proof. intros p b.
       induction b; intros.
       - rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l2, s3, w2)|]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0.
         subst. 
         rewrite(coseq_eq(act (p ! [|(l2, s2, w2)|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w2))). simpl. easy. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [|(l2, s3, w2)|]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [|(l2, s2, w2)|]))) in H0.
         simpl in H0. inversion H0. 
         subst.
         rewrite actBpL. apply eqscs. right.
         apply CoInSplit1 with (y := (p, snd)) (ys :=(act (w2))). simpl.
         rewrite(coseq_eq(act (p ! [|(l2, s2, w2)|]))). simpl. easy. easy.
       - rewrite bpend_an in H0. inversion H0. subst. easy.
Qed.

Lemma eqApBpsnd: forall q a p b l1 l2 s1 s2 w1 w2, 
merge_ap_cont q a (q & [|(l1, s1, w1)|]) = merge_bp_cont p b (p ! [|(l2, s2, w2)|]) ->
coseqIn (p,snd) (act (merge_ap_cont q a w1)).
Proof. intros q a.
       induction a; intros.
       - case_eq b; intros.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. inversion H.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst. 
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. inversion H.
           subst.
           rewrite(st_eq((merge_ap_cont q (ap_receive s3 n s4 s5) w1))). simpl.
           rewrite(coseq_eq(act (s3 & [|(s4, s5, w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys :=(act w1)). simpl. easy. easy.
           apply nBpeqsnd in H4. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_receive q0 n s s0) (q & [|(l1, s1, w1)|]))) in H. 
           rewrite bpend_an in H. simpl in H.
           easy.
       - case_eq b; intros.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. inversion H. subst.
           rewrite(st_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))).
           simpl.
           rewrite(coseq_eq(act (s3 & [|(s4, s5, merge_ap_cont q a w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           specialize(IHa p (bp_end) l1 l2 s1 s2 w1 w2). 
           apply IHa.
           rewrite bpend_an. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n0 s3 s4) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H.
           inversion H. subst.
           specialize(IHa p b0 l1 l2 s1 s2 w1 w2).
           rewrite(st_eq((merge_ap_cont q (ap_merge s3 n s4 s5 a) w1))). simpl.
           rewrite(coseq_eq (act (s3 & [|(s4, s5, merge_ap_cont q a w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s3, rcv)) (ys := (act (merge_ap_cont q a w1))). simpl. easy. easy.
           apply IHa. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H.
           rewrite(st_eq(merge_bp_cont p (bp_merge q1 n0 s3 s4 b0) (p ! [|(l2, s2, w2)|]))) in H.
           simpl in H. easy.
         + subst.
           rewrite(st_eq(merge_ap_cont q (ap_merge q0 n s s0 a) (q & [|(l1, s1, w1)|]))) in H.
           rewrite bpend_an in H. simpl in H. easy.
       - subst.
         rewrite apend_an in H.
         rewrite apend_an.
         apply nBpeqsnd in H. easy.
Qed.

Lemma nBpBpeqsnd: forall p b1 q b2 l1 l2 s1 s2 w1 w2,
p <> q ->
merge_bp_cont p b1 (p ! [|(l1, s1, w1)|]) = merge_bp_cont q b2 (q ! [|(l2, s2, w2)|]) ->
coseqIn (q, snd) (act (merge_bp_cont p b1 w1)).
Proof. intros p b1.
       induction b1; intros.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0.
           inversion H0. subst. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. inversion H0. subst.
           apply insndBp in H5.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s4 s5 s6) w1)). simpl.
           rewrite(coseq_eq(act (s4 & [|(s5, s6, w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act (w1))). simpl. easy. easy.
           easy. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite bpend_an in H0. simpl in H0. easy.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0. inversion H0. subst. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0. inversion H0. subst.
           apply insndBp in H5.
           rewrite(st_eq(merge_bp_cont p (bp_send q1 n s3 s4) w1)). simpl.
           rewrite(coseq_eq(act (q1 ! [|(s3, s4, w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act (w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           easy. easy.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_send q0 n l2 s2) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [|(l2, s2, w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (q0, snd)) (ys := (act (w1))). simpl. easy. easy.
       - case_eq b2; intros.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_receivea s4 s5 s6) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q (bp_end) l1 l2 s2 s3 w1 w2).
           rewrite(st_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1)). simpl.
           rewrite(coseq_eq (act (s4 & [|(s5, s6, merge_bp_cont p b1 w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           apply IHb1. easy.
           rewrite bpend_an. easy. 
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_send q0 n s4 s5) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_mergea s4 s5 s6 b) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. inversion H0. subst.
           specialize(IHb1 q b l1 l2 s2 s3 w1 w2).
           rewrite(st_eq((merge_bp_cont p (bp_mergea s4 s5 s6 b1) w1))). simpl.
           rewrite(coseq_eq(act (s4 & [|(s5, s6, merge_bp_cont p b1 w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s4, rcv)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
           apply IHb1. easy. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q (bp_merge q0 n s4 s5 b) (q ! [|(l2, s3, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [|(l1, s2, w1)|]))) in H0.
           rewrite bpend_an in H0. simpl in H0.
           easy.
       - case_eq b2; intros.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_receivea s3 s4 s5) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0.
           easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_send q1 n0 s3 s4) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0.
           inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [|(s3, s4, merge_bp_cont p b1 w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize(IHb1 q0 (bp_end) l1 l2 s1 s2 w1 w2).
           apply IHb1. easy.
           rewrite bpend_an. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_mergea s3 s4 s5 b) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite(st_eq(merge_bp_cont q0 (bp_merge q1 n0 s3 s4 b) (q0 ! [|(l2, s2, w2)|]))) in H0.
           simpl in H0. inversion H0. subst.
           rewrite(st_eq((merge_bp_cont p (bp_merge q1 n s3 s4 b1) w1))). simpl.
           rewrite(coseq_eq(act (q1 ! [|(s3, s4, merge_bp_cont p b1 w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (q1, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy.
           intro Hb. apply n0. inversion Hb. easy.
           specialize(IHb1 q0 b l1 l2 s1 s2 w1 w2).
           apply IHb1. easy. easy.
         + subst. 
           rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [|(l1, s1, w1)|]))) in H0.
           rewrite bpend_an in H0. simpl in H0. inversion H0. subst.
           rewrite(st_eq( (merge_bp_cont p (bp_merge q0 n l2 s2 b1) w1))). simpl.
           rewrite(coseq_eq(act (q0 ! [|(l2, s2, merge_bp_cont p b1 w1)|]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (q0, snd)) (ys := (act(merge_bp_cont p b1 w1))). simpl. easy. easy.
       - rewrite bpend_an in H0.
         rewrite bpend_an.
         apply insndBp in H0. easy. easy.
Qed.

Lemma actNeq: forall w1 w2, act_neq w1 w2 -> w1 ~< w2 -> False.
Proof. intros.
       unfold act_neq in H.
       destruct H as ((q,ac), [ (Ha, Hb) | (Ha, Hb)]).
       - case_eq ac; intros.
         + subst. apply Hb.
           punfold H0. inversion H0.
           subst. 
(*            apply mem_ext in H2. *)
           case_eq (eqb p q); intros.
           ++ rewrite eqb_eq in H3. subst.
              rewrite actApLcomb. apply eq0. right. 
              rewrite(coseq_eq(act (q & (cocons (l, s', w') conil)))). unfold coseq_id.
              simpl.
              apply CoInSplit1 with (y := (q, rcv)) (ys:= (act w')).
              simpl. easy. easy.
           ++ rewrite eqb_neq in H3.
              unfold act_eq in H2.
              rewrite(coseq_eq(act (p & (cocons (l, s, w) conil)))) in Ha.
              unfold coseq_id in Ha. simpl in Ha.
              inversion Ha. subst. simpl in H4. inversion H4.
              subst. easy.
              subst. simpl in H4. inversion H4. subst.
              apply H2 in H6.
              rewrite actApLcomb in H6.
              rewrite actApLcomb.
              apply eq0.
              apply eqscsrcv in H6.
              destruct H6 as [H6 | H6].
              * left. easy.
              * right.
                rewrite(coseq_eq(act (p & (cocons (l, s', w') conil)))). unfold coseq_id.
                simpl. 
                apply CoInSplit2 with (y := (p, rcv)) (ys:= (act w')). simpl. easy. easy. easy.
         + subst. 
(*          apply mem_ext in H2. *)
           rewrite actBpLcomb. apply eq0.
           rewrite(coseq_eq(act (p ! (cocons (l, s, w) conil)))) in Ha. unfold coseq_id in Ha.
           simpl in Ha. inversion Ha.
           subst. easy.
           subst.
           simpl in H3. inversion H3. subst.
           unfold act_eq in H2.
           apply H2 in H5.
           rewrite actBpLcomb in H5. apply eqscsrcv in H5.
           destruct H5 as [H5 | H5].
           left. easy.
           right.
           apply CoInSplit2 with (y := (p, snd)) (ys:= (act w')). 
           rewrite(coseq_eq(act (p ! cocons (l, s', w') conil))). unfold coseq_id. simpl. easy. easy. easy.
         + subst. rewrite(coseq_eq(act (end))) in Ha.
           unfold coseq_id in Ha. simpl in Ha.
           inversion Ha. subst. easy. subst. easy.
           apply refinementR2_mon.
       - subst. apply Hb.
         punfold H0. inversion H0.
         subst. 
(*          apply mem_ext in H2. *)
         rewrite(coseq_eq(act (p & (cocons (l, s, w) conil)))) in Ha.
         unfold coseq_id in Ha. simpl in Ha. 
         inversion Ha. subst. simpl in H3. easy.
         subst. simpl in H3. inversion H3. subst.
         apply H2 in H5.
         rewrite actApLcomb in H5.
         apply eqscssnd in H5.
         rewrite actApLcomb.
         apply eq0.
         destruct H5 as [H5 | H5].
         left. easy.
         right.
         apply CoInSplit2 with (y := (p, rcv)) (ys:= (act w')). simpl.
         rewrite(coseq_eq(act (p & cocons (l, s', w') conil))). simpl. easy. easy. easy.
         subst. 
(*          apply mem_ext in H2. *)
         case_eq (eqb p q); intros.
         ++ rewrite eqb_eq in H3. subst.
            rewrite actBpLcomb. apply eq0. right.
            rewrite(coseq_eq(act (q ! (cocons (l, s', w') conil)))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := (q, snd)) (ys:= (act w')). easy. easy.
         ++ rewrite eqb_neq in H3.
            unfold act_eq in H2.
            rewrite(coseq_eq(act (p ! (cocons (l, s, w) conil)))) in Ha.
            unfold coseq_id in Ha. simpl in Ha.
            inversion Ha. subst. simpl in H4. inversion H4.
            subst. easy.
            subst. simpl in H4. inversion H4. subst.
            apply H2 in H6.
            rewrite actBpLcomb in H6.
            rewrite actBpLcomb.
            apply eq0.
            apply eqscssnd in H6.
            destruct H6 as [H6 | H6].
            left. easy.
            right.
            rewrite(coseq_eq(act (p ! (cocons (l, s', w') conil)))). unfold coseq_id. simpl.
            apply CoInSplit2 with (y := (p, snd)) (ys:= (act w')). simpl. easy. easy. easy.
         ++ subst. rewrite(coseq_eq(act (end))) in Ha.
             unfold coseq_id in Ha. simpl in Ha.
             inversion Ha. subst. easy. subst. easy.
             apply refinementR2_mon.

       - case_eq ac; intros.
         + subst. apply Hb.
           punfold H0. inversion H0.
           subst. 
(*            apply mem_ext in H2. *)
           case_eq (eqb p q); intros.
           ++ rewrite eqb_eq in H3. subst.
              rewrite(coseq_eq(act (q & (cocons (l, s, w) conil)))). unfold coseq_id. simpl.
              apply CoInSplit1 with (y := (q, rcv)) (ys:= (act w)). easy. easy.
           ++ rewrite eqb_neq in H3.
              unfold act_eq in H2.
              rewrite actApLcomb in Ha.
              apply eqscsrcv in Ha.
              assert(In (q, rcv) (actAn p a n) \/ coseqIn (q, rcv) (act w')).
              { destruct Ha. left. easy.
                right.
                inversion H4. subst. simpl in H5.
                rewrite(coseq_eq(act (p & cocons (l, s', w') conil))) in H5. simpl in H5.
                inversion H5. subst. easy.
                rewrite(coseq_eq(act (p & cocons (l, s', w') conil))) in H5. simpl in H5.
                inversion H5.
                subst. easy.
              }
              apply eqscs in H4.
              rewrite actApLcomb in H2.
              apply H2 in H4.
              rewrite(coseq_eq(act (p & (cocons (l, s, w) conil)))). unfold coseq_id. simpl.
              apply CoInSplit2 with (y := (p, rcv)) (ys:= (act w)). simpl. easy.
              unfold not. intro Hx. apply H3.
              inversion Hx. easy. easy.
              subst.
              unfold act_eq in H2.
(*               apply mem_ext in H2. *)
              rewrite actBpLcomb in Ha.
              apply eqscsrcv in Ha.
              assert(In (q, rcv) (actBn p b n) \/ coseqIn (q, rcv) (act w')).
              { destruct Ha. left. easy.
                right.
                rewrite(coseq_eq(act (p ! cocons (l, s', w') conil))) in H3. simpl in H3.
                inversion H3. subst. simpl in H4. easy.
                subst. simpl in H4. inversion H4. subst. easy.
              }
              apply eqscs in H3.
              unfold act_eq in H2.
              rewrite actBpLcomb in H2.
              apply H2 in H3.
              rewrite(coseq_eq(act (p ! (cocons (l, s, w) conil)))). unfold coseq_id. simpl.
              apply CoInSplit2 with (y := (p, snd)) (ys:= (act w)). simpl. easy. easy. easy.
              subst. rewrite(coseq_eq(act (end))) in Ha.
              unfold coseq_id in Ha. simpl in Ha.
              inversion Ha. subst. easy. subst. easy.
              apply refinementR2_mon.
         + subst.
           apply Hb.
           punfold H0. inversion H0.
           subst.
(*            apply mem_ext in H2. *)
           unfold act_eq in H2.
           rewrite actApLcomb in H2.
           rewrite actApLcomb in Ha.
           apply eqscssnd in Ha.
           assert(In (q, snd) (actAn p a n) \/ coseqIn (q, snd) (act w')).
           { destruct Ha. left. easy.
             right.
             rewrite(coseq_eq((act (p & cocons (l, s', w') conil)))) in H3. simpl in H3.
             inversion H3. subst. simpl in H4. easy.
             subst. simpl in H4. inversion H4. subst. easy.
           }
           apply eqscs in H3.
           apply H2 in H3.
           rewrite(coseq_eq(act (p & (cocons (l, s, w) conil)))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (p, rcv)) (ys:= (act w)). simpl. easy. easy. easy.
         + subst.
         case_eq (eqb p q); intros.
         ++ rewrite eqb_eq in H3. subst.
            rewrite(coseq_eq(act (q ! (cocons (l, s, w) conil)))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := (q, snd)) (ys:= (act w)). simpl. easy. easy.
         ++ rewrite eqb_neq in H3.
            unfold act_eq in H2.
(*             apply mem_ext in H2. *)
            rewrite actBpLcomb in Ha.
            apply eqscssnd in Ha.
            assert(In (q, snd) (actBn p b n) \/ coseqIn (q, snd) (act w')).
            { destruct Ha.
              left. easy.
              right.
                inversion H4. subst. simpl in H5.
                rewrite(coseq_eq(act (p ! cocons (l, s', w') conil))) in H5. simpl in H5.
                inversion H5. subst. easy.
                subst.
                rewrite(coseq_eq(act (p ! cocons (l, s', w') conil))) in H5. simpl in H5.
                inversion H5.
                subst. easy.
            }
            apply eqscs in H4.
            unfold act_eq in H2.
            rewrite actBpLcomb in H2.
            apply H2 in H4.
            rewrite(coseq_eq(act (p ! (cocons (l, s, w) conil)))). unfold coseq_id. simpl.
            apply CoInSplit2 with (y := (p, snd)) (ys:= (act w)). simpl. easy.
            intro Hx. apply H3. inversion Hx. easy. easy.
            subst. rewrite(coseq_eq(act (end))) in Ha.
            unfold coseq_id in Ha. simpl in Ha.
            inversion Ha. subst. easy. subst. easy.
            apply refinementR2_mon.
Qed.

Lemma extdp: forall {d} w, singleton w -> singleton (merge_dp_cont d w).
Proof. induction d; intros.
       rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) w)).
       simpl. apply extr. easy.
       rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) w)).
       simpl. apply exts. easy.
       rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 d) w)).
       simpl. apply extr, IHd. easy.
       rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 d) w)).
       simpl. apply exts, IHd. easy.
       rewrite(st_eq(merge_dp_cont dp_end w)). simpl.
       destruct w; easy.
Defined.

Lemma extdpn: forall {n d} w, singleton w -> singleton (merge_dp_contn d w n).
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply extdp.
       apply IHn. easy.
Defined.

Lemma extdpf: forall {d} w, singleton w -> singleton (merge_dpf_cont d w).
Proof. induction d; intros.
       rewrite(st_eq(merge_dpf_cont (dpf_receive s s0 s1 d) w)).
       simpl. apply extr. apply IHd; easy.
       
       rewrite(st_eq(merge_dpf_cont (dpf_send s s0 s1 d) w)).
       simpl. apply exts. apply IHd; easy.
 
       rewrite(st_eq(merge_dpf_cont dpf_end w)). simpl.
       destruct w; easy.
Defined.

Lemma extdpfn: forall {n d} w, singleton w -> singleton (merge_dpf_contn d w n).
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply extdpf.
       apply IHn. easy.
Defined.

Lemma dpend_an: forall w, merge_dp_cont (dp_end) w = w.
Proof. intros.
       rewrite(st_eq(merge_dp_cont dp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma dpend_ann: forall n w, merge_dp_contn (dp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(st_eq(merge_dp_cont dp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma mergeSw5: forall d l w,
merge_dp_cont (listDp (dpList d ++ l)) w =
merge_dp_cont d (merge_dp_cont (listDp l) w).
Proof. intros d.
       induction d; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 dp_end) w)). simpl.
       rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) (merge_dp_cont dp_end w))). simpl.
       rewrite dpend_an. easy.
       rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 (listDp (d :: l0))) w)).
       rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) (merge_dp_cont (listDp (d :: l0)) w))).
       simpl. easy.
       rewrite(st_eq(merge_dp_cont (listDp (dpList (dp_send s s0 s1) ++ l)) w)).
       rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) (merge_dp_cont (listDp l) w))).
       simpl. easy.
       rewrite(st_eq(merge_dp_cont (listDp (dpList (dp_mergea s s0 s1 d) ++ l)) w )).
       rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 d) (merge_dp_cont (listDp l) w))).
       simpl.
       rewrite IHd. easy.
       rewrite(st_eq(merge_dp_cont (listDp (dpList (dp_merge s s0 s1 d) ++ l)) w )).
       rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 d) (merge_dp_cont (listDp l) w))).
       simpl. rewrite IHd. easy.
       simpl. rewrite dpend_an. easy.
Qed.

Lemma meqDp: forall n d w,
  merge_dp_cont (DpnA d n) w = merge_dp_contn d w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold DpnA. simpl.
       rewrite dpend_an. easy.
       simpl.
       rewrite <- IHn.

       unfold DpnA. simpl.
       rewrite mergeSw5. 
       easy.
Qed.

Lemma dpfend_dn: forall w, merge_dpf_cont (dpf_end) w = w.
Proof. intros.
       rewrite(st_eq(merge_dpf_cont dpf_end w)). simpl.
       destruct w; easy.
Qed.

Lemma eqdpsL: forall d w, merge_dp_cont d w = merge_dpf_cont (dp2dpf d) w.
Proof. intro d.
       induction d; intros.
       - simpl.
         rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) w)).
         rewrite(st_eq(merge_dpf_cont (dpf_receive s s0 s1 dpf_end) w)). simpl. 
         rewrite dpfend_dn. easy.
       - simpl.
         rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) w)).
         rewrite(st_eq(merge_dpf_cont (dpf_send s s0 s1 dpf_end) w)). simpl. 
         rewrite dpfend_dn. easy.
       - simpl.
         rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 d) w )).
         rewrite(st_eq(merge_dpf_cont (dpf_receive s s0 s1 (dp2dpf d)) w)). simpl.
         rewrite IHd. easy.
       - simpl.
         rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 d) w )).
         rewrite(st_eq(merge_dpf_cont (dpf_send s s0 s1 (dp2dpf d)) w)). simpl.
         rewrite IHd. easy.
       - simpl. rewrite dpfend_dn dpend_an. easy.
Qed.

Lemma eqdpsR: forall d w, merge_dpf_cont d w = merge_dp_cont (dpf2dp d) w.
Proof. intro d.
       induction d; intros.
       - rewrite(st_eq(merge_dpf_cont (dpf_receive s s0 s1 d) w )). simpl.
         rewrite IHd.
         destruct d.
         + rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 (dpf2dp (dpf_receive s2 s3 s4 d))) w)). simpl.
           easy.
         + rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 (dpf2dp (dpf_send s2 s3 s4 d))) w)). simpl.
           easy.
         + simpl. rewrite dpend_an.
           rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) w)). simpl. easy.
       - rewrite(st_eq(merge_dpf_cont (dpf_send s s0 s1 d) w )). simpl.
         rewrite IHd.
         destruct d.
         + rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 (dpf2dp (dpf_receive s2 s3 s4 d))) w)). simpl.
           easy.
         + rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 (dpf2dp (dpf_send s2 s3 s4 d))) w)). simpl.
           easy.
         + simpl. rewrite dpend_an.
           rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) w)). simpl. easy.
       - simpl. rewrite dpfend_dn dpend_an. easy. 
Qed.

Lemma Dmergel: forall a, Dpf_merge a dpf_end = a.
Proof. intro a.
       induction a; intros.
       - simpl. rewrite IHa. easy.
       - simpl. rewrite IHa. easy.
       - simpl. easy.
Qed.

Lemma DpnD3C: forall n a, DpnD3 a n.+1 =  Dpf_merge a (DpnD3 a n).
Proof. intros.
       simpl.
       case_eq n; intros.
       - simpl. rewrite Dmergel. easy.
       - easy.
Qed.

Lemma dpEnd: forall k, DpnD3 dpf_end k = dpf_end.
Proof. intro k.
       induction k; intros.
       - simpl. easy.
       - rewrite DpnD3C. rewrite IHk. simpl. easy. 
Qed.

Lemma merge_mergeD: forall d1 d2 w,
  merge_dpf_cont (Dpf_merge d1 d2) w = merge_dpf_cont d1 (merge_dpf_cont d2 w).
Proof. intro d1.
       induction d1; intros.
       - simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive s s0 s1 (Dpf_merge d1 d2)) w )).
         rewrite(st_eq(merge_dpf_cont (dpf_receive s s0 s1 d1) (merge_dpf_cont d2 w))). simpl.
         rewrite IHd1. easy.
       - simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send s s0 s1 (Dpf_merge d1 d2)) w )).
         rewrite(st_eq(merge_dpf_cont (dpf_send s s0 s1 d1) (merge_dpf_cont d2 w))). simpl.
         rewrite IHd1. easy.
       - simpl. rewrite dpfend_dn. easy.
Qed.

Lemma meqDpf: forall n d w,
  merge_dpf_cont (DpnD3 d n) w = merge_dpf_contn d w n.
Proof. intro n.
       induction n; intros.
       - simpl. rewrite dpfend_dn. easy.
       - rewrite DpnD3C. simpl. rewrite merge_mergeD IHn. easy.
Qed.

Lemma ApApeqInvAnd: forall p a1 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [|(l1, s1, w1)|]) =
  p & [|(l2, s2, w2)|] -> a1 = ap_end.
Proof. intros p a.
       induction a; intros.
       rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [|(l1, s1, w1)|]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [|(l1, s1, w1)|]))) in H. simpl in H.
       inversion H. subst. easy.
       easy.
Qed.

Lemma BpBpeqInvAnd: forall p b1 l1 l2 s1 s2 w1 w2,
  merge_bp_cont p b1 (p ! [|(l1, s1, w1)|]) =
  p ! [|(l2, s2, w2)|] -> b1 = bp_end.
Proof. intros p b.
       induction b; intros.
       rewrite(st_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [|(l1, s2, w1)|]))) in H.
       simpl in H. easy.
       subst.
       rewrite(st_eq(merge_bp_cont p (bp_send q n s s0) (p ! [|(l1, s1, w1)|]))) in H. simpl in H.
       inversion H. subst. easy.
       rewrite(st_eq( merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [|(l1, s2, w1)|]))) in H. simpl in H.
       inversion H.
       rewrite(st_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [|(l1, s1, w1)|]))) in H. simpl in H.
       inversion H. subst. easy.
       easy.
Qed.

Lemma refUnfDInv: forall d w w', (merge_dp_cont d (@und w) ~< merge_dp_cont d (@und w')) -> (@und w) ~< (@und w').
Proof. intro d. 
       induction d; intros.
       - setoid_rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) und)) in H. simpl in H.
         punfold H. inversion H.
         subst. 
         rewrite <- meqAp2 in H5, H6.
         pose proof H5 as H5a.
         apply ApApeqInvAnd in H5a.
         rewrite H5a in H5. rewrite apend_an in H5.
         inversion H5. subst.
         rewrite H5a in H6. rewrite apend_an in H6.
         unfold upaco2 in H6.
         destruct H6. punfold H0. pfold. easy.
         apply refinementR2_mon.
         easy.
         apply refinementR2_mon.
       - setoid_rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) und)) in H. simpl in H.
         punfold H. inversion H.
         subst. 
         rewrite <- meqBp in H5, H6.
         pose proof H5 as H5a.
         apply BpBpeqInvAnd in H5a.
         rewrite H5a in H5. rewrite bpend_an in H5.
         inversion H5. subst.
         rewrite H5a in H6. rewrite bpend_an in H6.
         unfold upaco2 in H6.
         destruct H6. punfold H0. pfold. easy.
         apply refinementR2_mon.
         easy.
         apply refinementR2_mon.
       - apply IHd. 
         setoid_rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 d) und)) in H. simpl in H.
         punfold H. inversion H.
         subst. simpl in *.
         pfold. unfold upaco2 in H6.
         destruct H6.
         punfold H0.
         rewrite <- meqAp2 in H5, H0, H7.
         pose proof H5 as H5a.
         apply ApApeqInvAnd in H5a.
         assert((s & [|(s0, s1, merge_dp_cont d und)|]) = merge_ap_cont s (ap_end) (s & [|(s0, s1, merge_dp_cont d und)|])).
         { rewrite apend_an. easy. }
         rewrite H1 in H5.
         apply ApApeqInv in H5.
         inversion H5. subst.
         rewrite H5a in H0. rewrite apend_an in H0. easy.
         apply refinementR2_mon.
         easy.
         apply refinementR2_mon.

         apply IHd.
         setoid_rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 d) und)) in H. simpl in H.
         punfold H. inversion H.
         subst. simpl in *.
         pfold. unfold upaco2 in H6.
         destruct H6.
         punfold H0.
         rewrite <- meqBp in H5, H0, H7.
         pose proof H5 as H5a.
         apply BpBpeqInvAnd in H5a.
         assert(s ! [|(s0, s1, merge_dp_cont d und)|] = merge_bp_cont s (bp_end) (s ! [|(s0, s1, merge_dp_cont d und)|])).
         { rewrite bpend_an. easy. }
         rewrite H1 in H5.
         apply BpBpeqInv2 in H5.
         inversion H5. subst.
         rewrite H5a in H0. rewrite bpend_an in H0. easy.
         apply refinementR2_mon.
         easy.
         apply refinementR2_mon.
         setoid_rewrite(st_eq(merge_dp_cont dp_end und)) in H. simpl in H.
         destruct und, und; easy.
Qed.

Lemma refUnfD: forall d w w', (@und w) ~< (@und w') -> merge_dp_cont d (@und w) ~< merge_dp_cont d (@und w').
Proof. intros.
       destruct w as (w, Hw).
       destruct w' as (w', Hw'). 
       simpl in *.
       revert w w' Hw Hw' H.
       induction d; intros.
       - setoid_rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) w)).
         setoid_rewrite(st_eq(merge_dp_cont (dp_receive s s0 s1) w')). simpl.
         pfold.
         specialize (ref2_a (upaco2 refinementR2 bot2) w w' s s0 s1 s1 (ap_end) 1); intro Ha.
         rewrite !apend_ann in Ha.
         apply Ha. constructor. left. pfold.
         punfold H.
         apply refinementR2_mon.
         specialize(classic(act_eq w w')); intros Hact.
         destruct Hact. easy.
         apply act_eq_neq in H0.
         apply actNeq in H0. easy.
         easy.
       - setoid_rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) w )).
         setoid_rewrite(st_eq(merge_dp_cont (dp_send s s0 s1) w')). simpl.
         pfold.
         specialize (ref2_b (upaco2 refinementR2 bot2) w w' s s0 s1 s1 (bp_end) 1); intro Ha.
         rewrite !bpend_ann in Ha.
         apply Ha. constructor. left. pfold.
         punfold H.
         apply refinementR2_mon.
         specialize(classic(act_eq w w')); intros Hact.
         destruct Hact. easy.
         apply act_eq_neq in H0.
         apply actNeq in H0. easy.
         easy.
       - rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 d) w)).
         rewrite(st_eq(merge_dp_cont (dp_mergea s s0 s1 d) w')). simpl.
         pfold.
         specialize (ref2_a (upaco2 refinementR2 bot2) (merge_dp_cont d w) (merge_dp_cont d w') s s0 s1 s1 (ap_end) 1); intro Ha.
         rewrite !apend_ann in Ha.
         apply Ha. constructor.
         specialize(IHd w w' Hw Hw').
         left.
         unfold refinement2 in IHd. apply IHd.
         pfold. punfold H.
         apply refinementR2_mon.
         specialize(classic(act_eq (merge_dp_cont d w) (merge_dp_cont d w'))); intros Hact.
         destruct Hact.
         easy.
         apply act_eq_neq in H0.
         apply actNeq in H0. easy.
         apply IHd. easy. easy. easy.
       - rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 d) w)).
         rewrite(st_eq(merge_dp_cont (dp_merge s s0 s1 d) w')). simpl.
         pfold.
         specialize (ref2_b (upaco2 refinementR2 bot2) (merge_dp_cont d w) (merge_dp_cont d w') s s0 s1 s1 (bp_end) 1); intro Ha.
         rewrite !bpend_ann in Ha.
         apply Ha. constructor.
         specialize(IHd w w' Hw Hw').
         left.
         unfold refinement2 in IHd. apply IHd.
         pfold. punfold H.
         apply refinementR2_mon.
         specialize(classic(act_eq (merge_dp_cont d w) (merge_dp_cont d w'))); intros Hact.
         destruct Hact.
         easy.
         apply act_eq_neq in H0.
         apply actNeq in H0. easy.
         apply IHd. easy. easy. easy.
       - rewrite !dpend_an. easy.
Qed.

Lemma pahselExt_so: forall ys xs l s y,
  copathsel l s ys y ->
  (Forall2Co (fun u v : string * local.sort * st => exists (l : string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2so bot2 t t') ys xs) ->
  exists u, copathsel l s xs u /\ st2soC y u.
Proof. intros.
       revert xs H0.
       induction H; intros.
       - pinversion H0. subst.
         destruct H2 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         exists t2. split. constructor. destruct H8c; easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H4 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         constructor. easy. easy. easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H4 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         apply pselneqs. easy. easy. easy.
         apply mon_f2Ho.
Qed.

Lemma pahselExt_soR: forall ys xs l s y,
  copathsel l s ys y ->
  (Forall2Co (fun u v : string * local.sort * st =>exists (l : string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2so bot2 t t') xs ys) ->
  exists u, copathsel l s xs u /\ st2soC u y.
Proof. intros.
       revert xs H0.
       induction H; intros.
       - pinversion H0. subst.
         destruct H3 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         exists t1. split. constructor. destruct H8c; easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H5 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         constructor. easy. easy. easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H5 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         apply pselneqs. easy. easy. easy.
         apply mon_f2Ho.
Qed.

Lemma pahselExt_si: forall ys xs l s y,
  copathsel l s xs y ->
  (Forall2Co (fun u v : string * local.sort * st => exists (l : string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2si bot2 t t') ys xs) ->
  exists u, copathsel l s ys u /\ st2siC u y.
Proof. intros.
       revert ys H0.
       induction H; intros.
       - pinversion H0. subst.
         destruct H3 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         exists t1. split. constructor. destruct H8c; easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H5 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         constructor. easy. easy. easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H5 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         apply pselneqs. easy. easy. easy.
         apply mon_f2Ho.
Qed.

Lemma pahselExt_siR: forall ys xs l s y,
  copathsel l s xs y ->
  (Forall2Co (fun u v : string * local.sort * st => exists (l : string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2si bot2 t t') xs ys) ->
  exists u, copathsel l s ys u /\ st2siC y u.
Proof. intros.
       revert ys H0.
       induction H; intros.
       - pinversion H0. subst.
         destruct H2 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         exists t2. split. constructor. destruct H8c; easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H4 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         constructor. easy. easy. easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H4 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         apply pselneqs. easy. easy. easy.
         apply mon_f2Ho.
Qed.

Lemma so_siDec: forall x y z, st2soC x y -> st2siC z x -> st2sisoC z y.
Proof. pcofix CIH.
       intros.
       pinversion H0.
       - subst. pinversion H1.
         subst. pfold. constructor.
         apply st2si_mon.
       - subst. pinversion H1.
         subst.
         pinversion H5. subst.
         destruct H7 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         pinversion H8. subst.
         pfold. apply st2siso_snd with (y := y0).
         right. apply CIH with (x := t2). easy. easy. easy.
         apply mon_f2Ho.
         apply mon_f2Ho.
         apply st2si_mon.
       - subst.
         pinversion H1.
         subst.
         assert (exists u, copathsel l s xs u /\ st2soC y u).
         { apply pahselExt_so with (xs := xs) in H6. easy. easy. }
         destruct H2 as (u,(H3a,H3b)).
         pfold.
         apply st2siso_rcv with (y := u).
         right. apply CIH with (x := y).
         easy. easy.
         easy.
         apply st2si_mon.
         apply st2so_mon.
Qed.

Lemma si_soDec: forall x y z, st2siC x y -> st2soC z x -> st2sisoC z y.
Proof. pcofix CIH.
       intros.
       pinversion H0.
       - subst. pinversion H1.
         subst. pfold. constructor.
         apply st2so_mon.
       - subst. pinversion H1.
         subst.
         pinversion H5. subst.
         destruct H7 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         pinversion H8. subst.
         pfold. apply st2siso_rcv with (y := y0).
         right. apply CIH with (x := t2). easy. easy. easy.
         apply mon_f2Ho.
         apply mon_f2Ho.
         apply st2so_mon.
       - subst.
         pinversion H1.
         subst.
         assert (exists u, copathsel l s xs u /\ st2siC y u).
         { apply pahselExt_siR with (ys := xs) in H6. easy. easy. }
         destruct H2 as (u,(H3a,H3b)).
         pfold.
         apply st2siso_snd with (y := u).
         right. apply CIH with (x := y).
         easy. easy.
         easy.
         apply st2so_mon.
         apply st2si_mon.
Qed.

