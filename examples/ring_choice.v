Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.acteqfacts ST.src.nondepro ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

Local Open Scope string_scope.

Definition ltB := lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, (lt_var 0));
                                                                 ("sub", I, (lt_var 0))])]).

Definition ltBOp := lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, (lt_var 0))]); 
                                        ("sub", I, lt_receive "A" [("add", I, (lt_var 0))])]).

CoFixpoint rcp := st_receive "A" [("add", I, st_send "C" [("add", I, rcp);
                                                          ("sub", I, rcp)])].

CoFixpoint rcop := st_send "C" [("add", I, st_receive "A" [("add", I, rcop)]); 
                                ("sub", I, st_receive "A" [("add", I, rcop)])].


CoFixpoint w1 := st_receive "A" [("add", I, st_send "C" [("add", I, w1)])].
CoFixpoint w2 := st_send "C" [("add", I, st_receive "A" [("add", I, w2)])].

CoFixpoint w3 := st_receive "A" [("add", I, st_send "C" [("sub", I, w3)])].
CoFixpoint w4 := st_send "C" [("sub", I, st_receive "A" [("add", I, w4)])].

Definition d1: Dpf := dpf_receive "A" "add" (I) (dpf_send "C" "add" (I) dpf_end).
Definition d2: Dpf := dpf_receive "A" "add" (I) (dpf_send "C" "sub" (I) dpf_end).
Definition d3: Dpf := dpf_send "C" "add" (I) (dpf_receive "A" "add" (I) dpf_end).
Definition d4: Dpf := dpf_send "C" "sub" (I) (dpf_receive "A" "add" (I) dpf_end).

Definition w5 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) w1 k.
Definition w6 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) w3 k.
Definition w7 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) w2 k.
Definition w8 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) w4 k.


Definition actL := [("A",rcv); ("C",snd)].

Lemma acteqr1: coseqInLC (act w2) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. 
       rewrite(coseq_eq(act ("A" & [("add", I, w2)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr2: coseqInLC (act w1) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, w1)])]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. 
       rewrite(coseq_eq(act ("C" ! [("add", I, w1)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr3: coseqInR actL (act w2).
Proof. unfold actL.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("C", snd)) (ys := (act ("A" & [("add", I, w2)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("A" & [("add", I, w2)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w2)). simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [("add", I, w2)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr4: coseqInR actL (act w1).
Proof. unfold actL.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, w1)])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, w1)]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, w1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [("add", I, w1)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w1)). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr5: coseqInLC (act ("A" & [("add", I, w2)])) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act ("A" & [("add", I, w2)]))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr1.
Qed.

Lemma acteqr6: coseqInLC (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr2.
Qed.

Lemma acteqr7: coseqInR actL (act ("A" & [("add", I, w2)])).
Proof. unfold actL.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, "A" & [("add", I, w2)])])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [("add", I, w2)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr8: coseqInR actL (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)).
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w1)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act w1)). simpl. easy. easy.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, w1)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, w1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [("add", I, w1)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w1)). simpl. easy. easy.
       constructor.
Qed.

Lemma refm1: forall m W1 W2, 
  refinement W1 W2 ->
  refinement (merge_dpf_cont (DpnD3 d4 m) W1) (merge_dpf_cont (DpnD3 d2 m) W2).
Proof. intro m.
       induction m; intros.
       - simpl. rewrite !dpfend_dn. easy.
       - rewrite !DpnD3C !merge_mergeD.
         unfold d4 at 1.
         unfold d2 at 1.
         rewrite(st_eq((merge_dpf_cont (dpf_send "C" "sub" (I) (dpf_receive "A" "add" (I) dpf_end)) (merge_dpf_cont (DpnD3 d4 m) W1)))).
         simpl.
         rewrite(st_eq  (merge_dpf_cont (dpf_receive "A" "add" (I) (dpf_send "C" "sub" (I) dpf_end)) (merge_dpf_cont (DpnD3 d2 m) W2))).
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) dpf_end) (merge_dpf_cont (DpnD3 d4 m) W1))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "C" "sub" (I) dpf_end) (merge_dpf_cont (DpnD3 d2 m) W2))). simpl.
         rewrite !dpfend_dn.
         pfold.
         specialize(ref_b (upaco2 refinementR bot2)
                          ("A" & [("add", I, merge_dpf_cont (DpnD3 d4 m) W1)])
                          (merge_dpf_cont (DpnD3 d2 m) W2)
                          "C" "sub" (I) (I)
                          (bp_receivea "A" "add" (I)) 1
                           ); intro HS.
        simpl in HS.
        rewrite(st_eq((merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [("sub", I, merge_dpf_cont (DpnD3 d2 m) W2)])))) in HS. simpl in HS.
        apply HS.
        constructor.
        left.
        rewrite(st_eq((merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_dpf_cont (DpnD3 d2 m) W2)))). simpl.
        pfold.
        specialize(ref_a (upaco2 refinementR bot2)
                         (merge_dpf_cont (DpnD3 d4 m) W1)
                         (merge_dpf_cont (DpnD3 d2 m) W2)
                         "A" "add" (I) (I)
                         (ap_end) 1
                          ); intro HR.
       simpl in HR.
       rewrite !apend_an in HR.
       apply HR.
       constructor.
       left. apply IHm. easy.
       
       
       apply IHm in H.
       apply refEquivR in H.
       pinversion H.

       (*receive*)
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [(l, s, w)]) = 
              (merge_apf_cont apf_end (p & [(l, s, w)]))).
       { rewrite apfend_an. easy. }
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5. apply actdRER. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply actdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         admit.
         easy.
         split.
         rewrite H5.
         apply IactdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply IactdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         admit.
         easy.
         easy.
       + exists ((p, rcv)::l1). exists ((p, rcv)::l2).
         split.
         rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         admit.
         easy.
         split.
         rewrite H5.
         apply IactdRNER. simpl. easy. easy. rewrite apfend_an. easy.
         split.
         apply IactdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         admit. easy.
         admit.

       (*send*)
       admit.
       (*end*)
       admit.
       apply refinementR3_mon.
       
       (*2nd goal*)
       
       (*receive*)
       apply IHm in H.
       apply refEquivR in H.
       pinversion H.
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [(l, s, w)]) = 
              (merge_apf_cont apf_end (p & [(l, s, w)]))).
       { rewrite apfend_an. easy. }
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_apf_cont (ApnA3 a n) (p & [(l, s', w')])))). simpl.
       
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split. 
         rewrite(coseq_eq (act ("A" & [("add", I, p & [(l, s, w)])]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         rewrite H5.
         apply actdRER. simpl. easy. easy.
         rewrite apfend_an. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [("add", I, merge_apf_cont (ApnA3 a n) (p & [(l, s', w')]))]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdRER. simpl. admit. admit.
         apply coseqINGA. easy.
         split.
         case_eq(eqb p "A"); intros.
         ++ rewrite eqb_eq in H6. subst.
            assert(("A" & [("add", I, "A" & [(l, s, w)])]) =
                   merge_apf_cont apf_end (("A" & [("add", I, "A" & [(l, s, w)])]))).
            { (* rewrite(st_eq(merge_apf_cont (apf_receive "A" "add" (I) apf_end) ("A" & [(l, s, w)]))). simpl. *)
              rewrite apfend_an. easy.
            }
            rewrite H6.
            apply IactdRER. simpl. easy.
            admit.
            apply IactdRER. simpl. easy.
            easy.
            rewrite apfend_an.
            apply InList. easy. easy.
         ++ assert(("A" & [("add", I, p & [(l, s, w)])]) =
                   merge_apf_cont (apf_receive "A" "add" (I) apf_end) (p & [(l, s, w)])).
            { rewrite(st_eq(merge_apf_cont (apf_receive "A" "add" (I) apf_end) (p & [(l, s, w)]))). simpl.
              rewrite apfend_an. easy.
            }
            rewrite H7.
            apply IactdRER.
            simpl. rewrite H6. easy.
            easy.
            apply InList. admit.
            rewrite(st_eq(merge_apf_cont (apf_receive "A" "add" (I) apf_end) w)). simpl.
            rewrite apfend_an.
            apply coseqRecvIn. easy.
         split.
         constructor. admit.
         apply coseqRecvIn.
         apply IactdRER.
         admit.
         admit.
         easy.
         admit.
       + exists(("A",rcv)::(p,rcv)::l1). exists(("A",rcv)::(p,rcv)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [("add", I, p & [(l, s, w)])]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [("add", I, merge_apf_cont (ApnA3 a n) (p & [(l, s', w')]))])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdRNER. admit. admit.
         easy.
         split.
         constructor. admit.
         constructor. admit.
         apply coseqRecvIn. apply coseqRecvIn. easy.
         split.
         constructor.
         admit.
         apply coseqRecvIn. 
         apply IactdRNER. admit. admit.
         easy.
         admit.
         
       (*send*)
       admit.
       (*end*)
       admit.
       apply refinementR3_mon.
Admitted.

Lemma refm2: forall m W1 W2, 
  refinement W1 W2 ->
  refinement (merge_dpf_cont (DpnD3 d3 m) W1) (merge_dpf_cont (DpnD3 d1 m) W2).
Proof. intro m.
       induction m; intros.
       - simpl. rewrite !dpfend_dn. easy.
       - rewrite !DpnD3C !merge_mergeD.
         unfold d3 at 1.
         unfold d1 at 1.
         rewrite(st_eq((merge_dpf_cont (dpf_send "C" "add" (I) (dpf_receive "A" "add" (I) dpf_end)) (merge_dpf_cont (DpnD3 d3 m) W1)))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (dpf_send "C" "add" (I) dpf_end)) (merge_dpf_cont (DpnD3 d1 m) W2))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) dpf_end) (merge_dpf_cont (DpnD3 d3 m) W1))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "C" "add" (I) dpf_end) (merge_dpf_cont (DpnD3 d1 m) W2))). simpl.
         rewrite !dpfend_dn.
         pfold.
         specialize(ref_b (upaco2 refinementR bot2)
                          ("A" & [("add", I, merge_dpf_cont (DpnD3 d3 m) W1)])
                          (merge_dpf_cont (DpnD3 d1 m) W2)
                          "C" "add" (I) (I)
                          (bp_receivea "A" "add" (I)) 1
                           ); intro HS.
        simpl in HS.
        rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [("add", I, merge_dpf_cont (DpnD3 d1 m) W2)]))) in HS.
        simpl in HS.
        apply HS.
        constructor.
        left.
        pfold.
        rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_dpf_cont (DpnD3 d1 m) W2))). simpl.
        specialize(ref_a (upaco2 refinementR bot2)
                         (merge_dpf_cont (DpnD3 d3 m) W1)
                         (merge_dpf_cont (DpnD3 d1 m) W2)
                         "A" "add" (I) (I)
                         (ap_end) 1
                          ); intro HR.
       simpl in HR.
       rewrite !apend_an in HR.
       apply HR.
       constructor.
       left. apply IHm. easy.
       admit.
       admit.
Admitted.

Lemma refw2w1: refinement w2 w1.
Proof. pcofix CIH.
       pfold.
       rewrite(st_eq w2). rewrite(st_eq w1). simpl.
       specialize(ref_b (upaco2 refinementR r) ("A" & [("add", I, w2)]) (w1)
                          "C" "add" (I) (I) (@bp_receivea "C" "A" "add" (I)) 1
                          ); intro Hb.
       simpl in Hb.
       rewrite(st_eq (merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [("add", I, w1)]))) in Hb. simpl in Hb.
       apply Hb.
       constructor.
       left. pfold.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)). simpl.
       clear Hb.

       specialize(ref_a (upaco2 refinementR r) (w2) (w1)
                          "A" "add" (I) (I) (ap_end) 1
                          ); intro Ha.
       simpl in Ha.
       rewrite(st_eq(merge_ap_cont "A" ap_end ("A" & [("add", I, w1)]))) in Ha. simpl in Ha.
       apply Ha. constructor.
       rewrite apend_an.
       right. exact CIH.
       admit.
       admit.
Admitted.

Lemma refw7w5: forall k n m, refinement (w7 n m k) (w5 n m k).
Proof. unfold w5, w7.
       intro k.
       induction k; intros.
       - simpl. apply refw2w1.
       - rewrite <- !meqDpf. rewrite DpnD3C.
         rewrite DpnD3C.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k)) w1) =
                (merge_dpf_cont (DpnD3 d1 n) (merge_dpf_cont (DpnD3 d2 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k) w1)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k)) w2) =
                (merge_dpf_cont (DpnD3 d3 n) (merge_dpf_cont (DpnD3 d4 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k) w2)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H0.
         apply refm2.
         apply refm1.
         specialize(IHk n m).
         rewrite <- !meqDpf in IHk. easy.
Qed.

Lemma refw4w3: refinement w4 w3.
Proof. pcofix CIH.
       pfold.
       rewrite(st_eq w4). rewrite(st_eq w3). simpl.
       specialize(ref_b (upaco2 refinementR r) ("A" & [("add", I, w4)]) (w3)
                          "C" "sub" (I) (I) (@bp_receivea "C" "A" "add" (I)) 1
                          ); intro Hb.
       simpl in Hb.
       rewrite(st_eq (merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [("sub", I, w3)]))) in Hb. simpl in Hb.
       apply Hb.
       constructor.
       left. pfold.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) w3)). simpl.
       clear Hb.

       specialize(ref_a (upaco2 refinementR r) (w4) (w3)
                          "A" "add" (I) (I) (ap_end) 1
                          ); intro Ha.
       simpl in Ha.
       rewrite(st_eq(merge_ap_cont "A" ap_end ("A" & [("add", I, w3)]))) in Ha. simpl in Ha.
       apply Ha. constructor.
       rewrite apend_an.
       right. exact CIH.
       admit.
       admit.
Admitted.

Lemma refw8w6: forall k n m, refinement (w8 n m k) (w6 n m k).
Proof. unfold w8, w6.
       intro k.
       induction k; intros.
       - simpl. apply refw4w3.
       - rewrite <- !meqDpf. rewrite DpnD3C.
         rewrite DpnD3C.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k)) w4) =
                (merge_dpf_cont (DpnD3 d3 n) (merge_dpf_cont (DpnD3 d4 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k) w4)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k)) w3) =
                (merge_dpf_cont (DpnD3 d1 n) (merge_dpf_cont (DpnD3 d2 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k) w3)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H0.
         apply refm2.
         apply refm1.
         specialize(IHk n m).
         rewrite <- !meqDpf in IHk. easy.
Qed.


Lemma st_rcp: forall (n m: nat), subtype rcop rcp.
Proof. intros n m.
       unfold subtype.
       assert (singleton w2) as Hw2.
       { pcofix CIH. rewrite(st_eq w2). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w1) as Hw1.
       { pcofix CIH. rewrite(st_eq w1). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w3) as Hw3.
       { pcofix CIH. rewrite(st_eq w3). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w4) as Hw4.
       { pcofix CIH. rewrite(st_eq w4). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       exists [((mk_siso w2 Hw2),(mk_siso w1 Hw1));((mk_siso w2 Hw2),(mk_siso w1 Hw1));
               ((mk_siso w4 Hw4),(mk_siso w3 Hw3));((mk_siso w4 Hw4),(mk_siso w3 Hw3))].
       simpl.
       split. split.

       pcofix CIH. pfold.
       rewrite(st_eq w2). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd.
       left. pfold. simpl.
       apply st2siso_rcv.
       simpl. right. apply CIH.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w1). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.
       
       split.
       pcofix CIH. pfold.
       rewrite(st_eq w2). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd.
       left. pfold. simpl.
       apply st2siso_rcv.
       simpl. right. apply CIH.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w1). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.
       
       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w4). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       right. exact CIH.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w3). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w4). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       right. exact CIH.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w3). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.
       easy.
       
       split.
       exists dpf_end. exists dpf_end. intro k.
       rewrite <- !meqDpf.
       rewrite dpEnd.
       rewrite !dpfend_dn.
       apply refw2w1.
       
       split.
       exists (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)).
       exists (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)).
       intro k.
       specialize (refw7w5 k n m); intro HH.
       unfold w7,w5 in HH. easy.

       split.
       exists dpf_end. exists dpf_end. intro k.
       rewrite <- !meqDpf.
       rewrite dpEnd.
       rewrite !dpfend_dn.
       apply refw4w3.

       split.
       exists (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)).
       exists (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)).
       intro k.
       specialize (refw8w6 k n m); intro HH.
       unfold w7,w5 in HH. easy.

       easy.
       

(*        exists actL.
       exists actL.
       split.
       apply acteqr1.
       split. rewrite apend_an.
       apply acteqr2.
       split.
       apply acteqr3.
       rewrite apend_an.
       split.
       apply acteqr4.
       easy.

       clear Hb.
       exists actL.
       exists actL.
       split.
       apply acteqr5.
       split.
       apply acteqr6.
       split.
       apply acteqr7.
       split.
       apply acteqr8.
       easy. *)
       
       
       
       
       
       

Qed.

Lemma ltB_rcp: lt2stC ltB rcp.
Proof. unfold ltB.
       rewrite (st_eq rcp). simpl.
       pcofix CIH.
       pfold.
       apply lt2st_mu. simpl.
       specialize (lt2st_rcv (upaco2 lt2st r)
       "A" ["add"] [(I)]
       [(lt_send "C"
         [("add", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
          ("sub", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))])]
       (["C" ! [("add", I, rcp); ("sub", I, rcp)]])
       ); intro HR.
       apply HR; clear HR. simpl. easy. 
       apply Forall_forall.
       intros (l, s).
       simpl. intros.
       destruct H as [H | H]. inversion H. subst.
       left. pfold.
       specialize (lt2st_snd (upaco2 lt2st r)
       "C" ["add"; "sub"] [(I); (I)]
       [(lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
        (lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))]
       [rcp; rcp]
       ); intro HS. simpl in HS.
       apply HS; clear HS. easy.
       apply Forall_forall.
       intros (l, s). simpl. intro H1.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcp). simpl. exact CIH.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcp). simpl. exact CIH.
       easy.
       easy.
Qed.

Lemma ltBop_rcop: lt2stC ltBOp rcop.
Proof. unfold ltBOp.
       rewrite (st_eq rcop). simpl.
       pcofix CIH.
       pfold. 
       apply lt2st_mu. simpl.
       specialize (lt2st_snd (upaco2 lt2st r)
         "C" ["add"; "sub"] [(I); (I)]
         [(lt_receive "A"
           [("add", I,
             lt_mu
               (lt_send "C"
                  [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
                   ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]);
        (lt_receive "A"
           [("add", I,
             lt_mu
               (lt_send "C"
                  [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
                   ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])]
           [("A" & [("add", I, rcop)]); ("A" & [("add", I, rcop)])]
       ); intro HS. simpl in HS.
       apply HS; clear HS. easy.
       apply Forall_forall.
       intros (l,s) H.
       simpl in H.
       destruct H as [H | H].
       inversion H. subst.
       left. pfold. simpl.
       specialize (lt2st_rcv (upaco2 lt2st r)
       "A" ["add"] [(I)]
       [(lt_mu
         (lt_send "C"
            [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
             ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]
       [rcop]
       ); intro HR. simpl in HR.
       apply HR; clear HR. easy.
       apply Forall_forall.
       intros (l, s) H1.
       simpl in H1.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcop). simpl. exact CIH.
       easy.
       destruct H as [H | H].
       inversion H. subst.
       left. pfold. simpl.
       specialize (lt2st_rcv (upaco2 lt2st r)
       "A" ["add"] [(I)]
       [(lt_mu
         (lt_send "C"
            [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
             ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]
       [rcop]
       ); intro HR. simpl in HR.
       apply HR; clear HR. easy.
       apply Forall_forall.
       intros (l, s) H1.
       simpl in H1.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcop). simpl. exact CIH.
       easy.
       easy.
Qed.

Lemma ltB_ltBop: forall (n m: nat), subltype ltBOp ltB rcop rcp ltBop_rcop ltB_rcp.
Proof. unfold subltype.
       exact st_rcp.
Qed.


