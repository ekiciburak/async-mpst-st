Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering 
ST.src.reorderingfacts ST.src.acteqfacts ST.src.nondepro ST.src.siso ST.src.inversion ST.types.local ST.subtyping.refinement ST.types.typenv.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.

Inductive projS (R: st -> participant -> st -> Prop): st -> participant -> st -> Prop :=
  | pjs_end : forall p, projS R st_end p st_end
  | pjs_snde: forall p l s w' w, R w' p w -> projS R (st_send p [|(l,s,w')|]) p (st_send p [|(l,s,w)|])
  | pjs_sndI: forall q l s w' p w, p <> q -> coseqIn (p, snd) (act w') -> R w' p w -> projS R (st_send q [|(l,s,w')|]) p w
  | pjs_sndN: forall q l s w' p, p <> q -> (coseqIn (p, snd) (act w') -> False) -> projS R (st_send q [|(l,s,w')|]) p st_end
  | pjs_rcvI: forall q l s w' p w, coseqIn (p, snd) (act w') -> R w' p w -> projS R (st_receive q [|(l,s,w')|]) p w
  | pjs_rcvN: forall q l s w' p, (coseqIn (p, snd) (act w') -> False) -> projS R (st_receive q [|(l,s,w')|]) p st_end.

Definition projSC w1 p w2 := paco3 projS bot3 w1 p w2.

Inductive projR (R: st -> participant -> st -> Prop): st -> participant -> st -> Prop :=
  | pjr_end : forall p, projR R st_end p st_end
  | pjr_rcve: forall p l s w' w, R w' p w -> projR R (st_receive p [|(l,s,w')|]) p (st_receive p [|(l,s,w)|])
  | pjr_rcvI: forall q l s w' p w, p <> q -> coseqIn (p, snd) (act w') -> R w' p w -> projR R (st_receive q [|(l,s,w')|]) p w
  | pjr_rcvN: forall q l s w' p, p <> q -> (coseqIn (p, snd) (act w') -> False) -> projR R (st_receive q [|(l,s,w')|]) p st_end
  | pjr_sndI: forall q l s w' p w, coseqIn (p, snd) (act w') -> R w' p w -> projR R (st_send q [|(l,s,w')|]) p w
  | pjr_sndN: forall q l s w' p, (coseqIn (p, snd) (act w') -> False) -> projR R (st_send q [|(l,s,w')|]) p st_end.

Definition projRC w1 p w2 := paco3 projR bot3 w1 p w2.

Inductive sRefinementR (R: st -> st -> Prop): st -> st -> Prop :=
  | sref_a  : forall w w' p l s s', subsort s' s ->
                                    R w w' ->
                                    sRefinementR R (st_receive p [|(l,s,w)|]) (st_receive p [|(l,s',w')|])
  | sref_b  : forall w w' p l s s', subsort s s' ->
                                    R w w' ->
                                    sRefinementR R (st_send p [|(l,s,w)|]) (st_send p [|(l,s',w')|])
  | sref_end: sRefinementR R st_end st_end.

Definition sRefinement w1 w2 := paco2 sRefinementR bot2 w1 w2.

Lemma mon_projs: monotone3 projS.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor.
       - constructor. apply LE. easy.
       - constructor. easy. easy. apply LE. easy.
       - apply pjs_sndN. easy. easy.
       - constructor. easy. apply LE. easy.
       - apply pjs_rcvN. easy.
Qed.

Lemma mon_projr: monotone3 projR.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor.
       - constructor. apply LE. easy.
       - constructor. easy. easy. apply LE. easy.
       - apply pjr_rcvN. easy. easy.
       - constructor. easy. apply LE. easy.
       - apply pjr_sndN. easy.
Qed.

Lemma prj_send_inv1: forall b p q l1 s1 w1 l2 s2 w2,
  isInB b p = false ->
  projSC (merge_bpf_cont b (p ! [|(l1, s1, w1)|])) p (q ! [|(l2, s2, w2)|]) ->
  p = q /\ l1 = l2 /\ s1 = s2 /\ projSC w1 p w2.
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq((merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [|(l1, s2, w1)|])))) in H0. simpl in H0.
         pinversion H0. subst.
         apply IHb; easy.
         apply mon_projs.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite(st_eq (merge_bpf_cont (bpf_send s s0 s1 b) (p ! [|(l1, s2, w1)|]))) in H0. simpl in H0.
         pinversion H0. subst. 
         rewrite String.eqb_refl in Ha. easy.
         subst.
         apply IHb; easy.
         apply mon_projs.
         rewrite bpfend_bn in H0.
         pinversion H0. subst. easy.
         subst. easy.
         apply mon_projs.
Qed.

Lemma inB_coseqL: forall b p w, coseqIn (p, snd) (act (merge_bpf_cont b w)) ->
  isInB b p \/ coseqIn (p, snd) (act w).
Proof. intro b.
       induction b; intros.
       - rewrite(coseq_eq(act (merge_bpf_cont (bpf_receive s s0 s1 b) w))) in H. simpl in H.
         simpl.
         inversion H. subst.
         inversion H0.
         subst. inversion H0. subst.
         apply IHb. easy.
       - rewrite(coseq_eq(act (merge_bpf_cont (bpf_send s s0 s1 b) w))) in H. simpl in H.
         inversion H. 
         subst. inversion H0. subst. simpl. rewrite String.eqb_refl. simpl. left. easy.
         subst. simpl. inversion H0. subst.
         assert(p <> s).
         { intro HH. apply H1. subst. easy. }
         apply String.eqb_neq in H3. rewrite H3. simpl.
         apply IHb. easy.
       - simpl. rewrite bpfend_bn in H. right. easy.
Qed.

Lemma inB_coseqR: forall b p w, isInB b p \/ coseqIn (p, snd) (act w) ->
  coseqIn (p, snd) (act (merge_bpf_cont b w)).
Proof. intro b.
       induction b; intros.
       - simpl in H. 
         rewrite(coseq_eq(act (merge_bpf_cont (bpf_receive s s0 s1 b) w))). simpl.
         destruct H as [H | H].
         + apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w))). easy. easy.
           apply IHb. left. easy.
         + apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w))). easy. easy.
           apply IHb. right. easy.
       - simpl in H.
         rewrite(coseq_eq(act (merge_bpf_cont (bpf_send s s0 s1 b) w))). simpl.
         destruct H as [H | H].
         + apply Bool.orb_true_iff in H.
           destruct H as [H | H].
           ++ rewrite String.eqb_eq in H. subst.
              apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))). easy. easy.
              case_eq(String.eqb p s); intros.
              * rewrite String.eqb_eq in H0. subst.
                apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))). easy. easy.
              * apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))). easy.
                intros HH. inversion HH. subst. rewrite String.eqb_refl in H0. easy.
           ++ apply IHb. left. easy.
         + case_eq(String.eqb p s); intros.
           * rewrite String.eqb_eq in H0. subst.
             apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))). easy. easy.
           * apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))). easy.
            intros HH. inversion HH. subst. rewrite String.eqb_refl in H0. easy.
           apply IHb. right. easy.
       - rewrite bpfend_bn. 
         destruct H as [H | H].
         + simpl in H. easy.
         + easy.
Qed.

Lemma inB_coseq: forall b p w, isInB b p \/ coseqIn (p, snd) (act w) <->
  coseqIn (p, snd) (act (merge_bpf_cont b w)).
Proof. split. 
       - intros. apply inB_coseqR; easy.
       - intros. apply inB_coseqL; easy.
Qed.

Lemma proj_send_b: forall b p w wb,
  isInB b p = false ->
  projSC w p wb ->
  projSC (merge_bpf_cont b w) p wb.
Proof. intros.
       pinversion H0.
       - subst.
         induction b; intros.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (end))). simpl.
           simpl in H.
           pfold. apply pjs_rcvN. intros.
           rewrite <- inB_coseq in H1.
           destruct H1 as [H1 | H1].
           * rewrite H in H1. easy.
           * rewrite(coseq_eq(act (end))) in H1. simpl in H1. inversion H1. subst. easy.
             subst. easy.
         + simpl in H.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (end))). simpl.
           rewrite orbtf in H.
           destruct H as (Ha, Hb).
           pfold. apply pjs_sndN. intros. apply String.eqb_neq in Ha. easy.
           rewrite <- inB_coseq. intro HH.
           destruct HH as [HH | HH]. rewrite Hb in HH. easy.
           rewrite(coseq_eq(act (end))) in HH. simpl in HH. inversion HH. subst. easy.
           subst. easy.
         + rewrite bpfend_bn. pfold. constructor.
       - subst. 
         induction b; intros.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s0 s1 s2 b) (p ! [|(l, s, w')|]))). simpl.
           pfold. constructor.
           rewrite <- inB_coseq. right. 
           rewrite(coseq_eq (act (p ! [|(l, s, w')|]))). simpl.
           apply CoInSplit1 with (y := (p, snd)) (ys := (act w')). easy. easy.
           left. apply IHb. easy.
         + rewrite(st_eq(merge_bpf_cont (bpf_send s0 s1 s2 b) (p ! [|(l, s, w')|]))). simpl.
           simpl in H.
           rewrite orbtf in H.
           destruct H as (Ha, Hb).
           pfold. constructor. rewrite String.eqb_neq in Ha. easy.
           rewrite <- inB_coseq. right.
           rewrite(coseq_eq (act (p ! [|(l, s, w')|]))). simpl.
           apply CoInSplit1 with (y := (p, snd)) (ys := (act w')). easy. easy.
           left. apply IHb. easy.
         + rewrite bpfend_bn. pfold. constructor. left. easy.
       - subst. 
         induction b; intros.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s0 s1 s2 b) (q ! [|(l, s, w')|])) ). simpl.
           pfold. constructor.
           rewrite <- inB_coseq. right.
           rewrite(coseq_eq (act (q ! [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. 
           intro HH. apply H1. inversion HH. subst. easy. easy.
           left. apply IHb. easy.
         + simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite(st_eq(merge_bpf_cont (bpf_send s0 s1 s2 b) (q ! [|(l, s, w')|]))). simpl.
           pfold. constructor. rewrite String.eqb_neq in Ha. easy.
           rewrite <- inB_coseq. right.
           rewrite(coseq_eq(act (q ! [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. 
           intro HH. apply H1. inversion HH. easy. easy.
           left. apply IHb. easy.
         + rewrite bpfend_bn. pfold. easy.
       - subst.
         induction b; intros.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s0 s1 s2 b) (q ! [|(l, s, w')|]))). simpl.
           pfold. apply pjs_rcvN. intro HH.
           simpl in H. 
           rewrite <- inB_coseq in HH. 
           destruct HH as [HH | HH].
           ++ rewrite H in HH. easy.
           ++ rewrite(coseq_eq(act (q ! [|(l, s, w')|]))) in HH. simpl in HH. inversion HH. subst.
              inversion H3. subst. easy.
              subst. inversion H3. subst. easy.
         + rewrite(st_eq(merge_bpf_cont (bpf_send s0 s1 s2 b) (q ! [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H. destruct H as (Ha, Hb).
           pfold. apply pjs_sndN. rewrite String.eqb_neq in Ha. easy.
           intro HH.
           rewrite <- inB_coseq in HH.
           destruct HH as [HH | HH].
           ++ rewrite Hb in HH. easy.
           ++ rewrite(coseq_eq(act (q ! [|(l, s, w')|]))) in HH. simpl in HH. inversion HH. subst.
              inversion H. subst. easy.
              subst. inversion H. subst. easy.
         + rewrite bpfend_bn. pfold. easy.
       - subst.
         induction b; intros.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s0 s1 s2 b) (q & [|(l, s, w')|])) ). simpl.
           simpl in H. pfold. constructor.
           rewrite <- inB_coseq. right.
           rewrite(coseq_eq(act (q & [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. easy. easy.
           left. apply IHb. easy.
         + rewrite(st_eq (merge_bpf_cont (bpf_send s0 s1 s2 b) (q & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H. destruct H as (Ha, Hb).
           pfold. constructor. rewrite String.eqb_neq in Ha. easy.
           rewrite <- inB_coseq. right.
           rewrite(coseq_eq(act (q & [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. easy. easy.
           left. apply IHb. easy.
         + rewrite bpfend_bn. pfold. easy.
       - subst.
         induction b; intros.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s0 s1 s2 b) (q & [|(l, s, w')|]))). simpl.
           simpl in H. pfold. apply pjs_rcvN. intro HH.
           rewrite <- inB_coseq in HH.
           destruct HH as [HH | HH].
           ++ rewrite H in HH. easy.
           ++ rewrite(coseq_eq(act (q & [|(l, s, w')|]))) in HH. simpl in HH. inversion HH. subst.
              inversion H. subst. easy.
              subst. inversion H2. subst. easy.
          + rewrite(st_eq (merge_bpf_cont (bpf_send s0 s1 s2 b) (q & [|(l, s, w')|]))). simpl.
            simpl in H. rewrite orbtf in H. destruct H as (Ha, Hb).
            pfold. apply pjs_sndN. rewrite String.eqb_neq in Ha. easy.
            intro HH. 
            rewrite <- inB_coseq in HH.
            destruct HH as [HH | HH].
            ++ rewrite Hb in HH. easy.
            ++ rewrite(coseq_eq(act (q & [|(l, s, w')|]))) in HH. simpl in HH. inversion HH. subst.
              inversion H. subst. inversion H. subst. easy.
          + rewrite bpfend_bn. pfold. easy.
       apply mon_projs.
Qed.

Lemma proj_send_bs: forall b p q l s w wb,
  p <> q ->
  isInB b p = false ->
  projSC w p wb ->
  projSC (q ! [|(l, s, merge_bpf_cont b w)|]) p wb.
Proof. intros.
       pinversion H1.
       - subst. pfold. apply pjs_sndN. easy.
         intros HH. rewrite <- inB_coseq in HH.
         admit.
       - subst. pfold. constructor. easy.
         rewrite <- inB_coseq. right. admit.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inB_coseq. right. admit.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_sndN. easy.
         intro HH. rewrite <- inB_coseq in HH. admit.
       - subst. pfold. constructor. easy.
         rewrite <- inB_coseq. right. admit.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_sndN. easy.
         intro HH. rewrite <- inB_coseq in HH.
         apply H2.
         admit.
       apply mon_projs.
Admitted.

Lemma proj_send_br: forall b p q l s w wb,
  isInB b p = false ->
  projSC w p wb ->
  projSC (q & [|(l, s, merge_bpf_cont b w)|]) p wb.
Proof. intros.
       pinversion H0.
       - subst. pfold. apply pjs_rcvN. 
         intro HH. rewrite <- inB_coseq in HH.
         admit.
       - subst. pfold. constructor.
         rewrite <- inB_coseq. right. admit.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. constructor.
         rewrite <- inB_coseq. right. admit.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_rcvN.
         intro HH. rewrite <- inB_coseq in HH. admit.
       - subst. pfold. constructor.
         rewrite <- inB_coseq. right. admit.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_rcvN.
         intro HH. rewrite <- inB_coseq in HH.
         admit.
       apply mon_projs.
Admitted.

Lemma prj_send_eq: forall p q l s w wa,
  singleton w ->
  projSC w p (q ! [|(l, s, wa)|]) ->
  p = q.
Proof. intros.
       pinversion H0. 
       - easy.
       - subst.
         apply inSendfE in H2; try easy.
         destruct H2 as (b1,(l1,(s1,(w1,(H2a,H2b))))).
         subst.
         apply prj_send_inv1 in H3. easy. easy.
         apply extsR in H. easy.
       - subst. 
         apply inSendfE in H1; try easy.
         destruct H1 as (b1,(l1,(s1,(w1,(H1a,H1b))))).
         subst.
         apply prj_send_inv1 in H2. easy. easy.
         apply extrR in H. easy.
       apply mon_projs.
Qed.

Lemma prj_send_inv2: forall p q l s w wa,
  singleton w ->
  projSC w p (q ! [|(l, s, wa)|]) ->
  p = q /\ exists b wb, w = (merge_bpf_cont b (q ! [|(l, s, wb)|])) /\ isInB b q = false /\ projSC wb p wa.
Proof. intros.
       specialize(prj_send_eq p q l s w wa H H0); intro Heq.
       subst. split. easy.
       pinversion H0.
       - subst. exists bpf_end. exists w'. rewrite bpfend_bn. easy.
       - subst.
         apply inSendfE in H2; try easy.
         destruct H2 as (b1,(l1,(s1,(w1,(H2a,H2b))))).
         subst.
         apply prj_send_inv1 in H3.
         destruct H3 as (H3a,(H3b,(H3c,H3d))).
         subst.
         exists (bpf_send q0 l0 s0 b1). exists w1.
         rewrite(st_eq(merge_bpf_cont (bpf_send q0 l0 s0 b1) (q ! [|(l, s, w1)|]))). simpl.
         split. easy. rewrite H2b. apply String.eqb_neq in H1. rewrite H1. easy. easy.
         apply extsR in H. easy.
       - subst.
         apply inSendfE in H1; try easy.
         destruct H1 as (b1,(l1,(s1,(w1,(H1a,H1b))))).
         subst.
         apply prj_send_inv1 in H2.
         destruct H2 as (H2a,(H2b,(H2c,H2d))).
         subst.
         exists (bpf_receive q0 l0 s0 b1). exists w1.
         rewrite(st_eq(merge_bpf_cont (bpf_receive q0 l0 s0 b1) (q ! [|(l, s, w1)|]) )). simpl.
         easy. easy.
         apply extrR in H. easy.
       apply mon_projs.
Qed.

Lemma prof_send_drop_snd: forall b p q l s w wb (Hs: singleton w),
  p <> q ->
  projSC (merge_bpf_cont b (p ! [|(l, s, w)|])) q wb ->
  projSC (merge_bpf_cont b w) q wb.
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq (merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         pfold. constructor.
         rewrite <- inB_coseq.
         rewrite <- inB_coseq in H7.
         destruct H7 as [H7 | H7].
         + left. easy.
         + right. rewrite(coseq_eq(act (p ! [|(l, s2, w)|]))) in H7. simpl in H7.
           inversion H7. subst. inversion H1. subst. easy.
           subst. inversion H1. subst. easy.
         left. apply IHb with (p := p) (l := l) (s := s2). easy.
         easy. easy.
       - subst.
         pfold. apply pjs_rcvN. intro HH. apply H7.
         rewrite <- inB_coseq. rewrite <- inB_coseq in HH.
         destruct HH as [HH | HH].
         + left. easy.
         + right.
           rewrite(coseq_eq(act (p ! [|(l, s2, w)|]))). simpl.
           apply CoInSplit2 with (y := (p, snd)) (ys := (act w)). easy. intro Hn. apply H. inversion Hn. easy.
           easy.
        apply mon_projs.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         pfold. constructor. left. apply IHb with (p := p) (l := l) (s := s2). easy.
         easy. easy. 
         subst.
         pfold. constructor. easy. 
         rewrite <- inB_coseq. rewrite <- inB_coseq in H8.
         destruct H8 as [H8 | H8].
         + left. easy.
         + right. rewrite(coseq_eq(act (p ! [|(l, s2, w)|]))) in H8. simpl in H8.
           inversion H8. subst. inversion H1. subst. easy.
           subst. inversion H1. subst. easy.
         left. apply IHb with (p := p) (l := l) (s := s2). easy.
         easy. easy.
         subst.
         pfold. apply pjs_sndN. easy.
         intro HH. apply H8.
         rewrite <- inB_coseq. rewrite <- inB_coseq in HH.
         destruct HH as [HH | HH].
         + left. easy.
         + right. rewrite(coseq_eq(act (p ! [|(l, s2, w)|]))). simpl.
           apply CoInSplit2 with (y := (p, snd)) (ys := (act w)). easy. intro Hn. apply H. inversion Hn. easy.
           easy.
        apply mon_projs.
       - rewrite bpfend_bn in H0.
         rewrite bpfend_bn.
         pinversion H0.
         subst. easy. subst. easy.
         subst.
         specialize(sinv w Hs); intros Hpw.
         destruct Hpw as [Hpw | [Hpw | Hpw]].
         + destruct Hpw as (p1,(l1,(s1,(w1,(Ha,Hb))))).
           subst.
           pfold. apply pjs_sndN.
           intro HH. subst. apply H8.
           rewrite(coseq_eq(act (p1 ! [|(l1, s1, w1)|]))). simpl.
           apply CoInSplit1 with (y := (p1, snd)) (ys := (act w1)). easy. easy.
           intro HH. apply H8.
           case_eq(String.eqb p1 q); intros.
           rewrite String.eqb_eq in H1. subst.
           rewrite(coseq_eq(act (q ! [|(l1, s1, w1)|]))). simpl.
           apply CoInSplit1 with (y := (q, snd)) (ys := (act w1)). easy. easy.
           rewrite(coseq_eq(act (p1! [|(l1, s1, w1)|]))). simpl.
           apply CoInSplit2 with (y := (p1, snd)) (ys := (act w1)). easy.
           apply String.eqb_neq in H1. intro HHa. apply H1. inversion HHa. easy.
           easy.
         + destruct Hpw as (p1,(l1,(s1,(w1,(Ha,Hb))))).
           subst. 
           pfold. apply pjs_rcvN.
           intro HH. subst. apply H8.
           rewrite(coseq_eq(act (p1 & [|(l1, s1, w1)|]))). simpl.
           apply CoInSplit2 with (y := (p1, rcv)) (ys := (act w1)). easy. easy.
           easy.
           subst. pfold. constructor.
        apply mon_projs.
Qed.

Lemma _B_7: forall w w' p w1 w2, refinement4 (@und w) (@und w') -> projSC (@und w) p (@und w1) -> projSC (@und w') p (@und w2) -> sRefinement (@und w1) (@und w2).
Proof. destruct w as (w, Pw).
       destruct w' as (w', Pw').
       destruct w1 as (w1, Pw1).
       destruct w2 as (w2, Pw2).
       generalize dependent w.
       generalize dependent w'.
       generalize dependent w1.
       generalize dependent w2.
       revert p. 
       pcofix CIH. simpl in CIH. simpl.
       intros.
       specialize(sinv w1 Pw1); intros Hpw1.
       destruct Hpw1 as [Hpw1 | [Hpw1 | Hpw1]].
       - destruct Hpw1 as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         specialize(sinv w2 Pw2); intros Hpw2.
         destruct Hpw2 as [Hpw2 | [Hpw2 | Hpw2]].
         + destruct Hpw2 as (q2, (l2, (s2, (wb, (Heq2, Hs2))))).
           subst.
           pinversion H1. subst.
           pinversion H2. subst. admit.
           subst.
           specialize(Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q ! [|(l, s, w'1)|])); intros HH.
           assert(isInB bpf_end q2 = false). easy.
           apply HH in H6. 2: { rewrite !bpfend_bn. easy. }
           destruct H6 as [H6 | H6].
           admit.
           destruct H6 as (b1,(w3,(s',(Ha,(Hb,(Hc,Hd)))))).
           apply pneqq7 in Hd; try easy.
           destruct Hd as (b2,(Hd,(He,Hf))).
           subst.
           apply prj_send_inv1 in H4.
           destruct H4 as (H4a,(H4b,(H4c,H4d))).
           subst. pfold. constructor. easy. 
           right.
           assert((q ! [|(l, s, merge_bpf_cont b2 (q2 ! [|(l2, s2, w3)|]))|]) = (merge_bpf_cont (bpf_send q l s b2) (q2 ! [|(l2, s2, w3)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b2) (q2 ! [|(l2, s2, w3)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (drop_send bpf_end (bpf_send q l s b2) q2 l2 s1 s2 w'0 w3); intro HD.
           rewrite bpfend_bn in HD.
           apply HD in H0. rewrite bpfend_bn in H0.
           apply CIH with (p := q2) (w' := (merge_bpf_cont (bpf_send q l s b2) w3)) (w := w'0).
           admit. admit. admit. admit.
           easy. easy.
           rewrite(st_eq(merge_bpf_cont (bpf_send q l s b2) w3)). simpl.
           apply proj_send_bs. easy. easy.
           easy. easy. simpl. rewrite Hd. apply String.eqb_neq in H. rewrite H. simpl. easy.
           easy.
           subst.
           specialize(Invert_Bpf_Apf bpf_end apf_end q1 l1 s1 w'0 (q & [|(l, s, w'1)|])); intros HH.
           assert(isInB bpf_end q2 = false). easy.
           
           apply HH in H4. 2: { rewrite bpfend_bn. rewrite apfend_an. easy. }
           destruct H4 as (b3,(w3,(s3,(Ha,(Hb,Hc))))).
(*            case_eq(String.eqb q q1); intros. rewrite String.eqb_eq in H4. subst. *)
           apply pneqq6 in Hc; try easy.
           destruct Hc as (b4,(Hc,(Hd,He))).
           subst.
           apply prj_send_inv1 in H3.
           destruct H3 as (H3a,(H3b,(H3c,H3d))). subst.
           pfold. constructor.
           easy.
           assert((q & [|(l, s, merge_bpf_cont b4 (q2 ! [|(l2, s2, w3)|]))|]) = 
                   (merge_bpf_cont (bpf_receive q l s b4) (q2 ! [|(l2, s2, w3)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b4) (q2 ! [|(l2, s2, w3)|]))). simpl. easy. }
           rewrite H3 in H0.
           specialize (drop_send bpf_end (bpf_receive q l s b4) q2 l2 s1 s2 w'0 w3); intro HD.
           rewrite !bpfend_bn in HD.
           apply HD in H0; try easy.
           right.
           apply CIH with (p := q2) (w' := (merge_bpf_cont (bpf_receive q l s b4) w3)) (w := w'0).
           admit. admit. admit. admit.
           easy. easy.
           rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b4) w3)). simpl.
           apply proj_send_br. easy. easy. easy.
           apply mon_projs.
           (*second inversion on H2 starts here*)
           subst.
           pinversion H2. subst.
           specialize(Invert_Bpf_Bpf bpf_end bpf_end q l s w'0 (q2 ! [|(l2, s2, w'1)|])); intros HH.
           assert(isInB bpf_end q2 = false). easy.
           apply HH in H5. 2: { rewrite !bpfend_bn. easy. }
           destruct H5 as [H5 | H5].
           admit.
           destruct H5 as (b3,(w3,(s3,(Ha,(Hb,(Hc,Hd)))))).
           apply pneqq7 in Hd; try easy.
           destruct Hd as (b2,(Hd,(He,Hf))).
           subst.
           assert((q2 ! [|(l2, s2, merge_bpf_cont b2 (q ! [|(l, s3, w3)|]))|]) =
                  (merge_bpf_cont (bpf_send q2 l2 s2 b2) (q ! [|(l, s3, w3)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q2 l2 s2 b2) (q ! [|(l, s3, w3)|]))). simpl. easy. }
           rewrite H5 in H0.
           specialize (drop_send bpf_end (bpf_send q2 l2 s2 b2) q l s s3 w'0 w3); intro HD.
           rewrite !bpfend_bn in HD.
           apply HD in H0; try easy.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a, (b4,(w4,(H4b,(H4c,H4d))))).
           subst.
           specialize(Invert_Bpf_Bpf b4 (bpf_send q1 l2 s2 b2) q1 l1 s1 w4 w3 H4c); intros HH2.
           pose proof H0 as H00.
           apply HH2 in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (a1,(a2,(s',(H0a,(H0b,H0c))))).
           assert(a1 = bpf_end) by admit.
           subst. simpl in H0c.
           inversion H0c. subst.
           pfold. constructor. easy. 
           right.
           rewrite(st_eq(merge_bpf_cont (bpf_send q1 l1 s' a2) w3)) in H00. simpl in H00.
           specialize (drop_send b4 bpf_end q1 l1 s1 s' w4 ( merge_bpf_cont a2 w3)); intro HD2.
           rewrite !bpfend_bn in HD2.
           apply HD2 in H00; try easy.
           apply CIH with (p := q1) (w' := (merge_bpf_cont a2 w3)) (w :=  (merge_bpf_cont b4 w4)).
           admit. admit. admit. admit. easy.
           apply proj_send_b; try easy.
           apply prof_send_drop_snd in H8. easy. admit. easy.
           destruct H0 as (a1,(a2,(s',(H0a,(H0b,(H0c,H0d)))))).
           simpl in H0c. rewrite String.eqb_refl in H0c. easy.
           apply extsR in Pw. easy.
           
           subst.
           specialize(Invert_Bpf_Bpf bpf_end bpf_end q l s w'0 (q0 ! [|(l0, s0, w'1)|])); intros HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           admit.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           case_eq(String.eqb q0 q); intros.
           rewrite String.eqb_eq in H0. subst.
(*            pinversion H00. subst. *)
           assert(b3 = bpf_end) by admit.
           subst. rewrite bpfend_bn in H0d.
           inversion H0d. subst.
           apply prj_send_inv2 in H7.
           destruct H7 as (H7a,(b5,(w5,(H7b,(H7c,H7d))))).
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           specialize (drop_send bpf_end bpf_end q l s s3 (merge_bpf_cont b6 (q2 ! [|(l1, s1, w6)|])) (merge_bpf_cont b5 (q2 ! [|(l2, s2, w5)|]))); intro HD2.
           rewrite !bpfend_bn in HD2.
           apply HD2 in H00; try easy.
           pose proof H00 as H000.
           apply send_inv_leq in H00.
           destruct H00. subst.
           pfold. constructor. easy.
           specialize (drop_send b6 b5 q2 l2 s1 s2 w6 w5 H4c H7c); intro HD3.
           apply HD3 in H000; try easy.
           right.
           apply CIH with (p := q2) (w' := (merge_bpf_cont b5 w5)) (w := (merge_bpf_cont b6 w6)).
           easy. easy. admit. admit. easy.
           apply proj_send_b. easy. easy.
           apply proj_send_b. easy. easy.
           easy. easy. admit. admit.
           rewrite String.eqb_neq in H0.
           apply pneqq7 in H0d; try easy.
           apply prj_send_inv2 in H7.
           destruct H7 as (H7a,(b5,(w5,(H7b,(H7c,H7d))))).
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q2 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q2 ! [|(l1, s1, w6)|]))) by admit.
           rewrite H4 in H00.
           assert((q0 ! [|(l0, s0, merge_bpf_cont b5 (q2 ! [|(l2, s2, w5)|]))|]) =
                  (merge_bpf_cont (bpf_send q0 l0 s0 b5) (q2 ! [|(l2, s2, w5)|]))) by admit.
           rewrite H7 in H00.
           pose proof H00 as H000.
           apply send_inv_leq in H00. destruct H00. subst.
           pfold. constructor. easy.
           right.
           specialize (drop_send (bpf_send q l s b6) (bpf_send q0 l0 s0 b5) q2 l2 s1 s2 w6 w5); intro HD2.
           apply HD2 in H000.
           rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) w6)) in H000.
           rewrite(st_eq(merge_bpf_cont (bpf_send q0 l0 s0 b5) w5)) in H000. simpl in H000.
           apply CIH with (p := q2) (w' := (q0 ! [|(l0, s0, merge_bpf_cont b5 w5)|])) (w := (q ! [|(l, s, merge_bpf_cont b6 w6)|])).
           easy. easy. admit. admit. easy.
           apply proj_send_bs. easy. easy. easy.
           apply proj_send_bs. easy. easy. easy. simpl. admit.
           simpl. admit. simpl. admit. simpl. admit.
           admit. admit. easy.
           
           subst.
           admit.
           apply mon_projs.
           (*third inversion on H2 starts here*)
           subst.
Admitted.


