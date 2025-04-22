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
  | pjr_rcvI: forall q l s w' p w, p <> q -> coseqIn (p, rcv) (act w') -> R w' p w -> projR R (st_receive q [|(l,s,w')|]) p w
  | pjr_rcvN: forall q l s w' p, p <> q -> (coseqIn (p, rcv) (act w') -> False) -> projR R (st_receive q [|(l,s,w')|]) p st_end
  | pjr_sndI: forall q l s w' p w, coseqIn (p, rcv) (act w') -> R w' p w -> projR R (st_send q [|(l,s,w')|]) p w
  | pjr_sndN: forall q l s w' p, (coseqIn (p, rcv) (act w') -> False) -> projR R (st_send q [|(l,s,w')|]) p st_end.

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

Lemma projSC_nmem: forall w p, ~coseqIn (p, snd) (act (@und w)) -> projSC (@und w) p st_end.
Proof. intros (w, Pw) p Ha.
       generalize dependent w.
       revert p.
       pcofix CIH. simpl.
       intros.
       specialize(sinv w Pw); intros Hpw.
       destruct Hpw as [Hpw | [Hpw | Hpw]].
       + destruct Hpw as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         subst.
         pfold. apply pjs_sndN.
         intro HH. apply Ha.
         subst. 
         rewrite(coseq_eq(act (q1 ! [|(l1, s1, wa)|]))). simpl.
         apply CoInSplit1 with (y := (q1, snd)) (ys := (act wa)). easy. easy. 
         intro HH.
         apply Ha. 
         rewrite(coseq_eq(act (q1 ! [|(l1, s1, wa)|]))). simpl.
         case_eq(String.eqb p q1); intros.
         ++ rewrite String.eqb_eq in H. subst.
            apply CoInSplit1 with (y := (q1, snd)) (ys := (act wa)). easy. easy.
         ++ rewrite String.eqb_neq in H.
            apply CoInSplit2 with (y := (q1, snd)) (ys := (act wa)). easy. intro HHa. apply H. inversion HHa. easy.
            easy.
       + destruct Hpw as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         subst.
         pfold. apply pjs_rcvN.
         intro HH.
         apply Ha.
         rewrite(coseq_eq(act (q1 & [|(l1, s1, wa)|]))). simpl.
         apply CoInSplit2 with (y := (q1, rcv)) (ys := (act wa)). easy. easy. easy.
       + subst. pfold. constructor.
Qed.

Lemma projRC_nmem: forall w p, ~coseqIn (p, rcv) (act (@und w)) -> projRC (@und w) p st_end.
Proof. intros (w, Pw) p Ha.
       generalize dependent w.
       revert p.
       pcofix CIH. simpl.
       intros.
       specialize(sinv w Pw); intros Hpw.
       destruct Hpw as [Hpw | [Hpw | Hpw]].
       + destruct Hpw as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         subst.
         pfold. apply pjr_sndN.
         intro HH. apply Ha.
         subst. 
         rewrite(coseq_eq(act (q1 ! [|(l1, s1, wa)|]))). simpl.
         apply CoInSplit2 with (y := (q1, snd)) (ys := (act wa)). easy. easy. easy.
       + destruct Hpw as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         subst.
         pfold. apply pjr_rcvN.
         intro HH.
         apply Ha. subst. 
         rewrite(coseq_eq(act (q1 & [|(l1, s1, wa)|]))). simpl.
         apply CoInSplit1 with (y := (q1, rcv)) (ys := (act wa)). easy. easy.
         intro HH. apply Ha.
         rewrite(coseq_eq(act (q1 & [|(l1, s1, wa)|]))). simpl.
         case_eq(String.eqb p q1); intros.
         ++ rewrite String.eqb_eq in H. subst.
            apply CoInSplit1 with (y := (q1, rcv)) (ys := (act wa)). easy. easy.
         ++ rewrite String.eqb_neq in H.
            apply CoInSplit2 with (y := (q1, rcv)) (ys := (act wa)). easy. intro HHa. apply H. inversion HHa. easy.
            easy.
       + subst. pfold. constructor.
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

Lemma prj_recv_inv1c: forall c p q l1 s1 w1 l2 s2 w2,
  isInC c p = false ->
  projRC (merge_cpf_cont c (p & [|(l1, s1, w1)|])) p (q & [|(l2, s2, w2)|]) ->
  p = q /\ l1 = l2 /\ s1 = s2 /\ projRC w1 p w2.
Proof. intro c.
       induction c; intros.
       - rewrite(st_eq (merge_cpf_cont (cpf_receive s s0 s1 c) (p & [|(l1, s2, w1)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         simpl in H. rewrite String.eqb_refl in H. easy.
         subst.
         apply IHc. 2:{ easy. }
         simpl in H. rewrite orbtf in H. easy.
         apply mon_projr.
       - rewrite(st_eq (merge_cpf_cont (cpf_send s s0 s1 c) (p & [|(l1, s2, w1)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         simpl in H. 
         apply IHc; easy.
         apply mon_projr.
       - rewrite cpfend_cn in H0.
         pinversion H0. subst. easy.
         subst. easy.
         apply mon_projr.
Qed.

Lemma prj_recv_inv1: forall a p q l1 s1 w1 l2 s2 w2,
  isInA a p = false ->
  projRC (merge_apf_cont a (p & [|(l1, s1, w1)|])) p (q & [|(l2, s2, w2)|]) ->
  p = q /\ l1 = l2 /\ s1 = s2 /\ projRC w1 p w2.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         pinversion H0.
         subst. easy.
         subst. easy.
         apply mon_projr.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [|(l1, s2, w1)|]))) in H0. 
         simpl in H0.
         pinversion H0.
         subst. simpl in H. rewrite String.eqb_refl in H. simpl in H. easy.
         subst.
         apply IHa. 2:{ easy. }
         simpl in H. rewrite orbtf in H. easy.
         apply mon_projr.
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

Lemma proj_recv_a: forall a p w wb,
  isInA a p = false ->
  projRC w p wb ->
  projRC (merge_apf_cont a w) p wb.
Proof. intros.
       pinversion H0.
       - subst.
         induction a; intros.
         + rewrite apfend_an. pfold. constructor.
         + simpl in H.
           rewrite(st_eq (merge_apf_cont (apf_receive s s0 s1 a) (end)) ). simpl.
           pfold. apply pjr_rcvN. rewrite orbtf in H. 
           destruct H as (Ha, Hb).
           apply String.eqb_neq in Ha. easy.
           intro HH.
           rewrite <- inA_coseq in HH.
           rewrite orbtf in H.
           destruct H as (Ha, Hb).
           destruct HH as [HH | HH].
           ++ rewrite HH in Hb. easy.
           ++ rewrite(coseq_eq(act (end))) in HH. simpl in HH.
              inversion HH. subst. easy.
              subst. easy.
       - subst.
         induction a; intros.
         + rewrite apfend_an. pfold. constructor. left. easy.
         + rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a) (p & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H. 
           destruct H as (Ha,Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvI. easy. 
           rewrite <- inA_coseq. right.
           rewrite(coseq_eq(act (p & [|(l, s, w')|]))). simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
           left. apply IHa; easy.
       - subst.
         induction a; intros.
         + rewrite apfend_an. pfold. constructor. easy. easy. left. easy.
         + rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a) (q & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H. 
           destruct H as (Ha,Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvI. easy. 
           rewrite <- inA_coseq. right.
           rewrite(coseq_eq(act (q & [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. intro HH. apply H1. inversion HH. easy.
           easy.
           left. apply IHa; easy.
       - subst. 
         induction a; intros.
         + rewrite apfend_an. pfold. apply pjr_rcvN. easy. easy.
         + rewrite(st_eq (merge_apf_cont (apf_receive s0 s1 s2 a) (q & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H. 
           destruct H as (Ha,Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvN. easy. intro HH.
           apply H2.
           rewrite <- inA_coseq in HH.
           destruct HH as [HH | HH].
           ++ rewrite HH in Hb. easy.
           ++ rewrite(coseq_eq(act (q & [|(l, s, w')|]))) in HH. simpl in HH.
              inversion HH. subst. inversion H. subst. easy.
              subst. inversion H. subst. easy.
       - subst.
         induction a; intros.
         + rewrite apfend_an. pfold. apply pjr_sndI. easy. left. easy.
         + rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a) (q ! [|(l, s, w')|])) ). simpl.
           simpl in H. rewrite orbtf in H. 
           destruct H as (Ha,Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvI. easy.
           rewrite <- inA_coseq. right. 
           rewrite(coseq_eq(act (q ! [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. easy. easy.
           left. apply IHa; easy.
       - subst.
         induction a; intros.
         + rewrite apfend_an. pfold. apply pjr_sndN. easy.
         + rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a) (q ! [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H. 
           destruct H as (Ha,Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvN. easy.
           intro HH. apply H1.
           rewrite <- inA_coseq in HH.
           destruct HH as [HH | HH].
           ++ rewrite HH in Hb. easy.
           ++ rewrite(coseq_eq(act (q ! [|(l, s, w')|]))) in HH. simpl in HH.
              inversion HH. subst. inversion H. subst. inversion H. subst. easy.
       apply mon_projr.
Qed.

Lemma proj_recv_c: forall c p w wb,
  isInC c p = false ->
  projRC w p wb ->
  projRC (merge_cpf_cont c w) p wb.
Proof. intros.
       pinversion H0.
       - subst.
         induction c; intros.
         + rewrite(st_eq (merge_cpf_cont (cpf_receive s s0 s1 c) (end))). simpl.
           simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvN. easy.
           intro HH.
           rewrite <- inC_coseq in HH.
           destruct HH as [HH | HH].
           ++ rewrite Hb in HH. easy.
           ++ rewrite(coseq_eq (act (end))) in HH. simpl in HH. inversion HH. easy. easy.
         + rewrite(st_eq(merge_cpf_cont (cpf_send s s0 s1 c) (end))). simpl.
           simpl in H. 
           pfold. apply pjr_sndN.
           intro HH.
           rewrite <- inC_coseq in HH.
           destruct HH as [HH | HH].
           ++ rewrite H in HH. easy.
           ++ rewrite(coseq_eq (act (end))) in HH. simpl in HH. inversion HH. easy. easy.
         + rewrite cpfend_cn. pfold. constructor.
       - subst.
         induction c; intros.
         + rewrite(st_eq(merge_cpf_cont (cpf_receive s0 s1 s2 c) (p & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvI. easy.
           rewrite <- inC_coseq.
           right.
           rewrite(coseq_eq (act (p & [|(l, s, w')|]))). simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
           left. apply IHc. easy.
         + rewrite(st_eq(merge_cpf_cont (cpf_send s0 s1 s2 c) (p & [|(l, s, w')|]))). simpl.
           simpl in H.
           pfold. apply pjr_sndI.
           rewrite <- inC_coseq.
           right.
           rewrite(coseq_eq (act (p & [|(l, s, w')|]))). simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
           left. apply IHc. easy.
         + rewrite cpfend_cn. pfold. constructor. left. easy.
       - subst.
         induction c; intros.
         + rewrite(st_eq (merge_cpf_cont (cpf_receive s0 s1 s2 c) (q & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvI. easy.
           rewrite <- inC_coseq. 
           right.
           rewrite(coseq_eq (act (q & [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. intro HH. apply H1. inversion HH. easy. easy.
           left. apply IHc. easy.
         + rewrite(st_eq (merge_cpf_cont (cpf_send s0 s1 s2 c) (q & [|(l, s, w')|]))). simpl.
           simpl in H.
           pfold. apply pjr_sndI.
           rewrite <- inC_coseq.
           right.
           rewrite(coseq_eq (act (q & [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. intro HH. apply H1. inversion HH. easy. easy.
           left. apply IHc. easy.
         + rewrite cpfend_cn.
           pfold. easy.
       - subst.
         induction c; intros.
         + rewrite(st_eq(merge_cpf_cont (cpf_receive s0 s1 s2 c) (q & [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvN. easy.
           rewrite <- inC_coseq.
           intro HH.
           destruct HH as [HH | HH].
           ++ rewrite Hb in HH. easy.
           ++ apply H2. 
              rewrite(coseq_eq(act (q & [|(l, s, w')|]))) in HH. simpl in HH.
              inversion HH. subst. inversion H. subst. easy. subst. inversion H. subst. easy.
         + rewrite(st_eq(merge_cpf_cont (cpf_send s0 s1 s2 c) (q & [|(l, s, w')|]))). simpl.
           simpl in H.
           pfold. apply pjr_sndN.
           rewrite <- inC_coseq.
           intro HH.
           destruct HH as [HH | HH].
           ++ rewrite H in HH. easy.
           ++ apply H2. 
              rewrite(coseq_eq(act (q & [|(l, s, w')|]))) in HH. simpl in HH.
              inversion HH. subst. inversion H3. subst. easy.              
              subst. inversion H3. subst. easy.
          + rewrite cpfend_cn.
            pfold. apply pjr_rcvN. easy. easy.
       - subst.
         induction c; intros.
         + rewrite(st_eq(merge_cpf_cont (cpf_receive s0 s1 s2 c) (q ! [|(l, s, w')|])) ). simpl.
           simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvI. easy.
           rewrite <- inC_coseq.
           right.
           rewrite(coseq_eq (act (q ! [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. easy. easy.
           left. apply IHc. easy.
         + rewrite(st_eq(merge_cpf_cont (cpf_send s0 s1 s2 c) (q ! [|(l, s, w')|]))). simpl.
           simpl in H.
           pfold. apply pjr_sndI.
           rewrite <- inC_coseq.
           right.
           rewrite(coseq_eq (act (q ! [|(l, s, w')|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. easy. easy.
           left. apply IHc. easy.
         + rewrite cpfend_cn. pfold. easy.
       - subst. 
         induction c; intros.
         + rewrite(st_eq(merge_cpf_cont (cpf_receive s0 s1 s2 c) (q ! [|(l, s, w')|]))). simpl.
           simpl in H. rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite String.eqb_neq in Ha.
           pfold. apply pjr_rcvN. easy.
           rewrite <- inC_coseq.
           intro HH.
           destruct HH as [HH | HH].
           ++ rewrite Hb in HH. easy.
           ++ apply H1. 
              rewrite(coseq_eq(act (q ! [|(l, s, w')|]))) in HH. simpl in HH.
              inversion HH. subst. inversion H. subst. inversion H. subst. easy.
         + rewrite(st_eq(merge_cpf_cont (cpf_send s0 s1 s2 c) (q ! [|(l, s, w')|]))). simpl.
           simpl in H.
           pfold. apply pjr_sndN.
           rewrite <- inC_coseq.
           intro HH.
           destruct HH as [HH | HH].
           ++ rewrite H in HH. easy.
           ++ apply H1. 
              rewrite(coseq_eq(act (q ! [|(l, s, w')|]))) in HH. simpl in HH.
              inversion HH. subst. inversion H. subst. inversion H. easy. subst. inversion H2. subst. easy.
         + rewrite cpfend_cn. pfold. easy.
       apply mon_projr.
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
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         rewrite(coseq_eq(act (end))) in HH. simpl in HH.
         inversion HH. subst. easy. subst. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inB_coseq. right.
         rewrite(coseq_eq(act (p ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w')). easy. easy.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inB_coseq. right.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, snd)) (ys := (act w')). easy.
         intro HH. apply H2. inversion HH. easy. easy.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_sndN. easy.
         intro HH. rewrite <- inB_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         apply H3.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))) in HH. simpl in HH.
         inversion HH. subst.
         inversion H4. subst. easy.
         subst. inversion H4. subst. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inB_coseq. right.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w')). easy. easy. easy.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_sndN. easy.
         intro HH. rewrite <- inB_coseq in HH.
         apply H2.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))) in HH.
         simpl in HH. 
         inversion HH. subst. inversion H3.
         subst. inversion H3. subst. easy.
       apply mon_projs.
Qed.

Lemma proj_recv_ar: forall a p q l s w wb,
  p <> q ->
  isInA a p = false ->
  projRC w p wb ->
  projRC (q & [|(l, s, merge_apf_cont a w)|]) p wb.
Proof. intros.
       pinversion H1.
       - subst. pfold. apply pjr_rcvN. easy.
         intros HH. rewrite <- inA_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         rewrite(coseq_eq(act (end))) in HH. simpl in HH.
         inversion HH. subst. easy. subst. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inA_coseq. right.
         rewrite(coseq_eq(act (p & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
         left. apply proj_recv_a. easy.
         pfold. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inA_coseq. right.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w')). easy.
         intro HH. apply H2. inversion HH. easy. easy.
         left. apply proj_recv_a. easy.
         pfold. easy.
       - subst. pfold. apply pjr_rcvN. easy.
         intro HH. rewrite <- inA_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         apply H3.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))) in HH. simpl in HH.
         inversion HH. subst.
         inversion H4. subst. easy.
         subst. inversion H4. subst. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inA_coseq. right.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, snd)) (ys := (act w')). easy. easy. easy.
         left. apply proj_recv_a. easy.
         pfold. easy.
       - subst. pfold. apply pjr_rcvN. easy.
         intro HH. rewrite <- inA_coseq in HH.
         apply H2.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))) in HH.
         simpl in HH. 
         inversion HH. subst. inversion H3.
         subst. inversion H3. subst. easy.
       apply mon_projr.
Qed.

Lemma proj_recv_cr: forall a p q l s w wb,
  p <> q ->
  isInC a p = false ->
  projRC w p wb ->
  projRC (q & [|(l, s, merge_cpf_cont a w)|]) p wb.
Proof. intros.
       pinversion H1.
       - subst. pfold. apply pjr_rcvN. easy.
         intros HH. rewrite <- inC_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         rewrite(coseq_eq(act (end))) in HH. simpl in HH.
         inversion HH. subst. easy. subst. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inC_coseq. right.
         rewrite(coseq_eq(act (p & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
         left. apply proj_recv_c. easy.
         pfold. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inC_coseq. right.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w')). easy.
         intro HH. apply H2. inversion HH. easy. easy.
         left. apply proj_recv_c. easy.
         pfold. easy.
       - subst. pfold. apply pjr_rcvN. easy.
         intro HH. rewrite <- inC_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         apply H3.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))) in HH. simpl in HH.
         inversion HH. subst.
         inversion H4. subst. easy.
         subst. inversion H4. subst. easy.
       - subst. pfold. constructor. easy.
         rewrite <- inC_coseq. right.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, snd)) (ys := (act w')). easy. easy. easy.
         left. apply proj_recv_c. easy.
         pfold. easy.
       - subst. pfold. apply pjr_rcvN. easy.
         intro HH. rewrite <- inC_coseq in HH.
         apply H2.
         destruct HH as [HH | HH].
         rewrite H0 in HH. easy.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))) in HH.
         simpl in HH. 
         inversion HH. subst. inversion H3.
         subst. inversion H3. subst. easy.
       apply mon_projr.
Qed.

Lemma proj_send_br: forall b p q l s w wb,
  isInB b p = false ->
  projSC w p wb ->
  projSC (q & [|(l, s, merge_bpf_cont b w)|]) p wb.
Proof. intros.
       pinversion H0.
       - subst. pfold. apply pjs_rcvN. 
         intro HH. rewrite <- inB_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         rewrite(coseq_eq(act (end))) in HH. simpl in HH.
         inversion HH. subst. easy. subst. easy.
       - subst. pfold. constructor.
         rewrite <- inB_coseq. right.
         rewrite(coseq_eq(act (p ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w')). easy. easy.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. constructor.
         rewrite <- inB_coseq. right.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, snd)) (ys := (act w')). easy.
         intro HH. apply H1. inversion HH. easy. easy.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_rcvN.
         intro HH. rewrite <- inB_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         apply H2.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))) in HH. simpl in HH.
         inversion HH. subst. inversion H3. subst. easy.
         subst. inversion H3. subst. easy.
       - subst. pfold. constructor.
         rewrite <- inB_coseq. right.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w')). easy. easy. easy.
         left. apply proj_send_b. easy.
         pfold. easy.
       - subst. pfold. apply pjs_rcvN.
         intro HH. rewrite <- inB_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))) in HH.
         simpl in HH. 
         inversion HH. subst. inversion H2.
         subst. inversion H2. subst. easy.
       apply mon_projs.
Qed.

Lemma proj_recv_as: forall a p q l s w wb,
  isInA a p = false ->
  projRC w p wb ->
  projRC (q ! [|(l, s, merge_apf_cont a w)|]) p wb.
Proof. intros.
       pinversion H0.
       - subst. pfold. apply pjr_sndN. 
         intro HH. rewrite <- inA_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         rewrite(coseq_eq(act (end))) in HH. simpl in HH.
         inversion HH. subst. easy. subst. easy.
       - subst. pfold. constructor.
         rewrite <- inA_coseq. right.
         rewrite(coseq_eq(act (p & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
         left. apply proj_recv_a. easy.
         pfold. easy.
       - subst. pfold. constructor.
         rewrite <- inA_coseq. right.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w')). easy.
         intro HH. apply H1. inversion HH. easy. easy.
         left. apply proj_recv_a. easy.
         pfold. easy.
       - subst. pfold. apply pjr_sndN.
         intro HH. rewrite <- inA_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         apply H2.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))) in HH. simpl in HH.
         inversion HH. subst. inversion H3. subst. easy.
         subst. inversion H3. subst. easy.
       - subst. pfold. constructor.
         rewrite <- inA_coseq. right.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, snd)) (ys := (act w')). easy. easy. easy.
         left. apply proj_recv_a. easy.
         pfold. easy.
       - subst. pfold. apply pjr_sndN.
         intro HH. rewrite <- inA_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))) in HH.
         simpl in HH. 
         inversion HH. subst. inversion H2.
         subst. inversion H2. subst. easy.
       apply mon_projr.
Qed.

Lemma proj_send_cr: forall a p q l s w wb,
  isInC a p = false ->
  projRC w p wb ->
  projRC (q ! [|(l, s, merge_cpf_cont a w)|]) p wb.
Proof. intros.
       pinversion H0.
       - subst. pfold. apply pjr_sndN. 
         intro HH. rewrite <- inC_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         rewrite(coseq_eq(act (end))) in HH. simpl in HH.
         inversion HH. subst. easy. subst. easy.
       - subst. pfold. constructor.
         rewrite <- inC_coseq. right.
         rewrite(coseq_eq(act (p & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
         left. apply proj_recv_c. easy.
         pfold. easy.
       - subst. pfold. constructor.
         rewrite <- inC_coseq. right.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w')). easy.
         intro HH. apply H1. inversion HH. easy. easy.
         left. apply proj_recv_c. easy.
         pfold. easy.
       - subst. pfold. apply pjr_sndN.
         intro HH. rewrite <- inC_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         apply H2.
         rewrite(coseq_eq(act (q0 & [|(l0, s0, w')|]))) in HH. simpl in HH.
         inversion HH. subst. inversion H3. subst. easy.
         subst. inversion H3. subst. easy.
       - subst. pfold. constructor.
         rewrite <- inC_coseq. right.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))). simpl.
         apply CoInSplit2 with (y := (q0, snd)) (ys := (act w')). easy. easy. easy.
         left. apply proj_recv_c. easy.
         pfold. easy.
       - subst. pfold. apply pjr_sndN.
         intro HH. rewrite <- inC_coseq in HH.
         destruct HH as [HH | HH].
         rewrite H in HH. easy.
         rewrite(coseq_eq(act (q0 ! [|(l0, s0, w')|]))) in HH.
         simpl in HH. 
         inversion HH. subst. inversion H2.
         subst. inversion H2. subst. easy.
       apply mon_projr.
Qed.

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

Lemma prj_recv_eq: forall p q l s w wa,
  singleton w ->
  projRC w p (q & [|(l, s, wa)|]) ->
  p = q.
Proof. intros.
       pinversion H0. 
       - easy.
       - subst.
         apply inReceivefE in H2; try easy.
         destruct H2 as (b1,(l1,(s1,(w1,(H2a,H2b))))).
         subst.
         apply prj_recv_inv1c in H3. easy. easy.
         apply extrR in H. easy.
       - subst. 
         apply inReceivefE in H1; try easy.
         destruct H1 as (b1,(l1,(s1,(w1,(H1a,H1b))))).
         subst.
         apply prj_recv_inv1c in H2. easy. easy.
         apply extsR in H. easy.
       apply mon_projr.
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

Lemma prj_recv_inv2c: forall p q l s w wa,
  singleton w ->
  projRC w p (q & [|(l, s, wa)|]) ->
  p = q /\ exists c wb, w = (merge_cpf_cont c (q & [|(l, s, wb)|])) /\ isInC c q = false /\ projRC wb p wa.
Proof. intros.
       specialize(prj_recv_eq p q l s w wa H H0); intro Heq.
       subst. split. easy.
       pinversion H0.
       - subst. exists cpf_end. exists w'. rewrite cpfend_cn. easy.
       - subst.
         apply inReceivefE in H2; try easy.
         destruct H2 as (b1,(l1,(s1,(w1,(H2a,H2b))))).
         rewrite H2a in H3.
         apply prj_recv_inv1c in H3.
         destruct H3 as (H3a,(H3b,(H3c,H3d))).
         exists (cpf_receive q0 l0 s0 b1). exists w1.
         rewrite(st_eq(merge_cpf_cont (cpf_receive q0 l0 s0 b1) (q & [|(l, s, w1)|]))). simpl.
         split. subst. easy. rewrite H2b. apply String.eqb_neq in H1. rewrite H1. easy. easy.
         apply extrR in H. easy.
       - subst.
         apply inReceivefE in H1; try easy.
         destruct H1 as (b1,(l1,(s1,(w1,(H1a,H1b))))).
         subst.
         apply prj_recv_inv1c in H2.
         destruct H2 as (H2a,(H2b,(H2c,H2d))).
         subst.
         exists (cpf_send q0 l0 s0 b1). exists w1.
         rewrite(st_eq(merge_cpf_cont (cpf_send q0 l0 s0 b1) (q & [|(l, s, w1)|]) )). simpl.
         split. easy. easy.
         apply extsR in H. easy.
         apply extsR in H. easy.
       apply mon_projr.
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

Lemma prof_recv_drop_recv: forall a p q l s w wb (Hs: singleton w),
  p <> q ->
  projRC (merge_apf_cont a (p & [|(l, s, w)|])) q wb ->
  projRC (merge_apf_cont a w) q wb.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         rewrite apfend_an.
         pinversion H0.
         subst. easy.
         subst. easy.
         specialize(sinv w Hs); intros Hpw.
         destruct Hpw as [Hpw | [Hpw | Hpw]].
         + destruct Hpw as (p1,(l1,(s1,(w1,(Ha,Hb))))).
           subst. pfold. apply pjr_sndN.
           intro HH. subst. apply H8.
           rewrite(coseq_eq(act (p1 ! [|(l1, s1, w1)|]))). simpl.
           apply CoInSplit2 with (y := (p1, snd)) (ys := (act w1)). easy. easy. easy.
         + destruct Hpw as (p1,(l1,(s1,(w1,(Ha,Hb))))).
           subst. subst. pfold. apply pjr_rcvN.
           intro HH.
           apply H8. subst.
           rewrite(coseq_eq (act (p1 & [|(l1, s1, w1)|]))). simpl.
           apply CoInSplit1 with (y := (p1, rcv)) (ys := (act w1)). easy. easy.
           intro HH. apply H8.
           case_eq(String.eqb q p1); intros.
           ++ rewrite String.eqb_eq in H1. subst.
              rewrite(coseq_eq (act (p1 & [|(l1, s1, w1)|]))). simpl.
              apply CoInSplit1 with (y := (p1, rcv)) (ys := (act w1)). easy. easy.
           ++ rewrite String.eqb_neq in H1. subst.
              rewrite(coseq_eq (act (p1 & [|(l1, s1, w1)|]))). simpl.
              apply CoInSplit2 with (y := (p1, rcv)) (ys := (act w1)). easy. intro HH2. apply H1. inversion HH2. easy.
              easy.
         + subst. pfold. constructor. 
        apply mon_projr.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w) ). simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst. pfold. constructor. left. apply IHa with (p := p) (l := l) (s := s2); try easy.
         subst. pfold. constructor. easy.
         rewrite <- inA_coseq. rewrite <- inA_coseq in H8.
         destruct H8 as [H8 | H8].
         + left. easy.
         + right. rewrite(coseq_eq(act (p & [|(l, s2, w)|]))) in H8. simpl in H8.
           inversion H8. subst. inversion H1. subst. easy.
           subst. inversion H1. subst. easy.
         left. apply IHa with (p := p) (l := l) (s := s2); try easy.
         subst. pfold. apply pjr_rcvN. easy.
         intro HH. apply H8.
         rewrite <- inA_coseq. rewrite <- inA_coseq in HH.
         destruct HH as [HH | HH].
         + left. easy.
         + right. rewrite(coseq_eq(act (p & [|(l, s2, w)|]))). simpl.
           apply CoInSplit2 with (y := (p, rcv)) (ys := (act w)). easy. intro HH2. apply H. inversion HH2. easy.
           easy.
        apply mon_projr.
Qed.

Lemma psend_not_recv: forall b p q l1 s1 w1 l2 s2 w2,
  projSC (merge_bpf_cont b (p ! [|(l1, s1, w1)|])) p (q & [|(l2, s2, w2)|]) -> False.
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [|(l1, s2, w1)|])) ) in H.
         simpl in H.
         pinversion H.
         subst.
         specialize(IHb p q l1 s2 w1 l2 s3 w2).
         apply IHb; easy.
         apply mon_projs.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [|(l1, s2, w1)|]))) in H. 
         simpl in H.
         pinversion H.
         subst.
         specialize(IHb p q l1 s2 w1 l2 s3 w2).
         apply IHb; easy.
         apply mon_projs.
       - rewrite bpfend_bn in H.
         pinversion H. subst.
         easy.
         apply mon_projs.
Qed.

Lemma precv_not_send: forall a p q l1 s1 w1 l2 s2 w2,
  projRC (merge_apf_cont a (p & [|(l1, s1, w1)|])) p (q ! [|(l2, s2, w2)|]) -> False.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H.
         pinversion H. subst. easy.
         apply mon_projr.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [|(l1, s2, w1)|]))) in H.
         simpl in H.
         pinversion H.
         subst.
         specialize(IHa p q l1 s2 w1 l2 s3 w2).
         apply IHa; easy.
         apply mon_projr.
Qed.

Lemma precv_not_sendc: forall c p q l1 s1 w1 l2 s2 w2,
  projRC (merge_cpf_cont c (p & [|(l1, s1, w1)|])) p (q ! [|(l2, s2, w2)|]) -> False.
Proof. intro c.
       induction c; intros.
       - rewrite(st_eq (merge_cpf_cont (cpf_receive s s0 s1 c) (p & [|(l1, s2, w1)|]))) in H. simpl in H.
         pinversion H.
         subst. 
         specialize(IHc p q l1 s2 w1 l2 s3 w2).
         apply IHc; easy.
         apply mon_projr.
       - rewrite(st_eq (merge_cpf_cont (cpf_send s s0 s1 c) (p & [|(l1, s2, w1)|]))) in H. simpl in H.
         pinversion H.
         subst.
         specialize(IHc p q l1 s2 w1 l2 s3 w2).
         apply IHc; easy.
         apply mon_projr.
       - rewrite cpfend_cn in H.
         pinversion H. subst. easy.
         apply mon_projr.
Qed.

Lemma psend_not_end: forall b p l s w,
  projSC (merge_bpf_cont b (p ! [|(l, s, w)|])) p (end) -> False.
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [|(l, s2, w)|]))) in H.
         simpl in H.
         pinversion H.
         subst.
         specialize(IHb p l s2 w).
         apply IHb; easy.
         subst.
         rewrite <- inB_coseq in H5.
         apply H5.
         right. 
         rewrite(coseq_eq(act (p ! [|(l, s2, w)|]))). simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w)). easy. easy.
         apply mon_projs.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [|(l, s2, w)|]))) in H.
         simpl in H.
         pinversion H. subst.
         specialize(IHb p l s2 w).
         apply IHb; easy.
         subst.
         rewrite <- inB_coseq in H6.
         apply H6. 
         right. 
         rewrite(coseq_eq(act (p ! [|(l, s2, w)|]))). simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w)). easy. easy.
         apply mon_projs.
       - rewrite bpfend_bn in H.
         pinversion H. subst. easy.
         subst. easy.
         apply mon_projs.
Qed.

Lemma precv_not_end: forall a p l s w,
  projRC (merge_apf_cont a (p & [|(l, s, w)|])) p (end) -> False.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H.
         pinversion H. subst. easy.
         subst. easy.
         apply mon_projr.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [|(l, s2, w)|]))) in H.
         simpl in H.
         pinversion H.
         subst.
         specialize(IHa p l s2 w).
         apply IHa; easy.
         subst.
         rewrite <- inA_coseq in H6.
         apply H6.
         right. 
         rewrite(coseq_eq(act (p & [|(l, s2, w)|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w)). easy. easy.
         apply mon_projr.
Qed.

Lemma precv_not_end_c: forall a p l s w,
  projRC (merge_cpf_cont a (p & [|(l, s, w)|])) p (end) -> False.
Proof. intro c.
       induction c; intros.
       - rewrite(st_eq(merge_cpf_cont (cpf_receive s s0 s1 c) (p & [|(l, s2, w)|]))) in H. simpl in H.
         pinversion H.
         subst.
         specialize(IHc p l s2 w).
         apply IHc; easy.
         subst.
         rewrite <- inC_coseq in H6.
         apply H6.
         right.
         rewrite(coseq_eq(act (p & [|(l, s2, w)|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w)). easy. easy.
         apply mon_projr.
       - rewrite(st_eq (merge_cpf_cont (cpf_send s s0 s1 c) (p & [|(l, s2, w)|]))) in H. simpl in H.
         pinversion H. subst.
         specialize(IHc p l s2 w).
         apply IHc; easy.
         subst.
         rewrite <- inC_coseq in H5.
         apply H5.
         right. 
         rewrite(coseq_eq(act (p & [|(l, s2, w)|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w)). easy. easy.
         apply mon_projr.
       - rewrite cpfend_cn in H.
         pinversion H. subst. easy.
         subst. easy.
         apply mon_projr.
Qed.

Lemma pjs_notin_end: forall w p w2,
  (coseqIn (p, snd) (act w) -> False) ->
  projSC w p w2 ->
  w2 = st_end.
Proof. intros.
       pinversion H0.
       - subst. easy.
       - subst. destruct H. rewrite(coseq_eq(act (p ! [|(l, s, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w')). easy. easy.
       - subst. destruct H. rewrite(coseq_eq(act (q ! [|(l, s, w')|]))). simpl.
         apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. intro HH. apply H1. inversion HH. easy.
         easy.
       - subst. easy.
       - subst. destruct H. rewrite(coseq_eq(act (q & [|(l, s, w')|]))). simpl.
         apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. easy. easy.
       - easy.
         apply mon_projs.
Qed.

Lemma pjr_notin_end: forall w p w2,
  (coseqIn (p, rcv) (act w) -> False) ->
  projRC w p w2 ->
  w2 = st_end.
Proof. intros.
       pinversion H0.
       - easy.
       - subst. destruct H. rewrite(coseq_eq(act (p & [|(l, s, w')|]))). simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w')). easy. easy.
       - subst. destruct H. rewrite(coseq_eq(act (q & [|(l, s, w')|]))). simpl.
         apply CoInSplit2 with (y := (q, rcv)) (ys := (act w')). easy. intro HH. apply H1. inversion HH. easy.
         easy.
       - easy.
       - subst. destruct H. rewrite(coseq_eq(act (q ! [|(l, s, w')|]))). simpl.
         apply CoInSplit2 with (y := (q, snd)) (ys := (act w')). easy. easy. easy.
       - easy.
         apply mon_projr.
Qed.

Lemma _B_7_1: forall w w' p w1 w2, refinement4 (@und w) (@und w') -> projSC (@und w) p (@und w1) -> projSC (@und w') p (@und w2) -> sRefinement (@und w1) (@und w2).
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
           pinversion H2. subst.
           pose proof H0 as H00.
           specialize(send_inv_leq bpf_end bpf_end q2 l1 s1 w'0 l2 s2 w'1); intros HH.
           rewrite !bpfend_bn in HH.
           apply HH in H0; try easy.
           destruct H0. subst.
           pfold. constructor.
           easy.
           specialize(drop_send bpf_end bpf_end q2 l2 s1 s2 w'0 w'1); intro HH2.
           rewrite !bpfend_bn in HH2. 
           apply HH2 in H00; try easy.
           right.
           apply CIH with (p := q2) (w' := w'1) (w := w'0). easy. easy. 
           apply extsR in Pw'. easy.
           apply extsR in Pw. easy.
           easy. easy. easy.
           subst.
           specialize(Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q ! [|(l, s, w'1)|])); intros HH.
           assert(isInB bpf_end q2 = false). easy.
           apply HH in H6. 2: { rewrite !bpfend_bn. easy. }
           destruct H6 as [H6 | H6].
           destruct H6 as (b1,(b2,(s3,(H6a,(H6b,H6c))))).
           apply end_nmerge in H6c. easy.
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
           easy. easy. 
           rewrite(st_eq((merge_bpf_cont (bpf_send q l s b2) w3))). simpl.
           apply exts. apply extbpf.
           apply extsR in Pw'.
           apply extbpfR in Pw'. apply extsR in Pw'. easy.
           apply extsR in Pw. easy.
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
           easy. easy. 
           
           apply extbpf. apply extrR in Pw'. apply extbpfR in Pw'.
           apply extsR in Pw'. easy.
           apply extsR in Pw. easy.
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
           destruct H5 as (b1,(b2,(s3,(H5a,(H5b,H5c))))).
           apply end_nmerge in H5c. easy.
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
           
           pose proof H0 as H00.
           rewrite(st_eq(merge_bpf_cont (bpf_send q1 l2 s2 b2) w3)) in H0.
           simpl in H0.
           specialize(send_inv_leq b4 bpf_end q1 l1 s1 w4 l2 s2 (merge_bpf_cont b2 w3)); intros HH2.
           rewrite !bpfend_bn in HH2.
           apply HH2 in H0; try easy.
           destruct H0. subst.
           
           pfold. constructor. easy. 
           right.
           rewrite(st_eq(merge_bpf_cont (bpf_send q1 l2 s2 b2) w3)) in H00. simpl in H00.
           specialize (drop_send b4 bpf_end q1 l2 s1 s2 w4 ( merge_bpf_cont b2 w3)); intro HD2.
           rewrite !bpfend_bn in HD2.
           apply HD2 in H00; try easy.
           apply CIH with (p := q1) (w' := (merge_bpf_cont b2 w3)) (w :=  (merge_bpf_cont b4 w4)).
           easy. easy. 
           apply extbpf. apply extsR in Pw'. apply extbpfR in Pw'.
           apply extsR in Pw'. easy.
           apply extsR in Pw. apply extbpfR in Pw. apply extsR in Pw.
           apply extbpf. easy. easy.
           apply proj_send_b; try easy.
           apply prof_send_drop_snd in H8. easy.
           apply extsR, extbpfR, extsR in Pw'. easy. easy.
           apply extsR in Pw. easy.
           
           subst.
           specialize(Invert_Bpf_Bpf bpf_end bpf_end q l s w'0 (q0 ! [|(l0, s0, w'1)|])); intros HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.

           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           case_eq(String.eqb q0 q); intros.
           rewrite String.eqb_eq in H0. subst.
           assert(b3 = bpf_end).
           { apply noPreS in H0d. easy. easy. }
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
           easy. easy.
           apply extsR, extbpfR, extsR in Pw'.
           apply extbpf. easy.
           apply extsR, extbpfR, extsR in Pw.
           apply extbpf. easy. easy.
           apply proj_send_b. easy. easy.
           apply proj_send_b. easy. easy.
           easy. easy.
           apply extsR in Pw. easy.
           apply extsR in Pw'. easy.
           rewrite String.eqb_neq in H0.
           apply pneqq7 in H0d; try easy.
           apply prj_send_inv2 in H7.
           destruct H7 as (H7a,(b5,(w5,(H7b,(H7c,H7d))))).
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q2 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q2 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q2 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H00.
           assert((q0 ! [|(l0, s0, merge_bpf_cont b5 (q2 ! [|(l2, s2, w5)|]))|]) =
                  (merge_bpf_cont (bpf_send q0 l0 s0 b5) (q2 ! [|(l2, s2, w5)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q0 l0 s0 b5) (q2 ! [|(l2, s2, w5)|]))). simpl. easy. }
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
           easy. easy.
           apply extsR, extbpfR, extsR in Pw'.
           apply exts, extbpf. easy.
           apply extsR, extbpfR, extsR in Pw.
           apply exts, extbpf. easy. easy.
           apply proj_send_bs. easy. easy. easy.
           apply proj_send_bs. easy. easy. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           simpl.
           apply String.eqb_neq in H5. rewrite H5. rewrite H7c. easy.
           simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           simpl.
           apply String.eqb_neq in H5. rewrite H5. rewrite H7c. easy.
           apply extsR in Pw. easy.
           apply extsR in Pw'. easy. easy.

           subst.
           apply prj_send_inv2 in H6.
           destruct H6 as (H6a,(b5,(w5,(H6b,(H6c,H6d))))).
           subst.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           pose proof H0 as H00.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           assert((q0 & [|(l0, s0, merge_bpf_cont b5 (q1 ! [|(l2, s2, w5)|]))|]) =
                  (merge_bpf_cont (bpf_receive q0 l0 s0 b5) (q1 ! [|(l2, s2, w5)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q0 l0 s0 b5) (q1 ! [|(l2, s2, w5)|]))). simpl. easy. }
           rewrite H6 in H0.
           apply send_inv_leq in H0.
           destruct H0 as (H0a,H0b).
           subst.
           pfold. constructor. easy.
           right.
           rewrite H4 in H00. rewrite H6 in H00.
           apply drop_send in H00.
           rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) w6)) in H00.
           rewrite(st_eq (merge_bpf_cont (bpf_receive q0 l0 s0 b5) w5)) in H00. simpl in H00.
           apply CIH with (p := q1) (w' := (q0 & [|(l0, s0, merge_bpf_cont b5 w5)|])) (w :=(q ! [|(l, s, merge_bpf_cont b6 w6)|])).
           easy. easy.
           apply extrR, extbpfR, extsR in Pw'. 
           apply extr, extbpf. easy.
           apply extsR, extbpfR, extsR in Pw.
           apply exts, extbpf. easy. easy.
           apply proj_send_bs. easy. easy. easy.
           apply proj_send_br. easy. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           simpl. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           simpl. easy.
           apply extsR in Pw. easy.
           apply extrR in Pw'. easy.
           apply mon_projs.
           (*third inversion on H2 starts here*)
           subst.
           pinversion H2.
           subst.
           apply rcv_snd_notRef in H0.
           easy.
           subst.
           apply rcv_snd_notRef in H0.
           easy.
           subst.
           apply prj_send_inv2 in H5.
           destruct H5 as (H5a,(b5,(w5,(H5b,(H5c,H5d))))).
           subst.
           apply prj_send_inv2 in H3.
           destruct H3 as (H3a,(b3,(w3,(H3b,(H3c,H3d))))).
           subst.
           pose proof H0 as H00.
           assert((q & [|(l, s, merge_bpf_cont b3 (q1 ! [|(l1, s1, w3)|]))|]) =
                  (merge_bpf_cont (bpf_receive q l s b3) (q1 ! [|(l1, s1, w3)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b3) (q1 ! [|(l1, s1, w3)|]))). simpl. easy. }
           assert((q0 & [|(l0, s0, merge_bpf_cont b5 (q1 ! [|(l2, s2, w5)|]))|]) =
                  (merge_bpf_cont (bpf_receive q0 l0 s0 b5) (q1 ! [|(l2, s2, w5)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q0 l0 s0 b5) (q1 ! [|(l2, s2, w5)|]))). simpl. easy. }
           rewrite H3 H5 in H0.
           apply send_inv_leq in H0.
           destruct H0. subst.
           pfold. constructor. easy.
           rewrite H3 H5 in H00.
           apply drop_send in H00.
           rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b3) w3)) in H00.
           rewrite(st_eq(merge_bpf_cont (bpf_receive q0 l0 s0 b5) w5)) in H00. simpl in H00.
           right.
           apply CIH with (p := q1) (w' := (q0 & [|(l0, s0, merge_bpf_cont b5 w5)|])) (w := (q & [|(l, s, merge_bpf_cont b3 w3)|])).
           easy. easy.
           apply extr, extbpf.
           apply extrR, extbpfR, extsR in Pw'. easy.
           apply extr, extbpf.
           apply extrR, extbpfR, extsR in Pw. easy. easy.
           apply proj_send_br. easy. easy.
           apply proj_send_br. easy. easy. 
           simpl. easy. simpl. easy. simpl. easy. simpl. easy.
           apply extrR in Pw. easy.
           apply extrR in Pw'. easy.
           apply mon_projs.
           apply mon_projs.

           (*second inversion on H1 starts here*)
           destruct Hpw2 as (q2, (l2, (s2, (wb, (Heq2, Hs2))))).
           subst.
           pinversion H1. subst.
           pinversion H2. subst.
           specialize (Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q ! [|(l, s, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_recv in H4. easy. easy. easy. easy.
           
           subst.
           specialize (Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q & [|(l, s, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_recv in H3. easy. easy. easy.
           apply mon_projs.
           subst.
           (*second inversion on H2 starts here*)
           pinversion H2. subst.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (Invert_Bpf_Bpf (bpf_send q l s b6) bpf_end q1 l1 s1 w6 (q0 ! [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_recv in H7. easy. easy. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           apply extsR in Pw. easy.

           subst.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (Invert_Bpf_Bpf (bpf_send q l s b6) bpf_end q1 l1 s1 w6 (q0 & [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_recv in H6. easy. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           apply extsR in Pw. easy.
           apply mon_projs.
           
           subst.
           (*third inversion on H2 starts here*)
           pinversion H2. subst.
           apply prj_send_inv2 in H3.
           destruct H3 as (H3a,(b6,(w6,(H3b,(H3c,H3d))))).
           subst.
           assert((q & [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H3 in H0.
           specialize (Invert_Bpf_Bpf (bpf_receive q l s b6) bpf_end q1 l1 s1 w6 (q0 ! [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_recv in H6. easy. easy. easy. simpl. easy. 
           apply extrR in Pw. easy.

           subst.
           apply prj_send_inv2 in H3.
           destruct H3 as (H3a,(b6,(w6,(H3b,(H3c,H3d))))).
           subst.
           assert((q & [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H3 in H0.
           specialize (Invert_Bpf_Bpf (bpf_receive q l s b6) bpf_end q1 l1 s1 w6 (q0 & [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_recv in H5. easy. easy. simpl. easy.
           apply extrR in Pw. easy.
           apply mon_projs.
           apply mon_projs.
           
           subst.
           (*third inversion on H1 starts here*)
           pinversion H1. subst.
           pinversion H2. subst.
           apply snd_end_notRef in H0. 
           easy.
           subst. 
           specialize (Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q ! [|(l, s, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_end in H4. easy. easy. easy. easy.
           
           subst.
           specialize (Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q ! [|(l, s, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           destruct H3.
           rewrite <- inB_coseq.
           right.
           rewrite(coseq_eq (act (q1 ! [|(l1, s3, w3)|]))). simpl.
           apply CoInSplit1 with (y := (q1, snd)) (ys := (act w3)). easy. easy. easy.
           easy. easy.
           
           subst.
           specialize (Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q & [|(l, s, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst. 
           apply psend_not_end in H3. easy. easy. easy.
           
           subst.
           specialize (Invert_Bpf_Bpf bpf_end bpf_end q1 l1 s1 w'0 (q & [|(l, s, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           destruct H.
           rewrite <- inB_coseq.
           right.
           rewrite(coseq_eq (act (q1 ! [|(l1, s3, w3)|]))). simpl.
           apply CoInSplit1 with (y := (q1, snd)) (ys := (act w3)). easy. easy. easy.
           easy.
           apply mon_projs.
           
           subst.
           (*second inversion on H2 starts here*)
           pinversion H2.
           subst.
           apply snd_end_notRef in H0. easy.
           subst. 
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (Invert_Bpf_Bpf (bpf_send q l s b6) bpf_end q1 l1 s1 w6 (q0 ! [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_end in H7. easy. easy. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           apply extsR in Pw. easy.

           subst.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (Invert_Bpf_Bpf (bpf_send q l s b6) bpf_end q1 l1 s1 w6 (q0 ! [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq7 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           destruct H6.
           rewrite <- inB_coseq.
           right.
           rewrite(coseq_eq (act (q1 ! [|(l1, s3, w3)|]))). simpl.
           apply CoInSplit1 with (y := (q1, snd)) (ys := (act w3)). easy. easy. easy.
           easy. simpl. 
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           apply extsR in Pw. easy.

           subst.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (Invert_Bpf_Bpf (bpf_send q l s b6) bpf_end q1 l1 s1 w6 (q0 & [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_end in H6. easy. easy. simpl.
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           apply extsR in Pw. easy.

           subst.
           apply prj_send_inv2 in H4.
           destruct H4 as (H4a,(b6,(w6,(H4b,(H4c,H4d))))).
           subst.
           assert((q ! [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (Invert_Bpf_Bpf (bpf_send q l s b6) bpf_end q1 l1 s1 w6 (q0 & [|(l0, s0, w'1)|])); intro HH.
           rewrite !bpfend_bn in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (b1,(b2,(s3,(H0a,(H0b,H0c))))).
           apply end_nmerge in H0c. easy.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq6 in H0d.
           destruct H0d as (b4,(H0d,(H0e,H0f))).
           subst.
           destruct H5.
           rewrite <- inB_coseq.
           right.
           rewrite(coseq_eq (act (q1 ! [|(l1, s3, w3)|]))). simpl.
           apply CoInSplit1 with (y := (q1, snd)) (ys := (act w3)). easy. easy. easy.
           simpl. 
           apply String.eqb_neq in H. rewrite H. rewrite H4c. easy.
           apply extsR in Pw. easy.
           apply mon_projs.
           
           subst.
           (*third inversion on H2 starts here*)
           pinversion H2.
           subst.
           apply rcv_end_notRef in H0. easy.
           
           subst.
           apply rcv_snd_notRef in H0. easy.
           
           subst.
           apply rcv_snd_notRef in H0. easy.
           
           subst.
           apply prj_send_inv2 in H3.
           destruct H3 as (H3a,(b6,(w6,(H3b,(H3c,H3d))))).
           subst.
           assert((q & [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H3 in H0.
           specialize (Invert_Bpf_Apf (bpf_receive q l s b6) apf_end q1 l1 s1 w6 (q0 & [|(l0, s0, w'1)|])); intro HH.
           rewrite !apfend_an in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,H0c))))).
           apply pneqq6 in H0c.
           destruct H0c as (b4,(H0d,(H0e,H0f))).
           subst.
           apply psend_not_end in H5. easy. easy. simpl. easy.
           apply extrR in Pw. easy.

           subst.
           apply prj_send_inv2 in H3.
           destruct H3 as (H3a,(b6,(w6,(H3b,(H3c,H3d))))).
           subst.
           assert((q & [|(l, s, merge_bpf_cont b6 (q1 ! [|(l1, s1, w6)|]))|]) =
                  (merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_receive q l s b6) (q1 ! [|(l1, s1, w6)|]))). simpl. easy. }
           rewrite H3 in H0.
           specialize (Invert_Bpf_Apf (bpf_receive q l s b6) apf_end q1 l1 s1 w6 (q0 & [|(l0, s0, w'1)|])); intro HH.
           rewrite !apfend_an in HH.
           pose proof H0 as H00.
           apply HH in H0.
           destruct H0 as (b3,(w3,(s3,(H0a,(H0b,H0c))))).
           apply pneqq6 in H0c.
           destruct H0c as (b4,(H0d,(H0e,H0f))).
           subst.
           destruct H4.
           rewrite <- inB_coseq.
           right.
           rewrite(coseq_eq (act (q1 ! [|(l1, s3, w3)|]))). simpl.
           apply CoInSplit1 with (y := (q1, snd)) (ys := (act w3)). easy. easy. easy.
           simpl. easy.
           apply extrR in Pw. easy. 
           apply mon_projs.
           apply mon_projs.
           
       - destruct Hpw1 as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         + subst.
           (*third inversion on H1 starts here*)
           pinversion H1. subst.
           pinversion H2. subst.
           apply snd_end_notRef in H0. easy.
           apply inSendf in H3. subst.
           destruct H3 as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H4. easy.
           apply extsR in Pw. easy.
           subst.
           apply inSendf in H3. subst.
           destruct H3 as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H4. easy.
           apply extsR in Pw. easy.
           subst.
           apply inSendf in H3. subst.
           destruct H3 as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H4. easy.
           apply extsR in Pw. easy. 
           subst.
           apply inSendf in H3. subst.
           destruct H3 as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H4. easy.
           apply extsR in Pw. easy. 
           subst.
           apply inSendf in H3. subst.
           destruct H3 as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H4. easy.
           apply extsR in Pw. easy.
           apply mon_projs.
           
         + subst.
           (*second inversion on H2 starts here*)
           pinversion H2.
           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H3. easy.
           apply extrR in Pw. easy.
           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H3. easy.
           apply extrR in Pw. easy.
           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H3. easy.
           apply extrR in Pw. easy.
           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H3. easy.
           apply extrR in Pw. easy.
           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H3. easy.
           apply extrR in Pw. easy.
           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_recv in H3. easy.
           apply extrR in Pw. easy.
           apply mon_projs.
           apply mon_projs.
           
           subst.
           (*fourth inversion on H1 starts here*)
           pinversion H1. subst.
           pinversion H2. subst.
           pfold. constructor.
           subst.
           pinversion H0.
           apply refinementR4_mon.
           
           subst.
           pinversion H0.
           apply refinementR4_mon.
           
           subst.
           pinversion H0.
           apply refinementR4_mon.
           
           subst.
           pinversion H0.
           apply refinementR4_mon.
           
           subst.
           pinversion H0.
           apply refinementR4_mon.
           apply mon_projs.
           
           subst.
           apply inSendf in H3. subst.
           destruct H3 as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_end in H4. easy.
           apply extsR in Pw. easy.
           
           subst.
           assert(coseqIn (p, snd) (act (q ! [|(l, s, w'0)|])) -> False).
           { intro HH. apply H3.
             rewrite(coseq_eq(act (q ! [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H4. subst. easy.
             subst. inversion H4. subst. easy.
           }
           specialize (actionExLNF (p, snd)  (q ! [|(l, s, w'0)|]) w' H4 H0); intro HH.
           apply pjs_notin_end in H2; try easy.
           subst.
           pfold. constructor.

           subst.
           apply inSendf in H. subst.
           destruct H as (b3,(l3,(s3,(w3,H3a)))).
           subst.
           apply psend_not_end in H3. easy.
           apply extrR in Pw. easy.
           subst.

           assert(coseqIn (p, snd) (act (q & [|(l, s, w'0)|])) -> False).
           { intro HH. apply H.
             rewrite(coseq_eq(act (q & [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H3. subst. inversion H3. subst. easy.
           }
           specialize (actionExLNF (p, snd) (q & [|(l, s, w'0)|]) w' H3 H0); intro HH.
           apply pjs_notin_end in H2; try easy.
           subst.
           pfold. constructor.
           apply mon_projs.
Qed.

Lemma _B_7_2: forall w w' p w1 w2, refinement4 (@und w) (@und w') -> projRC (@und w) p (@und w1) -> projRC (@und w') p (@und w2) -> sRefinement (@und w1) (@und w2).
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
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H4. easy.
           apply extrR in Pw. easy.
           subst.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H3. easy.
           apply extsR in Pw. easy.
           apply mon_projr.
         + destruct Hpw2 as (q2, (l2, (s2, (wb, (Heq2, Hs2))))).
           subst.
           (*second inversion on H1 starts here*)
           pinversion H1. subst.
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H4. easy.
           apply extrR in Pw. easy.
           subst.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H3. easy.
           apply extsR in Pw. easy.
           apply mon_projr.
           subst.
           (*third inversion on H1 starts here*)
           pinversion H1. subst.
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H4. easy.
           apply extrR in Pw. easy.
           subst.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H3. easy.
           apply extsR in Pw. easy.
           apply mon_projr.
       - destruct Hpw1 as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         specialize(sinv w2 Pw2); intros Hpw2.
         destruct Hpw2 as [Hpw2 | [Hpw2 | Hpw2]].
         + destruct Hpw2 as (q2, (l2, (s2, (wb, (Heq2, Hs2))))).
           subst.
           pinversion H2. subst.
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H4. easy.
           apply extrR in Pw'. easy.
           subst.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           apply precv_not_sendc in H3. easy.
           apply extsR in Pw'. easy.
           apply mon_projr.
         + destruct Hpw2 as (q2, (l2, (s2, (wb, (Heq2, Hs2))))).
           subst.
           pinversion H1. subst.
           pinversion H2. subst.
           pose proof H0 as H00.
           specialize(recv_inv_leq apf_end apf_end q2 l1 s1 w'0 l2 s2 w'1); intro HH.
           rewrite !apfend_an in HH.
           apply HH in H0; try easy.
           destruct H0. subst.
           pfold. constructor. easy.
           specialize(drop_recv apf_end apf_end q2 l2 s1 s2 w'0 w'1); intro HH2.
           rewrite !apfend_an in HH2.
           apply HH2 in H00; try easy.
           right. apply CIH with (p := q2) (w' := w'1) (w:= w'0); try easy.
           apply extrR in Pw'. easy.
           apply extrR in Pw. easy.

           subst.
           pose proof H0 as H00.
           specialize(Invert_Apf_Apf apf_end apf_end q1 l1 s1 w'0 (q & [|(l, s, w'1)|])); intro HH.
           rewrite !apfend_an in HH.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (a1,(a2,(H0a,(H0b,(H0c,H0d))))).
           apply end_nmerge_a in H0d. easy.
           destruct H0 as (a3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           apply pneqq4 in H0d; try easy.
           destruct H0d as (a4,(H0d,(H0e,H0f))).
           subst.
           rewrite mgApf2Cpf in H4. subst.
           apply prj_recv_inv1c in H4.
           destruct H4 as (H4a,(H4n,(H4c,H4d))). subst.
           pfold. constructor. easy.
           assert((q & [|(l, s, merge_apf_cont a4 (q2 & [|(l2, s2, w3)|]))|]) =
                  (merge_apf_cont (apf_receive q l s a4) (q2 & [|(l2, s2, w3)|]))).
           { rewrite(st_eq(merge_apf_cont (apf_receive q l s a4) (q2 & [|(l2, s2, w3)|]))). simpl. easy. }
           rewrite H0 in H00.
           specialize(drop_recv apf_end (apf_receive q l s a4) q2 l2 s1 s2 w'0 w3); intro HH2.
           rewrite !apfend_an in HH2.
           apply HH2 in H00; try easy.
           rewrite(st_eq(merge_apf_cont (apf_receive q l s a4) w3)) in H00. simpl in H00.
           right. apply CIH with (p := q2) (w' := (q & [|(l, s, merge_apf_cont a4 w3)|])) (w:= w'0); try easy.
           apply extr. apply extapf.
           apply extrR, extapfR, extrR in Pw'. easy.
           apply extrR in Pw. easy.
           
           apply proj_recv_ar; try easy. 
           rewrite <- inAC. easy. easy.
           
           subst.
           pose proof H0 as H00.
           specialize(Invert_Apf_Apf apf_end apf_end q1 l1 s1 w'0 (q ! [|(l, s, w'1)|])); intro HH.
           rewrite !apfend_an in HH.
           apply HH in H0.
           destruct H0 as [H0 | H0].
           destruct H0 as (a1,(a2,(H0a,(H0b,(H0c,H0d))))).
           apply end_nmerge_a in H0d. easy.
           destruct H0 as (a3,(w3,(s3,(H0a,(H0b,(H0c,H0d)))))).
           symmetry in H0d. apply rcv_snd_notMer in H0d; try easy. easy.
           apply mon_projr.
           
           subst.
           pinversion H2. subst.
           pose proof H0 as H00.
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           pose proof H4 as H4n.
           apply prj_recv_inv1c in H4.
           destruct H4 as (H4a,(H4b,(H4c,H4d))). subst.
           assert((q & [|(l, s, merge_cpf_cont c3 (q1 & [|(l1, s1, w3)|]))|]) =
                  (merge_cpf_cont (cpf_receive q l s c3) (q1 & [|(l1, s1, w3)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_receive q l s c3) (q1 & [|(l1, s1, w3)|]))). simpl. easy. }
           rewrite H3 in H0.
           specialize(recv_inv_leqc (cpf_receive q l s c3) cpf_end q1 l1 s1 w3 l2 s2 w'1); intros HH.
           rewrite cpfend_cn in HH.
           apply HH in H0.
           destruct H0. subst.
           pfold. constructor. easy.
           rewrite H3 in H00.
           specialize(drop_recv_c (cpf_receive q l s c3) cpf_end q1 l2 s1 s2 w3 w'1); intros.
           rewrite !cpfend_cn in H0.
           apply H0 in H00; try easy.
           rewrite(st_eq(merge_cpf_cont (cpf_receive q l s c3) w3)) in H00. simpl in H00.
           right.
           apply CIH with (p := q1) (w' := w'1) (w := (q & [|(l, s, merge_cpf_cont c3 w3)|])).
           easy. easy.
           apply extrR in Pw'. easy.
           apply extr, extcpf.
           apply extrR, extcpfR, extrR in Pw. easy. easy. 
           apply proj_recv_cr; try easy. easy. simpl. apply String.eqb_neq in H. rewrite H. rewrite H3b. easy.
           simpl. apply String.eqb_neq in H. rewrite H. rewrite H3b. easy.
           easy. easy.
           apply extrR in Pw. easy.

           subst.
           pose proof H0 as H00.
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           apply inReceivefE in H6.
           destruct H6 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply prj_recv_inv1c in H4.
           destruct H4 as (H4a,(H4b,(H4c,H4d))).
           apply prj_recv_inv1c in H7.
           destruct H7 as (H7a,(H7b,(H7c,H7d))).
           subst.
           assert((q & [|(l, s, merge_cpf_cont c3 (q2 & [|(l1, s1, w3)|]))|]) =
                  (merge_cpf_cont (cpf_receive q l s c3) (q2 & [|(l1, s1, w3)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_receive q l s c3) (q2 & [|(l1, s1, w3)|]))). simpl. easy. }
           assert((q0 & [|(l0, s0, merge_cpf_cont c6 (q2 & [|(l2, s2, w6)|]))|]) =
                  (merge_cpf_cont (cpf_receive q0 l0 s0 c6) (q2 & [|(l2, s2, w6)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_receive q0 l0 s0 c6) (q2 & [|(l2, s2, w6)|]))). simpl. easy. }
           rewrite H3 H4 in H0, H00.
           apply recv_inv_leqc in H0. destruct H0. subst.
           apply drop_recv_c in H00.
           rewrite(st_eq(merge_cpf_cont (cpf_receive q l s c3) w3)) in H00.
           rewrite(st_eq(merge_cpf_cont (cpf_receive q0 l0 s0 c6) w6)) in H00. simpl in H00.
           pfold. constructor. easy.
           right.
           apply CIH with (p := q2) (w' := (q0 & [|(l0, s0, merge_cpf_cont c6 w6)|])) (w := (q & [|(l, s, merge_cpf_cont c3 w3)|])).
           easy. easy.
           apply extr, extcpf.
           apply extrR, extcpfR, extrR in Pw'. easy.
           apply extr, extcpf.
           apply extrR, extcpfR, extrR in Pw. easy. easy.
           apply proj_recv_cr; try easy.
           apply proj_recv_cr; try easy.
           simpl. apply String.eqb_neq in H. rewrite H. rewrite H3b. easy.
           simpl. apply String.eqb_neq in H5. rewrite H5. rewrite H6b. easy.
           simpl. apply String.eqb_neq in H. rewrite H. rewrite H3b. easy.
           simpl. apply String.eqb_neq in H5. rewrite H5. rewrite H6b. easy.
           easy. easy.
           apply extrR in Pw'. easy.
           apply extrR in Pw. easy.
           
           subst.
           apply rcv_snd_notRef in H0. easy.
           apply mon_projr.
           
           subst.
           pinversion H2. subst.
           pose proof H0 as H00.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           pose proof H3 as H3n.
           apply prj_recv_inv1c in H3.
           destruct H3 as (H4a,(H4b,(H4c,H4d))). subst.
           assert((q ! [|(l, s, merge_cpf_cont c3 (q1 & [|(l1, s1, w3)|]))|]) =
                  (merge_cpf_cont (cpf_send q l s c3) (q1 & [|(l1, s1, w3)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_send q l s c3) (q1 & [|(l1, s1, w3)|]))). simpl. easy. }
           rewrite H in H0 H00.
           specialize(recv_inv_leqc (cpf_send q l s c3) cpf_end q1 l1 s1 w3 l2 s2 w'1); intro HH.
           rewrite cpfend_cn in HH.
           apply HH in H0. destruct H0. subst.
           specialize(drop_recv_c (cpf_send q l s c3) cpf_end q1 l2 s1 s2 w3 w'1); intro HH2.
           rewrite cpfend_cn in HH2.
           apply HH2 in H00; try easy.
           rewrite(st_eq(merge_cpf_cont (cpf_send q l s c3) w3)) in H00. simpl in H00.
           rewrite cpfend_cn in H00.
           pfold. constructor. easy.
           right.
           apply CIH with (p := q1) (w' := w'1) (w := (q ! [|(l, s, merge_cpf_cont c3 w3)|])).
           easy. easy.
           apply extrR in Pw'. easy.
           apply exts, extcpf.
           apply extsR, extcpfR, extrR in Pw. easy. easy.
           apply proj_send_cr; try easy.
           easy.
           simpl. easy. easy. easy.
           apply extsR in Pw. easy.

           subst.
           pose proof H0 as H00.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           apply inReceivefE in H5.
           destruct H5 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply prj_recv_inv1c in H3.
           destruct H3 as (H4a,(H4b,(H4c,H4d))).
           apply prj_recv_inv1c in H6.
           destruct H6 as (H7a,(H7b,(H7c,H7d))).
           subst.
           assert((q ! [|(l, s, merge_cpf_cont c3 (q2 & [|(l1, s1, w3)|]))|]) =
                  (merge_cpf_cont (cpf_send q l s c3) (q2 & [|(l1, s1, w3)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_send q l s c3) (q2 & [|(l1, s1, w3)|]))). simpl. easy. }
           assert((q0 & [|(l0, s0, merge_cpf_cont c6 (q2 & [|(l2, s2, w6)|]))|]) =
                  (merge_cpf_cont (cpf_receive q0 l0 s0 c6) (q2 & [|(l2, s2, w6)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_receive q0 l0 s0 c6) (q2 & [|(l2, s2, w6)|]))). simpl. easy. }
           rewrite H3 H in H0, H00.
           apply recv_inv_leqc in H0. destruct H0. subst.
           apply drop_recv_c in H00.
           rewrite(st_eq(merge_cpf_cont (cpf_send q l s c3) w3)) in H00.
           rewrite(st_eq(merge_cpf_cont (cpf_receive q0 l0 s0 c6) w6)) in H00. simpl in H00.
           pfold. constructor. easy.
           right.
           apply CIH with (p := q2) (w' := (q0 & [|(l0, s0, merge_cpf_cont c6 w6)|])) (w := (q ! [|(l, s, merge_cpf_cont c3 w3)|])).
           easy. easy.
           apply extr, extcpf.
           apply extrR, extcpfR, extrR in Pw'. easy.
           apply exts, extcpf.
           apply extsR, extcpfR, extrR in Pw. easy. easy.

           apply proj_send_cr; try easy.
           apply proj_recv_cr; try easy.
           simpl. easy.
           simpl. apply String.eqb_neq in H4. rewrite H4 H6b. easy.
           easy.
           simpl.
           simpl. apply String.eqb_neq in H4. rewrite H4 H6b. easy.
           easy. easy.
           apply extrR in Pw'. easy.
           apply extsR in Pw. easy.
           
           subst.
           pose proof H0 as H00.
           apply inReceivefE in H.
           destruct H as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           apply inReceivefE in H4.
           destruct H4 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply prj_recv_inv1c in H3.
           destruct H3 as (H4a,(H4b,(H4c,H4d))).
           apply prj_recv_inv1c in H5.
           destruct H5 as (H7a,(H7b,(H7c,H7d))).
           subst.
           assert((q ! [|(l, s, merge_cpf_cont c3 (q2 & [|(l1, s1, w3)|]))|]) =
                  (merge_cpf_cont (cpf_send q l s c3) (q2 & [|(l1, s1, w3)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_send q l s c3) (q2 & [|(l1, s1, w3)|]))). simpl. easy. }
           assert((q0 ! [|(l0, s0, merge_cpf_cont c6 (q2 & [|(l2, s2, w6)|]))|]) =
                  (merge_cpf_cont (cpf_send q0 l0 s0 c6) (q2 & [|(l2, s2, w6)|]))).
           { rewrite(st_eq(merge_cpf_cont (cpf_send q0 l0 s0 c6) (q2 & [|(l2, s2, w6)|]))). simpl. easy. }
           rewrite H3 H in H0, H00.
           apply recv_inv_leqc in H0. destruct H0. subst.
           apply drop_recv_c in H00.
           rewrite(st_eq(merge_cpf_cont (cpf_send q l s c3) w3)) in H00.
           rewrite(st_eq(merge_cpf_cont (cpf_send q0 l0 s0 c6) w6)) in H00. simpl in H00.
           pfold. constructor. easy.
           right.
           apply CIH with (p := q2) (w' := (q0 ! [|(l0, s0, merge_cpf_cont c6 w6)|])) (w := (q ! [|(l, s, merge_cpf_cont c3 w3)|])).
           easy. easy.
           apply exts, extcpf.
           apply extsR, extcpfR, extrR in Pw'. easy.
           apply exts, extcpf.
           apply extsR, extcpfR, extrR in Pw. easy. easy.
           apply proj_send_cr; try easy.
           apply proj_send_cr; try easy.
           simpl. easy. simpl. easy. easy. simpl. easy. simpl. easy. easy.
           apply extsR in Pw'. easy.
           apply extsR in Pw. easy.
           apply mon_projr.
           apply mon_projr.
           
           subst.
           pinversion H1. subst.
           pinversion H2. subst.
           apply rcv_end_notRef in H0. easy.
           subst.
           apply inReceivefE in H3.
           destruct H3 as (c3,(l3,(s3,(w3,(H3a,H3b))))).
           subst.
           pinversion H0.
           subst.
           apply precv_not_end_c in H4. easy.
           apply refinementR4_mon.
           apply extrR in Pw'. easy.
           
           subst.
           assert(coseqIn (q1, rcv) (act (q & [|(l, s, w'1)|])) -> False).
           { intro HH. apply H3.
             rewrite(coseq_eq(act (q & [|(l, s, w'1)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H4. subst. easy.
             subst. inversion H4. subst. easy.
           }
           apply actionExRNF with (a :=  (q1, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q1 & [|(l1, s1, w'0)|]))). simpl.
           apply CoInSplit1 with (y := (q1, rcv)) (ys := (act w'0)). easy. easy.
 
           subst.
           apply rcv_snd_notRef in H0. easy.
           
           subst.
           apply rcv_snd_notRef in H0. easy.
           apply mon_projr.
           
           subst.
           pinversion H2. subst.
           apply rcv_end_notRef in H0. easy.
           
           subst.
           apply inReceivefE in H6.
           destruct H6 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H7. easy.
           apply extrR in Pw'. easy.

           subst.
           assert(coseqIn (p, rcv) (act (q0 & [|(l0, s0, w'1)|])) -> False).
           { intro HH. apply H6.
             rewrite(coseq_eq(act (q0 & [|(l0, s0, w'1)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H7. subst. easy.
             subst. inversion H7. subst. easy.
           }
           apply actionExRNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q & [|(l, s, w'0)|]))). simpl.
           apply CoInSplit2 with (y := (q, rcv)) (ys := (act w'0)). easy. intro HH. apply H. inversion HH. easy. easy.

           subst.
           apply rcv_snd_notRef in H0. easy.
           
           subst.
           apply rcv_snd_notRef in H0. easy.
           apply mon_projr.
           
           subst.
           pinversion H2. subst.
           apply snd_end_notRef in H0. easy.
           
           subst.
           apply inReceivefE in H5.
           destruct H5 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H6. easy.
           apply extrR in Pw'. easy.
 
           subst.
           assert(coseqIn (p, rcv) (act (q0 & [|(l0, s0, w'1)|])) -> False).
           { intro HH. apply H5.
             rewrite(coseq_eq(act (q0 & [|(l0, s0, w'1)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H6. subst. easy.
             subst. inversion H6. subst. easy.
           }
           apply actionExRNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q ! [|(l, s, w'0)|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w'0)). easy. easy. easy. 

           subst.
           apply inReceivefE in H4.
           destruct H4 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H5. easy.
           apply extsR in Pw'. easy.
           
           subst.
           assert(coseqIn (p, rcv) (act (q0 ! [|(l0, s0, w'1)|])) -> False).
           { intro HH. apply H4.
             rewrite(coseq_eq(act (q0 ! [|(l0, s0, w'1)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H5. subst. inversion H5. subst. easy.
           }
           apply actionExRNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q ! [|(l, s, w'0)|]))). simpl.
           apply CoInSplit2 with (y := (q, snd)) (ys := (act w'0)). easy. easy. easy. 
           apply mon_projr.
           apply mon_projr.
           
           subst.
           
           pinversion H1. subst.
           pinversion H2. subst.
           
           pfold. constructor.
           
           subst.
           pinversion H0.
           apply refinementR4_mon.
           
           subst.
           pinversion H0.
           apply refinementR4_mon.

           pfold. constructor.

           subst.
           pinversion H0.
           apply refinementR4_mon.

           pfold. constructor.
           apply mon_projr.

           subst.
           pinversion H2. subst.
           pfold. constructor.
           
           subst.
           apply inReceivefE in H3.
           destruct H3 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H4. easy.
           apply extrR in Pw. easy.

           subst.
           apply inReceivefE in H3.
           destruct H3 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H4. easy.
           apply extrR in Pw. easy.
           
           subst.
           apply inReceivefE in H3.
           destruct H3 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H4. easy.
           apply extrR in Pw. easy.

           subst.
           apply inReceivefE in H3.
           destruct H3 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H4. easy.
           apply extrR in Pw. easy.

           subst.
           apply inReceivefE in H3.
           destruct H3 as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H4. easy.
           apply extrR in Pw. easy.
           apply mon_projr.
           
           subst.
           pinversion H2.
           subst.
           apply rcv_end_notRef in H0. easy.
           
           subst.
           assert(coseqIn (p, rcv) (act (q & [|(l, s, w'0)|])) -> False).
           { intro HH. apply H3.
             rewrite(coseq_eq(act (q & [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H5. subst. easy.
             subst. inversion H5. subst. easy.
           }
           apply actionExLNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (p & [|(l0, s0, w'1)|]))). simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w'1)). easy. easy.

           subst.
           assert(coseqIn (p, rcv) (act (q & [|(l, s, w'0)|])) -> False).
           { intro HH. apply H3.
             rewrite(coseq_eq(act (q & [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H7. subst. easy.
             subst. inversion H7. subst. easy.
           }
           apply actionExLNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q0 & [|(l0, s0, w'1)|]))). simpl.
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w'1)). easy. intro HH. apply H4. inversion HH. easy. easy. 

           pfold. constructor.
           
           subst.
           assert(coseqIn (p, rcv) (act (q & [|(l, s, w'0)|])) -> False).
           { intro HH. apply H3.
             rewrite(coseq_eq(act (q & [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H6. subst. easy.
             subst. inversion H6. subst. easy.
           }
           apply actionExLNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q0 ! [|(l0, s0, w'1)|]))). simpl.
           apply CoInSplit2 with (y := (q0, snd)) (ys := (act w'1)). easy. easy. easy.

           pfold. constructor.
           apply mon_projr.
           
           subst.
           apply inReceivefE in H.
           destruct H as (c6,(l6,(s6,(w6,(H6a,H6b))))).
           subst.
           apply precv_not_end_c in H3. easy.
           apply extsR in Pw. easy.

           subst.
           pinversion H2. subst.
           pfold. constructor.
           
           subst.
           assert(coseqIn (p, rcv) (act (q ! [|(l, s, w'0)|])) -> False).
           { intro HH. apply H.
             rewrite(coseq_eq(act (q ! [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H4. subst. inversion H4. subst. easy.
           }
           apply actionExLNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (p & [|(l0, s0, w'1)|]))). simpl. 
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w'1)). easy. easy.
           
           subst.
           assert(coseqIn (p, rcv) (act (q ! [|(l, s, w'0)|])) -> False).
           { intro HH. apply H.
             rewrite(coseq_eq(act (q ! [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H6. subst. inversion H6. subst. easy.
           }
           apply actionExLNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q0 & [|(l0, s0, w'1)|]))). simpl. 
           apply CoInSplit2 with (y := (q0, rcv)) (ys := (act w'1)). easy. intro HH. apply H3. inversion HH. easy. easy.

           pfold. constructor.
           
           subst.
           assert(coseqIn (p, rcv) (act (q ! [|(l, s, w'0)|])) -> False).
           { intro HH. apply H.
             rewrite(coseq_eq(act (q ! [|(l, s, w'0)|]))) in HH. simpl in HH.
             inversion HH. subst. inversion H5. subst. inversion H5. subst. easy.
           }
           apply actionExLNF with (a :=  (p, rcv)) in H0. easy. easy.
           rewrite(coseq_eq(act (q0 ! [|(l0, s0, w'1)|]))). simpl. 
           apply CoInSplit2 with (y := (q0, snd)) (ys := (act w'1)). easy. easy. easy. 

           pfold. constructor.
           apply mon_projr.
           apply mon_projr.
Qed.

Lemma correctness: forall w w' p w1 w2 w3 w4, 
  refinement4 (@und w) (@und w') -> 
  projSC (@und w) p (@und w1) -> projSC (@und w') p (@und w2) -> 
  projRC (@und w) p (@und w3) -> projRC (@und w') p (@und w4) ->
  sRefinement (@und w1) (@und w2) /\ sRefinement (@und w3) (@und w4).
Proof. split.
       - apply _B_7_1 with (w := w) (w' := w') (p := p); easy.
       - apply _B_7_2 with (w := w) (w' := w') (p := p); easy.
Qed.

