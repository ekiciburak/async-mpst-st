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

Lemma proj_send_inv2: forall b p q l s w wb,
  p <> q ->
  isInB b q = false ->
  projSC w q wb ->
  projSC (p! [|(l, s, merge_bpf_cont b w)|]) q wb.
Proof. intros.
       pinversion H1.
       - subst. pfold. apply pjs_sndN. easy. admit.
       - subst. pfold. constructor. easy. admit.
         left. induction b; intros.
         + simpl in H0.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s1 s2 s3 b) (q ! [|(l0, s0, w')|]))). simpl.
           pfold. constructor. admit.
           left. apply IHb. easy.
           rewrite(st_eq(merge_bpf_cont (bpf_send s1 s2 s3 b) (q ! [|(l0, s0, w')|]))). simpl.
           pfold. simpl in H0. rewrite orbtf in H0.
           destruct H0 as (Ha, Hb).
           constructor. admit. admit.
           left. apply IHb. easy.
           rewrite bpfend_bn. pfold. easy.
       - subst. pfold. constructor. easy. admit.
         left. pfold.
         admit. (*induction b*)
       - subst.
         pfold. apply pjs_sndN. easy. admit.
       - subst. pfold. constructor. easy. admit.
         admit. (*induction b*)
       - subst. pfold. apply pjs_sndN. easy. admit.
       apply mon_projs.
Admitted.

Lemma dropBA4: forall b b2 p l s s' w w',
  isInB b p = false ->
  isInB b2 p = false ->
  paco2 refinementR4 bot2 (merge_bpf_cont b (p ! [|(l, s, w)|])) (merge_bpf_cont b2 (p ! [|(l, s', w')|])) ->
  paco2 refinementR4 bot2 (merge_bpf_cont b w) (merge_bpf_cont b2 w').
Proof. Admitted.

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
           subst. pfold. constructor. easy. simpl. 
           right.
           assert((q ! [|(l, s, merge_bpf_cont b2 (q2 ! [|(l2, s2, w3)|]))|]) = (merge_bpf_cont (bpf_send q l s b2) (q2 ! [|(l2, s2, w3)|]))).
           { rewrite(st_eq(merge_bpf_cont (bpf_send q l s b2) (q2 ! [|(l2, s2, w3)|]))). simpl. easy. }
           rewrite H4 in H0.
           specialize (dropBA4 bpf_end (bpf_send q l s b2) q2 l2 s1 s2 w'0 w3); intro HD.
           rewrite bpfend_bn in HD.
           apply HD in H0.
           apply CIH with (p := q2) (w' := (merge_bpf_cont (bpf_send q l s b2) w3)) (w := w'0).
           admit. admit. admit. admit.
           rewrite bpfend_bn in H0. easy.
           easy.
           rewrite(st_eq (merge_bpf_cont (bpf_send q l s b2) w3)). simpl.
           apply proj_send_inv2. easy. easy. easy. easy. simpl. admit. easy.
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
           (*here*)
           admit. easy.
           admit.
           (*second inversion on H2 starts here*)
           subst.
           pinversion H2. subst.
           specialize(Invert_Bpf_Bpf bpf_end bpf_end q l s w'0 (q2 ! [|(l2, s2, w'1)|])); intros HH.
           assert(isInB bpf_end q2 = false). easy.
           apply HH in H5. 2: { rewrite !bpfend_bn. easy. }
           admit.
Admitted.


