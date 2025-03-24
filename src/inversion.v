Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.reorderingfacts ST.src.acteqfacts ST.src.nondepro ST.src.siso ST.types.local ST.subtyping.refinement.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.

Lemma Invert_Bpf_Apf: forall b a p l s w w', 
  isInB b p = false ->
  refinement4 (merge_bpf_cont b (p ! [|(l, s, w)|])) (merge_apf_cont a w') ->
  exists b1 w1 s', isInB b1 p = false /\ subsort s s' /\ w' = merge_bpf_cont b1 (p ! [|(l, s', w1)|]).
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         rewrite <- meqAp3 in H5, H8, H9.
         specialize(IHb (ApnA3 a0 n) p l s2 w w'0 H H8).
         destruct IHb as (b1,(w2,(s'',(Ha,(Hb,Hc))))).
         case_eq(Apf_eqb (ApnA3 a0 n) a); intros.
         + apply apf_eqb_eq in H1. subst.
           apply merge_same_aeq in H5.
           exists (bpf_receive s s0 s' b1). exists w2.
           exists s''.
           split. simpl. easy.
           split. easy.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s' b1) (p ! [|(l, s'', w2)|]))). simpl.
           easy.
         + apply apf_eqb_neq in H1.
           case_eq(isInA a s); intros.
           ++ assert(isInA (ApnA3 a0 n) s = false).
              { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InN; easy.
              }
              specialize(inH4 (ApnA3 a0 n) a s s0 s' w'0 w' H1 H3 H2 H5); intro HIn4.
              destruct HIn4 as (a1,(Hin4a,Hin4b)).
              case_eq(isBpSend b1); intros.
              * specialize(_39_3 b1 a1 p w'0 (p ! [|(l, s'', w2)|]) w' Ha Hc Hin4b H4); intro HR.
                destruct HR as (c,(Hd,(He,(Hf,Hg)))).
                exists c. exists w2. exists s''.
                split. easy. split. easy. easy.
              * specialize(mcBp2Ap b1 (p ! [|(l, s'', w2)|]) H4); intro HN.
                destruct HN as (a2,(HN,HHa)).
                rewrite HN in Hc.
                case_eq(Apf_eqb a2 a1); intros.
                ** apply apf_eqb_eq in H10. subst.
                   apply merge_same_aeq in Hc.
                   exists bpf_end. exists w2. exists s''.
                   split. simpl. easy. split. easy.
                   rewrite bpfend_bn. easy.
                ** apply apf_eqb_neq in H10.
                   assert(a1 <> a2) by easy.
                   specialize(_39_4 a1 a2 p l s'' w'0 w' w2 H11 Hin4b Hc); intros.
                   destruct H12 as (c,(Hc1,Hc2)).
                   exists (Ap2BpSeq c). exists w2. exists s''.
                   split. apply BisInAF. split. easy.
                   rewrite mcAp2Bp2 in Hc2. easy.
           ++ assert(isInA (ApnA3 a0 n) s = false).
              { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InN; easy.
              }
              assert(merge_apf_cont a w' = merge_apf_cont a w') by easy.
              symmetry in H5.
              specialize(_39_2 (ApnA3 a0 n) a s s
              (merge_apf_cont a w')
              (s & [|(s0, s', w'0)|])
              w' H3 H2 H1 H5 H4
              ); intro HR.
              destruct HR as [HR | HR].
              * destruct HR as (c,(Hd,(He,(Hf,Hg)))).
                rewrite Hc in Hg.
                assert(c = apf_end).
                { apply noPre with (p := s) (l := s0) (s := s') (w := merge_bpf_cont b1 (p ! [|(l, s'', w2)|])) (w' := w'); easy. }
                rewrite H10 in Hg. rewrite apfend_an in Hg.
                exists (bpf_receive s s0 s' b1). exists w2. exists s''.
                split. simpl. easy. split. easy.
                rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s' b1) (p ! [|(l, s'', w2)|]))). simpl.
                easy.
              * destruct HR as (c,(Hd,(He,(Hf,Hg)))).
                rewrite Hc in Hg.
                exists (Bpf_merge (Ap2BpSeq c) (bpf_receive s s0 s' b1)). exists w2. exists s''.
                split.
                apply InMergeFS. split. rewrite BisInAF. easy. simpl. easy.
                split. easy.
                rewrite mcAp2Bp2 in Hg.
                rewrite breOrg2. easy.
                apply refinementR4_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite eqb_neq in Ha.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         rewrite <- meqBp3 in H4, H7, H8.
         case_eq(isBpSend (BpnB3 b0 n)); intros.
         + assert(isInB (BpnB3 b0 n) s = false).
           { case_eq n; intros.
             - simpl. easy.
             - rewrite <- InNS; easy.
           }
           subst.
           specialize(inH7  (BpnB3 b0 n) a s s0 s' w'0 w' H10 H4); intro HIn.
           destruct HIn as (c,(Hc1,(Hc2,Hc3))).
           rewrite Hc2 in H7.
           simpl in H7.
           assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq a) c) w'0) = 
                  (merge_apf_cont a (merge_bpf_cont c w'0))
                  ).
           { rewrite bareOrg1. easy. }
           rewrite H in H7.
           specialize(IHb a p l s2 w  (merge_bpf_cont c w'0) Hb H7).
           destruct IHb as (b1,(w1,(s'',(HHa,(HHb,HHc))))).
           case_eq(Bpf_eqb c b1); intros H1.
           assert(c = b1).
           { apply bpf_eqb_eq in H1. easy. }
           rewrite H2 in HHc.
           assert(w'0 = (p ! [|(l, s'', w1)|])).
           { apply merge_same_beq in HHc. easy. }
           rewrite H3 in Hc3.
           assert(merge_bpf_cont c (s ! [|(s0, s', p ! [|(l, s'', w1)|])|]) =
                  merge_bpf_cont (Bpf_merge c (bpf_send s s0 s' bpf_end)) (p ! [|(l, s'', w1)|])).
           { rewrite breOrg1. rewrite bpfend_bn. easy. }
           exists ((Bpf_merge c (bpf_send s s0 s' bpf_end))). exists w1. exists s''.
           split. simpl.
           apply InMergeFS. split. rewrite H2. easy. simpl. apply eqb_neq in Ha. rewrite Ha. easy.
           split. easy.
           rewrite H11 in Hc3.
           easy.
           assert(merge_bpf_cont c w'0 = merge_bpf_cont c w'0 ) by easy.
           case_eq(isInB c p); intros HHN.
           assert(exists b2, c = Bpf_merge b1 (bpf_send p l s'' b2) /\ w1 = merge_bpf_cont b2 w'0).
           { symmetry in HHc. 
             specialize(inH8 b1 c p (p ! [|(l, s'', w1)|]) w'0 
             HHa HHN HHc
             );intro HP.
             destruct HP as (c1,(HP1,(HP2,HP3))).
             apply inH9 in HP3.
             destruct HP3 as (c2,(HP4,HP5)).
             exists c2. rewrite <- HP4. split; easy.
             easy. 
           }
           destruct H3 as (b2,(Hb2,Hb3)).
           rewrite Hb2 in Hc3.
           simpl in Hc3.
           assert(merge_bpf_cont (Bpf_merge b1 (bpf_send p l s'' b2)) (s ! [|(s0, s', w'0)|]) =
                  merge_bpf_cont b1 (p! [|(l, s'', (merge_bpf_cont b2 (s ! [|(s0, s', w'0)|])))|])).
           { rewrite breOrg1. easy. }
           rewrite H3 in Hc3.
           exists b1. exists(merge_bpf_cont b2 (s ! [|(s0, s', w'0)|])). exists s''.
           split. easy. split. easy. easy.
           rename H1 into HH1.
           assert(c <> b1).
           { apply bpf_eqb_neq in HH1. easy. }
           specialize(_39_1 c b1 p p (merge_bpf_cont c w'0) w'0 (p ! [|(l, s'', w1)|])
           HHN HHa H1 H2 HHc
           ); intro HR.
           destruct HR as [HR | HR].
           ++ destruct HR as (d,(Hr1,(Hr2,(Hr3,Hr4)))).
              rewrite Hr4 in Hc3.
              assert(merge_bpf_cont c (s ! [|(s0, s', merge_bpf_cont d (p ! [|(l, s'', w1)|]))|]) =
                     merge_bpf_cont (Bpf_merge c (bpf_send s s0 s' d)) (p ! [|(l, s'', w1)|])).
              { rewrite breOrg1. easy. }
              rewrite H3 in Hc3.
              exists (Bpf_merge c (bpf_send s s0 s' d)). exists w1. exists s''.
              split. simpl.
              apply InMergeFS. split. easy. simpl. rewrite Hr1.
              apply eqb_neq in Ha. rewrite Ha. easy.
              split. easy. easy.
           ++ destruct HR as (d,(Hr1,(Hr2,(Hr3,Hr4)))).
              rewrite Hr3 in Hc3.
              assert(d = bpf_end).
              { apply noPreS in Hr4. easy. easy. }
              rewrite H3 in Hr4.
              rewrite bpfend_bn in Hr4.
              rewrite <- Hr4 in Hc3.
              rewrite H3 in Hc3. simpl in Hc3.
              assert(merge_bpf_cont (Bpf_merge b1 bpf_end) (s ! [|(s0, s', p ! [|(l, s'', w1)|])|]) =
                    merge_bpf_cont (Bpf_merge b1 (bpf_send s s0 s' bpf_end)) (p ! [|(l, s'', w1)|])).
              { rewrite breOrg1. rewrite bpfend_bn. rewrite mergeRS. easy. }
              rewrite H11 in Hc3.
              exists (Bpf_merge b1 (bpf_send s s0 s' bpf_end)). exists w1. exists s''.
              split. 
              apply InMergeFS. split. easy. simpl. 
              apply eqb_neq in Ha. rewrite Ha. easy.
              split. easy. easy.
         + specialize(mcBp2Ap (BpnB3 b0 n) (s ! [|(s0, s', w'0)|]) H9); intro HR.
           destruct HR as (a2,(HR,HRa)).
           rewrite HR in H4.
           case_eq(Apf_eqb a2 a); intros.
           ++ apply apf_eqb_eq in H10. subst.
              apply merge_same_aeq in H4.
              rewrite HRa in H7.
              assert( (merge_bpf_cont (Ap2BpSeq a) w'0) = (merge_apf_cont a w'0)).
              { rewrite mcAp2Bp2. easy. }
              rewrite H in H7.
              specialize(IHb a p l s2 w  w'0 Hb H7).
              destruct IHb as (b1,(w1,(s'',(HHa,(HHb,HHc))))).
              rewrite HHc in H4.
              exists(bpf_send s s0 s' b1). exists w1. exists s''.
              split. simpl. rewrite HHa. simpl. apply eqb_neq in Ha. rewrite Ha. easy.
              split. easy. 
              rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w1)|]))). simpl. easy.
           ++ apply apf_eqb_neq in H10. subst.
              assert(a <> a2) by easy.
              symmetry in H4.
              assert(merge_apf_cont a w' = merge_apf_cont a w') by easy.
              specialize(_39_4 a a2 s s0 s' (merge_apf_cont a w') w' w'0 H H1 H4); intro HH.
              destruct HH as (c,(HHa,HHb)).
              rewrite HRa in H7. rewrite HHa in H7.
              assert((merge_bpf_cont (Ap2BpSeq (Apf_merge a c)) w'0) = (merge_apf_cont (Apf_merge a c) w'0)).
              { rewrite mcAp2Bp2. easy. }
              rewrite H2 in H7.
              specialize(IHb (Apf_merge a c) p l s2 w  w'0 Hb H7).
              destruct IHb as (b1,(w1,(s'',(HHc,(HHd,HHe))))).
              rewrite HHe in HHb.
              assert(merge_apf_cont c (s ! [|(s0, s', merge_bpf_cont b1 (p ! [|(l, s'', w1)|]))|]) =
                     merge_bpf_cont (Bpf_merge (Ap2BpSeq c) (bpf_send s s0 s' b1)) (p ! [|(l, s'', w1)|])).
              { rewrite mcAp2Bp2. rewrite breOrg1. easy. }
              rewrite H3 in HHb.
              exists (Bpf_merge (Ap2BpSeq c) (bpf_send s s0 s' b1)). exists w1. exists s''.
              split. simpl.
              apply InMergeFS. split. rewrite BisInAF. easy. simpl.
              apply eqb_neq in Ha. rewrite Ha. easy.
              split. easy.
              easy.
         apply refinementR4_mon. 
       - rewrite bpfend_bn in H0.
         pinversion H0.
         subst.
         rewrite <- meqBp3 in H5, H8, H9.
         assert(isInB (BpnB3 b n) p = false).
         { case_eq n; intros.
           - simpl. easy.
           - rewrite <- InNS; easy.
         }
         specialize(inH7 (BpnB3 b n) a p l s' w'0 w' H1 H5); intro Hin.
         destruct Hin as (c,(Hi1,(Hi2,Hi3))).
         exists c. exists w'0. exists s'.
         split. easy. split. easy. easy.
         apply refinementR4_mon.
Qed.

Lemma Invert_Bpf_Bpf: forall a b p l s w w', 
  isInB a p = false ->
  refinement4 (merge_bpf_cont a (p ! [|(l, s, w)|])) (merge_bpf_cont b w') ->
  (exists a1 a2 s', isInB a1 p = false /\ subsort s s' /\ b = Bpf_merge a1 (bpf_send p l s' a2))
  \/
  (exists a1  w1 s', isInB a1 p = false /\ subsort s s' /\ isInB b p = false /\ w' = merge_bpf_cont a1 (p ! [|(l, s', w1)|])).
Proof. intro a.
       induction a; intros.
       - simpl in H.
         rewrite(st_eq (merge_bpf_cont (bpf_receive s s0 s1 a) (p ! [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         rewrite <- meqAp3 in H5, H8, H9.
         assert((merge_apf_cont (ApnA3 a0 n) w'0) = (merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) w'0)).
         { rewrite mcAp2Bp2. easy. }
         rewrite H1 in H8.
         specialize(IHa (Ap2BpSeq (ApnA3 a0 n)) p l s2 w w'0 H H8).
         assert(merge_apf_cont (ApnA3 a0 n) (s & [|(s0, s', w'0)|]) =
                merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) (s & [|(s0, s', w'0)|])).
         { rewrite mcAp2Bp2. easy. }
         rewrite H2 in H5.
         case_eq(Bpf_eqb (Ap2BpSeq (ApnA3 a0 n)) b); intros.
         + assert(Ap2BpSeq (ApnA3 a0 n) = b).
           { apply bpf_eqb_eq. easy. }
           assert((s & [|(s0, s', w'0)|]) = w').
           { rewrite H4 in H5. apply merge_same_beq in H5. easy. }
           destruct IHa as [IHa | IHa].
           ++ destruct IHa as (b1,(b2,(s'',(Hb1,(Hb2,Hb3))))). 
              left.
              exists b1. exists b2. exists s''.
              split. easy. split. easy. rewrite <- H4. easy.
           ++ destruct IHa as (b1,(w1,(s'',(Hb1,(Hb2,(Hb3,Hb4)))))).
              rewrite Hb4 in H10.
              right. 
              exists (Bpf_merge (Ap2BpSeq (apf_receive s s0 s' apf_end)) b1).
              exists w1. exists s''.
              split. simpl. easy. split. easy. split. rewrite <- H4. easy.
              simpl.
              rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s' b1) (p ! [|(l, s'', w1)|]))). simpl.
              easy.
         + assert(Ap2BpSeq (ApnA3 a0 n) <> b).
           { apply bpf_eqb_neq. easy. }
           destruct IHa as [IHa | IHa].
           ++ destruct IHa as (b1,(b2,(s'',(Hb1,(Hb2,Hb3))))).
              apply abContra in Hb3. easy.
           ++ destruct IHa as (b1,(w1,(s'',(Hb1,(Hb2,(Hb3,Hb4)))))).
              simpl in Hb3.
              case_eq (isInB b p); intros.
              * assert(merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) (s & [|(s0, s', w'0)|]) =
                       merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) w'0).
                { rewrite bareOrg2. easy. }
                rewrite H11 in H5. 
                assert(isInB (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) p = false).
                { rewrite BisInAF. easy. }
                specialize(inH8 (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b
                p w'0 w' H12 H10 H5
                ); intro HP.
                destruct HP as (c,(HP1,(HP2,HP3))).
                rewrite Hb4 in HP3.
                specialize(inH8 b1 c p (p ! [|(l, s'', w1)|]) w' Hb1 HP1 HP3); intro HP.
                destruct HP as (c2,(HP4,(HP5,HP6))).
                left. 
                rewrite HP2. simpl.
                rewrite HP5. simpl.
                assert(exists c3, c2 = bpf_send p l s'' c3).
                { apply inH9 in HP6.
                  destruct HP6 as (b2,(HP6,HP7)).
                  exists b2. easy. easy.
                }
                destruct H13 as (c3,HP7).
                rewrite HP7.
                assert(Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) (Bpf_merge b1 (bpf_send p l s'' c3)) =
                       Bpf_merge (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1) (bpf_send p l s'' c3)).
                { rewrite bpf_merge_assoc. easy. }
                rewrite H13.
                exists (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1).
                exists c3.
                exists s''.
                split. simpl.
                apply InMergeFS. rewrite BisInAF. easy.
                split. easy. easy.
              * assert(merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) (s & [|(s0, s', w'0)|]) =
                       merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) w'0).
                { rewrite bareOrg2. easy. }
                rewrite H11 in H5.
                rewrite Hb4 in H5.
                assert(merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) (merge_bpf_cont b1 (p ! [|(l, s'', w1)|])) =
                       merge_bpf_cont (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1) (p ! [|(l, s'', w1)|])).
                { rewrite bareOrg1. rewrite mcAp2Bp2. easy.  }
                rewrite H12 in H5.
                case_eq(Bpf_eqb b (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1)); intros.
                ** assert((p ! [|(l, s'', w1)|]) = w').
                   { apply bpf_eqb_eq in H13. rewrite <- H13 in H5. apply merge_same_beq in H5. easy. }
                   right. exists bpf_end. exists w1. exists s''.
                   split. easy. split. easy. split. easy. rewrite bpfend_bn. easy.
                ** assert(isInB (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1) p = false).
                   { apply InMergeFS. rewrite BisInAF. easy. }
                   assert( b <> Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1).
                   { apply bpf_eqb_neq. easy. }
                   assert(merge_bpf_cont b w' = merge_bpf_cont b w') by easy.
                   symmetry in H5.
                   specialize(_39_1 b (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1) 
                   p p (merge_bpf_cont b w') w' (p ! [|(l, s'', w1)|]) H10 H14 H15 H16 H5
                   ); intro HP.
                   destruct HP as [HP | HP].
                   *** destruct HP as (c,(HP1,(HP2,(HP3,HP4)))).
                       right. exists c. exists w1. exists s''.
                       split. easy. split. easy. split. easy. easy.
                   *** destruct HP as (c,(HP1,(HP2,(HP3,HP4)))).
                       apply noPreS in HP4; try easy.
                       rewrite HP4 in HP3. simpl in HP3.
                       rewrite mergeRS in HP3.
                       rewrite <- HP3 in H5.
                       apply merge_same_beq in H5.
                       right.
                       exists bpf_end.
                       exists w1.
                       exists s''.
                       rewrite bpfend_bn. easy.
         apply refinementR4_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite eqb_neq in Ha.
         rewrite(st_eq (merge_bpf_cont (bpf_send s s0 s1 a) (p ! [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         rewrite <- meqBp3 in H4, H7, H8.
         specialize(IHa (BpnB3 b0 n) p l s2 w w'0 Hb H7).
         destruct IHa as [IHa | IHa].
         + destruct IHa as (b1,(b2,(s'',(Hb1,(Hb2,Hb3))))). 
           rewrite Hb3 in H4.
           case_eq(Bpf_eqb (Bpf_merge b1 (bpf_send p l s'' b2)) b); intros.
           ++ assert((Bpf_merge b1 (bpf_send p l s'' b2)) = b).
              { apply bpf_eqb_eq. easy. }
              rewrite <- H1.
              left. exists b1. exists b2. exists s''.
              split. easy. split. easy. easy.
           ++ assert((Bpf_merge b1 (bpf_send p l s'' b2)) <> b).
              { apply bpf_eqb_neq. easy. }
              case_eq(isInB b s); intros.
              * assert(isInB (Bpf_merge b1 (bpf_send p l s'' b2)) s = false).
                { rewrite InMergeFS. simpl.
                  assert(isInB (BpnB3 b0 n) s = false).
                  { case_eq n; intros.
                    - simpl. easy.
                    - rewrite <- InNS; easy.
                  }
                  rewrite Hb3 in H3.
                  apply InMergeFS in H3. simpl in H3.
                  easy.
                }
                specialize(inH8 (Bpf_merge b1 (bpf_send p l s'' b2)) b s
                (s ! [|(s0, s', w'0)|]) w' H3 H2 H4
                ); intro HP.
                destruct HP as (c,(HP1,(HP2,HP3))).
                assert(Bpf_merge (Bpf_merge b1 (bpf_send p l s'' b2)) c =
                       Bpf_merge b1 (bpf_send p l s'' (Bpf_merge b2 c))).
                { rewrite bpf_merge_assoc. easy. }
                rewrite H9 in HP2.
                left.
                exists b1. exists (Bpf_merge b2 c). exists s''.
                split. easy. split. easy. easy.
              * assert(isInB (Bpf_merge b1 (bpf_send p l s'' b2)) s = false).
                { rewrite InMergeFS. simpl.
                  assert(isInB (BpnB3 b0 n) s = false).
                  { case_eq n; intros.
                    - simpl. easy.
                    - rewrite <- InNS; easy.
                  }
                  rewrite Hb3 in H3.
                  apply InMergeFS in H3. simpl in H3.
                  easy.
                }
                assert(merge_bpf_cont b w' = merge_bpf_cont b w') by easy. 
                symmetry in H4.
                specialize(_39_1 (Bpf_merge b1 (bpf_send p l s'' b2)) b s s
                (merge_bpf_cont b w')
                (s ! [|(s0, s', w'0)|]) w' H3 H2 H1 H4 H9
                ); intro HP.
                destruct HP as [HP | HP].
                ** destruct HP as (c,(HP1,(HP2,(HP3,HP4)))).
                   assert(c = bpf_end).
                   { apply noPreS in HP4; easy. }
                   rewrite H10 in HP3.
                   assert(Bpf_merge (Bpf_merge b1 (bpf_send p l s'' b2)) bpf_end =
                          Bpf_merge b1 (bpf_send p l s'' b2)).
                   { rewrite bpf_merge_assoc. simpl.
                     rewrite mergeRS.
                     easy.
                   }
                   rewrite H11 in HP3.
                   left.
                   exists b1. exists b2. exists s''.
                   split. easy. split. easy. easy.
                ** destruct HP as (c,(HP1,(HP2,(HP3,HP4)))).
                   case_eq(isInB b p); intros.
                   *** specialize(inH5B b1 b2 b c p l s'' Hb1 H10 HP3); intro HP.
                       destruct HP as (c2,(HP5,HP6)).
                       left.
                       exists b1. exists c2. exists s''.
                       split. easy. easy.
                   *** specialize(inH6B b1 b2 b c p l s'' Hb1 H10 HP3); intro HP.
                       destruct HP as (c2,(HP5,(HP6,HP7))).
                       rewrite HP6 in HP4.
                       assert(merge_bpf_cont (Bpf_merge c2 (bpf_send p l s'' b2)) (s ! [|(s0, s', w'0)|]) =
                              merge_bpf_cont c2 (p ! [|(l, s'', merge_bpf_cont b2 (s ! [|(s0, s', w'0)|]))|])).
                       { rewrite breOrg1. easy. }
                       rewrite H11 in HP4.
                       right. 
                       exists c2. exists(merge_bpf_cont b2 (s ! [|(s0, s', w'0)|])). exists s''.
                       split. easy. split. easy. split; easy.
         + destruct IHa as (b1,(w2,(s'',(Hb1,(Hb2,(Hb3,Hb4)))))).
           case_eq(Bpf_eqb (BpnB3 b0 n) b); intros.
           ++ assert((BpnB3 b0 n) = b).
              { apply bpf_eqb_eq. easy. } 
             rewrite H1 in H4.
             assert((s ! [|(s0, s', w'0)|]) = w').
             { apply merge_same_beq in H4. easy. }
             rewrite Hb4 in H2.
             assert(s ! [|(s0, s', merge_bpf_cont b1 (p ! [|(l, s'', w2)|]))|] =
                    merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w2)|])).
             { rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w2)|]))). simpl. easy. }
             rewrite H3 in H2.
             right.
             exists(bpf_send s s0 s' b1).
             exists w2.
             exists s''.
             simpl. split. rewrite Hb1. apply eqb_neq in Ha. rewrite Ha. easy. 
             split. easy. rewrite <- H1. split; easy.
           ++ assert((BpnB3 b0 n) <> b).
              { apply bpf_eqb_neq. easy. }
              case_eq(isInB b s); intros.
              * assert(isInB (BpnB3 b0 n) s = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InNS; easy.
                }
                specialize(inH8 (BpnB3 b0 n) b s (s ! [|(s0, s', w'0)|]) w'
                H3 H2 H4
                ); intro HP.
                destruct HP as (c,(HP1,(HP2,HP3))).
                rewrite Hb4 in HP3.
                assert(s ! [|(s0, s', merge_bpf_cont b1 (p ! [|(l, s'', w2)|]))|] =
                      merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w2)|])).
                { rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w2)|]))). simpl. easy. }
                rewrite H9 in HP3.
                case_eq(Bpf_eqb (bpf_send s s0 s' b1) c); intros.
                ** assert((bpf_send s s0 s' b1) = c).
                   { apply bpf_eqb_eq. easy. }
                   assert((p ! [|(l, s'', w2)|]) = w').
                   { rewrite H11 in HP3.
                     apply merge_same_beq in HP3. easy.
                   }
                   right. exists bpf_end. exists w2. exists s''.
                   simpl. rewrite bpfend_bn. split. easy. split. easy. split. rewrite HP2.
                   rewrite <- H11.
                   apply InMergeFS. simpl. split. easy. rewrite Hb1.
                   apply eqb_neq in Ha. rewrite Ha. easy.
                   easy.
                ** assert((bpf_send s s0 s' b1) <> c).
                   { apply bpf_eqb_neq. easy. }
                   case_eq(isInB c p); intros.
                   *** assert(isInB (bpf_send s s0 s' b1) p = false).
                       { simpl. apply eqb_neq in Ha. rewrite Ha. easy. }
                       specialize(inH8 (bpf_send s s0 s' b1) c
                       p (p ! [|(l, s'', w2)|]) w' H13 H12 HP3
                       ); intro HP.
                       destruct HP as (c2,(HP4,(HP5,HP6))).
                       rewrite HP5 in HP2.
                       assert(exists c3, c2 = bpf_send p l s'' c3).
                       { apply inH9 in HP6. 
                         destruct HP6 as (c3,(HP6,HP7)).
                         exists c3. easy.
                         easy.
                       }
                       destruct H14 as (c3,HP7).
                       rewrite HP7 in HP2.
                       assert(Bpf_merge (BpnB3 b0 n) (Bpf_merge (bpf_send s s0 s' b1) (bpf_send p l s'' c3)) =
                             (Bpf_merge (Bpf_merge (BpnB3 b0 n) (bpf_send s s0 s' b1)) (bpf_send p l s'' c3))).
                       { rewrite bpf_merge_assoc. easy. }
                       rewrite H14 in HP2.
                       left. 
                       exists((Bpf_merge (BpnB3 b0 n) (bpf_send s s0 s' b1))).
                       exists c3.
                       exists s''.
                       split. simpl.
                       apply InMergeFS. simpl.
                       apply eqb_neq in Ha. rewrite Ha.
                       easy.
                       split; easy.
                   *** assert(isInB (bpf_send s s0 s' b1) p = false).
                       { simpl. apply eqb_neq in Ha. rewrite Ha. easy. }
                       assert(merge_bpf_cont c w' = merge_bpf_cont c w') by easy.
                       symmetry in HP3.
                       specialize(_39_1 (bpf_send s s0 s' b1) c p p
                       (merge_bpf_cont c w') (p ! [|(l, s'', w2)|]) w' H13 H12 H11 HP3 H14
                       ); intro HP.
                       destruct HP as [HP | HP].
                       +++ destruct HP as (c2,(HP4,(HP5,(HP6,HP7)))).
                           assert(c2 = bpf_end).
                           { apply noPreS in HP7; easy. }
                           rewrite H15 in HP7. 
                           rewrite bpfend_bn in HP7.
                           right. 
                           exists bpf_end. exists w2. exists s''.
                           split. easy. split. easy. split. rewrite HP2. rewrite HP6.
                           rewrite H15. simpl. 
                           apply InMergeFS. simpl.
                           apply eqb_neq in Ha. rewrite Ha. split. easy.
                           simpl. 
                           apply InMergeFS. simpl. easy.
                           rewrite bpfend_bn. easy.
                       +++ destruct HP as (c2,(HP4,(HP5,(HP6,HP7)))).
                           right.
                           exists c2. exists w2. exists s''.
                           split. easy. split. easy. rewrite HP2. split.
                           apply InMergeFS. simpl. easy. easy.
              * assert(isInB (BpnB3 b0 n) s = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InNS; easy. }
                assert(merge_bpf_cont b w' = merge_bpf_cont b w') by easy.
                symmetry in H4.
                specialize(_39_1 (BpnB3 b0 n) b s s
                (merge_bpf_cont b w') (s ! [|(s0, s', w'0)|]) w' H3 H2 H1 H4 H9
                ); intro HP.
                destruct HP as [HP | HP].
                ** destruct HP as (c,(HP4,(HP5,(HP6,HP7)))).
                   assert(c = bpf_end).
                   { apply noPreS in HP7; easy. }
                   rewrite H10 in HP7. rewrite bpfend_bn in HP7.
                   rewrite Hb4 in HP7.
                   assert(s ! [|(s0, s', merge_bpf_cont b1 (p ! [|(l, s'', w2)|]))|] =
                          merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w2)|])).
                   { rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [|(l, s'', w2)|]))). simpl. easy. }
                   rewrite H11 in HP7.
                   right.
                   exists(bpf_send s s0 s' b1).
                   exists w2.
                   exists s''.
                   split. simpl. rewrite Hb1. apply eqb_neq in Ha. rewrite Ha. easy.
                   split. easy. split. rewrite HP6. rewrite H10. simpl.
                   rewrite mergeRS. easy.
                   easy.
                ** destruct HP as (c,(HP4,(HP5,(HP6,HP7)))).
                   rewrite Hb4 in HP7.
                   assert(merge_bpf_cont c (s ! [|(s0, s', merge_bpf_cont b1 (p ! [|(l, s'', w2)|]))|]) =
                          merge_bpf_cont (Bpf_merge c (bpf_send s s0 s' b1)) (p ! [|(l, s'', w2)|])).
                   { rewrite breOrg1. easy. }
                   rewrite H10 in HP7.
                   right.
                   exists(Bpf_merge c (bpf_send s s0 s' b1)).
                   exists w2.
                   exists s''.
                   split. simpl.
                   apply InMergeFS. simpl.
                   apply eqb_neq in Ha. rewrite Ha. simpl. rewrite Hb1. 
                   split; try easy.
                   rewrite HP6 in Hb3.
                   apply InMergeFS in Hb3. easy.
                   split. easy. split.
                   rewrite HP6 in Hb3.
                   apply InMergeFS in Hb3. easy.
                   easy.
         apply refinementR4_mon.
       - rewrite bpfend_bn in H0.
         pinversion H0.
         subst.
         rewrite <- meqBp3 in H5, H8, H9.
         case_eq(Bpf_eqb (BpnB3 b0 n) b); intros.
         + assert((BpnB3 b0 n) = b).
           { apply bpf_eqb_eq. easy. }
           assert((p ! [|(l, s', w'0)|]) = w').
           { rewrite H2 in H5. apply merge_same_beq in H5. easy. }
           right.
           exists bpf_end. exists w'0. exists s'.
           simpl. split. easy. split. easy. split. rewrite <- H2.
           case_eq n; intros.
           - simpl. easy.
           - rewrite <- InNS; easy.
           rewrite bpfend_bn. easy.
         + assert((BpnB3 b0 n) <> b).
           { apply bpf_eqb_neq. easy. }
           case_eq(isInB b p); intros.
           ++ assert(isInB (BpnB3 b0 n) p = false).
              { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InNS; easy.
              }
              specialize(inH8 (BpnB3 b0 n) b p(p ! [|(l, s', w'0)|]) w'
              H4 H3 H5
              ); intro HP.
              destruct HP as (c,(HP1,(HP2,HP3))).
              assert(exists c2, c = bpf_send p l s' c2).
              { apply inH9 in HP3.
                destruct HP3 as (c3,(HP3,HP4)).
                exists c3. easy. easy.
              }
              destruct H10 as (c2,H10).
              rewrite H10 in HP2.
              left.
              exists (BpnB3 b0 n).
              exists c2.
              exists s'.
              split. easy. split. easy. easy.
           ++ assert(isInB (BpnB3 b0 n) p = false).
              { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InNS; easy.
              }
              assert(merge_bpf_cont b w' = merge_bpf_cont b w') by easy.
              symmetry in H5.
              specialize(_39_1 (BpnB3 b0 n) b p p
              (merge_bpf_cont b w') (p ! [|(l, s', w'0)|]) w' H4 H3 H2 H5 H10
              ); intro HP.
              destruct HP as [HP | HP].
              * destruct HP as (c,(HP1,(HP2,(HP3,HP4)))).
                assert(c = bpf_end).
                { apply noPreS in HP4; easy. }
                rewrite H11 in HP4.
                rewrite bpfend_an in HP4.
                right. 
                exists bpf_end. exists w'0. exists s'.
                split. easy. split. easy. split. easy. rewrite bpfend_bn. easy.
              * destruct HP as (c,(HP1,(HP2,(HP3,HP4)))).
                right.
                exists c. exists w'0. exists s'.
                split; easy.
         apply refinementR4_mon.
Qed.


Lemma Invert_Apf_Apf: forall a b p l s w w', 
  isInA a p = false ->
  refinement4 (merge_apf_cont a (p & [|(l, s, w)|])) (merge_apf_cont b w') ->
  (exists a1 a2 s', isInA a1 p = false /\ subsort s' s /\ b = Apf_merge a1 (apf_receive p l s' a2))
  \/
  (exists a1  w1 s', isInA a1 p = false /\ subsort s' s /\ isInA b p = false /\ w' = merge_apf_cont a1 (p & [|(l, s', w1)|])).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         pinversion H0.
         + subst.
           rewrite <- meqAp3 in H5.
           case_eq(Apf_eqb (ApnA3 a n) b); intros.
           ++ apply apf_eqb_eq in H1. subst.
              apply merge_same_aeq in H5.
              rewrite <- H5.
              right.
              exists apf_end. exists w'0. exists s'.
              split. simpl. easy.
              rewrite apfend_an.
              split. easy. split.

              case_eq n; intros.
              subst. simpl in *.
              easy.
              rewrite <- InN; easy.

              easy.
           ++ case_eq(isInA b p); intros.
              * assert((ApnA3 a n) <> b).
                { apply apf_eqb_neq in H1. easy. }
                assert(isInA (ApnA3 a n) p = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InN; easy.
                }
                specialize(inH4 (ApnA3 a n) b p l s' w'0 w' H3 H4 H2 H5); intro Hin.
                destruct Hin as (a1,Ha1). 
                left.
                exists(ApnA3 a n). exists a1. exists s'.
                split. easy. split. easy. easy.
              * assert((ApnA3 a n) <> b).
                { apply apf_eqb_neq in H1. easy. }
                assert(isInA (ApnA3 a n) p = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InN; easy.
                }
                assert(merge_apf_cont b w' = merge_apf_cont b w') by easy.
                symmetry in H5. 
                specialize(_39_2 (ApnA3 a n) b p p
                (merge_apf_cont b w')
                (p & [|(l, s', w'0)|]) w'
                H4 H2 H3 H5 H10
                ); intro Hnin. 
                destruct Hnin as [Hnin | Hnin].
                destruct Hnin as (c, (Ha,(Hb,(Hc,Hd)))).
                assert(c = apf_end).
                { apply noPre with (p := p) (l := l) (s := s') (w :=  w'0) (w' := w'); easy.
                }
                rewrite H11 in Hd.
                rewrite apfend_an in Hd.
                right. exists apf_end. exists w'0. exists s'.
                split. simpl. easy. split. easy. split. easy.
                rewrite apfend_an. easy.
                destruct Hnin as (c, (Ha,(Hb,(Hc,Hd)))).
                right.
                exists c. exists w'0. exists s'.
                split. easy. split. easy. split. easy. easy.
                apply refinementR4_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [|(l, s2, w)|]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         rewrite <- meqAp3 in H7, H4.
         rewrite eqb_neq in Ha.
         specialize(IHa (ApnA3 a0 n) p l s2 w w'0 Hb H7).
         destruct IHa as [IHa | IHa].
         destruct IHa as (a1,(a2,(s'',(Hc,(Hd,He))))).
         case_eq(Apf_eqb (ApnA3 a0 n) b); intros.
         + apply apf_eqb_eq in H. subst.
           apply merge_same_aeq in H4.
           left. exists a1. exists a2. exists s''.
           split. easy. split. easy. easy.
         + case_eq(isInA b s); intros.
           * assert((ApnA3 a0 n) <> b).
             { apply apf_eqb_neq in H. easy. }
             assert(isInA (ApnA3 a0 n) s = false).
             { case_eq n; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             specialize(inH4 (ApnA3 a0 n) b s s0 s' w'0 w' H2 H3 H1 H4); intro Hin.
             destruct Hin as (a3,Ha3).
             rewrite He in Ha3.
             simpl in Ha3.
             assert(b = Apf_merge a1 (apf_receive p l s'' (Apf_merge a2 (apf_receive s s0 s' a3)))).
             { destruct Ha3 as (Ha3,Ha4).
               rewrite Ha3.
               rewrite reOrg1.
               easy.
             }
             left. exists a1. exists (Apf_merge a2 (apf_receive s s0 s' a3)).
             exists s''. split. easy. split. easy. easy.
           * assert((ApnA3 a0 n) <> b).
             { apply apf_eqb_neq in H. easy. }
             assert(isInA (ApnA3 a0 n) s = false).
             { case_eq n; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             assert(merge_apf_cont b w' = merge_apf_cont b w') by easy.
             symmetry in H4. 
             specialize(_39_2 (ApnA3 a0 n) b s s
                (merge_apf_cont b w')
                (s & [|(s0, s', w'0)|]) w'
                H3 H1 H2 H4 H9
                ); intro Hnin.
             destruct Hnin as [Hnin | Hnin].
             destruct Hnin as (c, (Hf,(Hg,(Hh,Hi)))).
             rewrite He in Hh.
             assert(b = Apf_merge a1 (apf_receive p l s'' (Apf_merge a2 c))).
             { rewrite Hh.
               rewrite reOrg1. easy.
             }
             left.
             exists a1. exists (Apf_merge a2 c). exists s''.
             split. easy. split. easy. easy.
             destruct Hnin as (c, (Hf,(Hg,(Hh,Hi)))).
             rewrite He in Hh.
             case_eq(isInA b p); intros.
             ++ specialize(inH5 a1 a2 b c p l s'' Hc H10 Hh); intro Hin.
                destruct Hin as (a3,(Ha3,Ha4)).
                left. exists a1. exists a3. exists s''.
                split. easy. split. easy. easy.
             ++ specialize(inH6 a1 a2 b c p l s'' Hc H10 Hh); intro Hin.
                destruct Hin as (a3,(Ha3,(Ha4,Ha5))).
                right.
                rewrite Ha4 in Hi.
                assert(w' = merge_apf_cont a3 (p & [|(l, s'', merge_apf_cont a2 (s & [|(s0, s', w'0)|]))|])).
                { rewrite Hi.
                  rewrite reOrg2. easy.
                }
                exists a3. exists (merge_apf_cont a2 (s & [|(s0, s', w'0)|])). exists s''.
                split. easy. split. easy. split. easy. easy.
         destruct IHa as (a1,(w1,(s'',(Ha1,(Ha2,(Ha3,Ha4)))))).
         case_eq(Apf_eqb (ApnA3 a0 n) b); intros.
         + apply apf_eqb_eq in H. subst.
           apply merge_same_aeq in H4.
           right.
           exists(apf_receive s s0 s' a1).
           exists w1. exists s''.
           split. simpl. rewrite Ha1. 
           rewrite orbtf. split. rewrite eqb_neq. easy. easy.
           split. easy. split. easy.
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s' a1) (p & [|(l, s'', w1)|]))). simpl.
           easy.
         + rewrite Ha4 in H4.
           case_eq(isInA b s); intros.
           * assert((ApnA3 a0 n) <> b).
             { apply apf_eqb_neq in H. easy. }
             assert(isInA (ApnA3 a0 n) s = false).
             { case_eq n; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             specialize(inH4 (ApnA3 a0 n) b s s0 s' (merge_apf_cont a1 (p & [|(l, s'', w1)|])) w' H2 H3 H1 H4); intro Hin.
             destruct Hin as (a3,(Ha5,Ha6)).
             case_eq(Apf_eqb a1 a3); intros.
             ++ apply apf_eqb_eq in H9. subst.
                apply merge_same_aeq in Ha6.
                right.
                exists apf_end. exists w1. exists s''.
                simpl. split. easy. split. easy.
                split.
                assert(isInA (ApnA3 a0 n) s = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InN; easy.
                }
                rewrite InMerge. rewrite Ha3. simpl.
                apply orbtf. split. rewrite eqb_neq. easy. easy.
                rewrite apfend_an. easy.
             ++ assert(a1 <> a3).
                { apply apf_eqb_neq in H9. easy. }
                case_eq(isInA a3 p); intros.
                ** specialize(inH4 a1 a3 p l s'' w1 w' H10 Ha1 H11 Ha6); intro Hin.
                   destruct Hin as (a2,(Ha2a,Ha2b)).
                   rewrite Ha2a in Ha5.
                   assert(b = Apf_merge (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' a1)) (apf_receive p l s'' a2)).
                   { rewrite Ha5.
                     rewrite reOrg1.
                     easy.
                   }
                   left.
                   exists(Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' a1)).
                   exists a2. exists s''.
                   split.
                   assert(isInA (ApnA3 a0 n) s = false).
                   { case_eq n; intros.
                     - simpl. easy.
                     - rewrite <- InN; easy.
                   }
                   rewrite InMerge. rewrite Ha3. simpl.
                   apply orbtf. split. rewrite eqb_neq. easy. easy.
                   split. easy. easy.
                ** symmetry in Ha6.
                   assert(merge_apf_cont a3 w' = merge_apf_cont a3 w') by easy.
                   specialize(_39_2 a1 a3 p p 
                   (merge_apf_cont a3 w') (p & [|(l, s'', w1)|]) w'
                   Ha1 H11 H10 Ha6 H12
                   ); intro Hin.
                   destruct Hin as [Hin | Hin].
                   *** destruct Hin as (c,(Hc,(Hd,(He,Hf)))).
                       assert(c = apf_end).
                       { apply noPre with (p := p) (l := l) (s := s'') (w :=  w1) (w' := w'); easy. }
                       rewrite H13 in Hf. rewrite apfend_an in Hf.
                       right. exists apf_end. exists w1. exists s''.
                       simpl. split. easy. split. easy. 
                       split. rewrite Ha5. 
                       apply InMergeF.
                       split. easy.
                       simpl.
                       rewrite orbtf. split. rewrite eqb_neq. easy. easy.
                       rewrite apfend_an. easy.
                   *** destruct Hin as (c,(Hc,(Hd,(He,Hf)))).
                       right. exists c. exists w1. exists s''.
                       split. easy. split. easy. 
                       split. rewrite Ha5.
                       apply InMergeF.
                       split. easy.
                       simpl.
                       rewrite orbtf. split. rewrite eqb_neq. easy. easy.
                       easy.
           * assert((ApnA3 a0 n) <> b).
             { apply apf_eqb_neq in H. easy. }
             assert(isInA (ApnA3 a0 n) s = false).
             { case_eq n; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             symmetry in H4.
             assert(merge_apf_cont b w' = merge_apf_cont b w') by easy.
             specialize(_39_2 (ApnA3 a0 n) b s s 
                   (merge_apf_cont b w')
                   (s & [|(s0, s', merge_apf_cont a1 (p & [|(l, s'', w1)|]))|]) w'
                   H3 H1 H2 H4 H9
                   ); intro Hin.
             destruct Hin as [Hin | Hin].
             ++ destruct Hin as (c,(Hc,(Hd,(He,Hf)))).
                assert(c = apf_end).
                { apply noPre with (p := s) (l := s0) (s := s') (w := merge_apf_cont a1 (p & [|(l, s'', w1)|])) (w' := w'); easy.
                }
                rewrite H10 in Hf.
                rewrite apfend_an in Hf.
                right.
                exists (apf_receive s s0 s' a1). exists w1. exists s''.
                split. simpl. rewrite Ha1.
                apply orbtf. split. rewrite eqb_neq. easy. easy.
                split. easy.
                split. rewrite He H10. simpl.
                assert(isInA (ApnA3 a0 n) s = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InN; easy.
                }
                rewrite InMerge. rewrite Ha3. simpl. easy.
                rewrite(st_eq(merge_apf_cont (apf_receive s s0 s' a1) (p & [|(l, s'', w1)|]))). simpl.
                easy.
             ++ destruct Hin as (c,(Hc,(Hd,(He,Hf)))).
                assert(w' =  merge_apf_cont (Apf_merge c (apf_receive s s0 s' a1)) (p & [|(l, s'', w1)|])).
                { rewrite Hf.
                  rewrite reOrg2.
                  easy.
                }
                rewrite He in Ha3.
                right.
                exists (Apf_merge c (apf_receive s s0 s' a1)). exists w1. exists s''.
                split.
                rewrite InMerge.
                apply InMergeF in Ha3.
                destruct Ha3 as (Ha3a,Ha3b).
                rewrite Ha3b. simpl.
                rewrite orbtf. split. rewrite eqb_neq. easy. easy.
                split. easy. split.
                apply InMergeF in Ha3. easy.
                easy.
                apply refinementR4_mon.
Qed.

(** TODO: drop lemmata for refinement4 *)


