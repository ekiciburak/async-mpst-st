Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local ST.subtyping.refinement.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.

Lemma Bp2ApSeq (b: Bpf) (H: isBpSend b = false): option Apf.
Proof. induction b; intros.
       - simpl in H.
         refine (
         match (IHb H) with
           | Some a => Some (apf_receive s s0 s1 a)
           | None   => None
         end
         ). 
       - exact None.
       - exact (Some apf_end).
Defined.

Fixpoint Ap2BpSeq (a: Apf): Bpf :=
  match a with
    | apf_receive q l s a' => bpf_receive q l s (Ap2BpSeq a')
    | apf_end              => bpf_end
  end.

Lemma Ap2Bp: forall a, exists b, b = Ap2BpSeq a.
Proof. intro a.
       exists (Ap2BpSeq a). easy.
Qed.

Lemma Bp2Ap: forall b, exists a, a = Bp2ApSeq b.
Proof. intro b.
       exists (Bp2ApSeq b). easy.
Qed.

Lemma Ap2BpSeq2: forall a b,
  Ap2BpSeq (Apf_merge a b) = Bpf_merge (Ap2BpSeq a) (Ap2BpSeq b).
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl. rewrite IHa. easy.
Qed.

Lemma BpApSeq: forall b, 
  isBpSend b = false ->
  exists a, b = Ap2BpSeq a.
Proof. intro b.
       induction b; intros.
       - simpl in H.
         specialize(IHb H).
         destruct IHb as (a, Ha).
         exists(apf_receive s s0 s1 a).
         simpl. rewrite Ha. easy.
       - simpl in H. easy.
       - exists apf_end. simpl. easy.
Qed.

Lemma mergel: forall a, Apf_merge a apf_end = a.
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl. rewrite IHa. easy.
Qed.

Lemma mergelb: forall b, Bpf_merge b bpf_end = b.
Proof. intro b.
       induction b; intros.
       - simpl. rewrite IHb. easy.
       - simpl. rewrite IHb. easy.
       - simpl. easy.
Qed.

Lemma ApnA3C: forall n a, ApnA3 a n.+1 =  Apf_merge a (ApnA3 a n).
Proof. intros.
       simpl.
       case_eq n; intros.
       - simpl. rewrite mergel. easy.
       - easy.
Qed.

Lemma BpnB3C: forall n b, BpnB3 b n.+1 =  Bpf_merge b (BpnB3 b n).
Proof. intros.
       simpl.
       case_eq n; intros.
       - simpl. rewrite mergelb. easy.
       - easy.
Qed.

Lemma apfend_an: forall w, merge_apf_cont apf_end w = w.
Proof. intros.
       case_eq w; intros.
       - rewrite(st_eq(merge_apf_cont apf_end (end))). simpl. easy.
       - rewrite(st_eq(merge_apf_cont apf_end (s & l) )). simpl. easy.
       - rewrite(st_eq(merge_apf_cont apf_end (s ! l))). simpl. easy.
Qed.

Lemma bpfend_bn: forall w, merge_bpf_cont bpf_end w = w.
Proof. intros.
       case_eq w; intros.
       - rewrite(st_eq(merge_bpf_cont bpf_end (end))). simpl. easy.
       - rewrite(st_eq(merge_bpf_cont bpf_end (s & l) )). simpl. easy.
       - rewrite(st_eq(merge_bpf_cont bpf_end (s ! l))). simpl. easy.
Qed.

Lemma meqApH: forall a b w,
  merge_apf_cont (Apf_merge a b) w = merge_apf_cont a (merge_apf_cont b w).
Proof. intro a.
       induction a; intros.
       - simpl. rewrite apfend_an. easy.
       - simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 (Apf_merge a b)) w)). simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (merge_apf_cont b w))). simpl.
         rewrite IHa. easy.
Qed.

Lemma meqBpH: forall a b w,
  merge_bpf_cont (Bpf_merge a b) w = merge_bpf_cont a (merge_bpf_cont b w).
Proof. intro a.
       induction a; intros.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Bpf_merge a b)) w)).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) (merge_bpf_cont b w))).
         simpl. rewrite IHa. easy.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 (Bpf_merge a b)) w)).
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) (merge_bpf_cont b w))).
         simpl. rewrite IHa. easy.
       - rewrite bpfend_bn. easy.
Qed.

Lemma meqAp3: forall n a w, merge_apf_cont (ApnA3 a n) w = merge_apf_contn a w n.
Proof. intro n.
       induction n; intros.
       - simpl. rewrite apfend_an. easy.
       - rewrite ApnA3C.
         rewrite meqApH. rewrite IHn.
         simpl. easy.
Qed.

Lemma meqBp3: forall n a w, merge_bpf_cont (BpnB3 a n) w = merge_bpf_contn a w n.
Proof. intro n.
       induction n; intros.
       - simpl. rewrite bpfend_bn. easy.
       - rewrite BpnB3C.
         rewrite meqBpH. rewrite IHn.
         simpl. easy.
Qed.

Lemma orbtf: forall b1 b2 : bool, b1 || b2 = false <-> b1 = false /\ b2 = false.
Proof. intro b1.
       case_eq b1; intros.
       - simpl. split; easy.
       - case_eq b2; intros.
         + split; easy.
         + split; easy.
Defined.

Lemma bpfend_an: forall w, merge_bpf_cont bpf_end w = w.
Proof. intros.
       case_eq w; intros.
       - rewrite(st_eq(merge_bpf_cont bpf_end (end))). simpl. easy.
       - rewrite(st_eq(merge_bpf_cont bpf_end (s & l) )). simpl. easy.
       - rewrite(st_eq(merge_bpf_cont bpf_end (s ! l))). simpl. easy.
Qed.

Lemma mcAp2Bp: forall a w, 
  exists b, 
  merge_apf_cont a w = merge_bpf_cont b w.
Proof. intro a.
       induction a; intros.
       - exists bpf_end.
         rewrite apfend_an.
         rewrite bpfend_bn.
         easy.
       - specialize(IHa w).
         destruct IHa as (b, IHa).
         exists(bpf_receive s s0 s1 b).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)).
         simpl. rewrite IHa.
         easy.
Qed.

Lemma mcAp2Bp2: forall a w, 
  merge_apf_cont a w = merge_bpf_cont (Ap2BpSeq a) w.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an.
         rewrite bpfend_bn.
         easy.
       - specialize(IHa w).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Ap2BpSeq a)) w)).
         simpl. rewrite IHa.
         easy.
Qed.


Lemma mcBp2Ap: forall b w, 
  isBpSend b = false ->
  exists a, merge_bpf_cont b w = merge_apf_cont a w /\ b = Ap2BpSeq a.
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
         specialize(IHb w H).
         destruct IHb as (a, (IHb,HH)).
         exists (apf_receive s s0 s1 a). split. rewrite IHb. 
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         easy. simpl. rewrite HH. easy.
       - simpl in H. easy.
       - exists apf_end. rewrite apfend_an. rewrite bpfend_bn. easy.
Qed.


Lemma eqbs_eq: forall s1 s2, eqbs s1 s2 = true <-> s1 = s2.
Proof. intro s1.
       induction s1; intros.
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.       
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.
Qed.

Lemma eqbs_neq: forall s1 s2, eqbs s1 s2 = false <-> s1 <> s2.
Proof. intro s1.
       induction s1; intros.
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.       
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.
       - case_eq s2; intros.
         + subst. easy.
         + subst. easy.
         + subst. easy.
         + subst. easy.
Qed.

Lemma eqbs_refl: forall s, eqbs s s = true.
Proof. intro s.
       destruct s; intros; easy.
Qed.

Lemma apf_eqb_eq: forall a b, Apf_eqb a b <-> a = b.
Proof. intro a.
       induction a; intros.
       - case_eq b; intros.
         + simpl. easy.
         + subst. simpl. easy.
       - simpl.
         case_eq b; intros.
         + subst. easy.
         + subst. split.
           intros.
           apply Bool.andb_true_iff in H.
           destruct H as (Ha,Hb).
           apply Bool.andb_true_iff in Ha.
           destruct Ha as (Ha,Hc).
           apply Bool.andb_true_iff in Ha.
           destruct Ha as (Ha,Hd).
           rewrite eqb_eq in Ha.
           rewrite eqb_eq in Hd.
           rewrite eqbs_eq in Hc.
           apply IHa in Hb.
           subst. easy.
           intros.
           inversion H. subst.
           apply Bool.andb_true_iff. split.
           apply Bool.andb_true_iff. split.
           apply Bool.andb_true_iff. split.
           rewrite eqb_eq. easy.
           rewrite eqb_eq. easy.
           rewrite eqbs_eq. easy.
           apply IHa. easy.
Qed.

Lemma bpf_eqb_eq: forall a b, Bpf_eqb a b <-> a = b.
Proof. intro a.
       induction a; intros.
       - case_eq b; intros.
         + subst. simpl.
           case_eq(eqb s s2); intros.
           ++ rewrite eqb_eq in H. subst.
              case_eq(eqb s0 s3); intros.
              +++ rewrite eqb_eq in H. subst.
                  case_eq(eqbs s1 s4); intros.
                  * rewrite eqbs_eq in H. subst.
                     simpl. rewrite IHa.
                     split. intro Ha. subst. easy.
                     intro Ha. inversion Ha. easy.
                  * simpl. split. intro Ha. easy.
                    rewrite eqbs_neq in H.
                    intro Ha. inversion Ha. subst. easy.
              +++ simpl. split. intro Ha. easy.
                  rewrite eqb_neq in H.
                  intro Ha. inversion Ha. subst. easy.
           ++ simpl. split. intro Ha. easy.
              rewrite eqb_neq in H.
              intro Ha. inversion Ha. subst. easy.
         + simpl. split. intro Ha. easy.
           intro Ha. easy.
         + simpl. easy.
       - case_eq b; intros.
         + simpl. split. intro Ha. easy.
           intro Ha. easy.
         + simpl.
           case_eq(eqb s s2); intros.
           ++ rewrite eqb_eq in H0. subst.
              case_eq(eqb s0 s3); intros.
              +++ rewrite eqb_eq in H. subst.
                  case_eq(eqbs s1 s4); intros.
                  * rewrite eqbs_eq in H. subst.
                     simpl. rewrite IHa.
                     split. intro Ha. subst. easy.
                     intro Ha. inversion Ha. easy.
                  * simpl. split. intro Ha. easy.
                    rewrite eqbs_neq in H.
                    intro Ha. inversion Ha. subst. easy.
              +++ simpl. split. intro Ha. easy.
                  rewrite eqb_neq in H.
                  intro Ha. inversion Ha. subst. easy.
           ++ simpl. split. intro Ha. easy.
              rewrite eqb_neq in H0.
              intro Ha. inversion Ha. subst. easy.
         + simpl. easy.
         + case_eq b; intros; easy.
Qed.

Lemma apf_eqb_neq: forall a b, Apf_eqb a b = false <-> a <> b.
Proof. intro a.
       induction a; intros.
       - case_eq b; intros.
         + simpl. easy.
         + subst. simpl. easy.
       - simpl.
         case_eq b; intros.
         + subst. easy.
         + subst. split.
           intros.
           apply Bool.andb_false_iff in H.
           destruct H as [H | H].
           ++ apply Bool.andb_false_iff in H.
              destruct H as [H | H].
              +++ apply Bool.andb_false_iff in H.
                  destruct H as [H | H].
                  * rewrite eqb_neq in H.
                    unfold not. intro Ha.
                    apply H. inversion Ha. easy.
                  * rewrite eqb_neq in H.
                    unfold not. intro Ha.
                    apply H. inversion Ha. easy.
              +++ rewrite eqbs_neq in H.
                  unfold not. intro Ha.
                  apply H. inversion Ha. easy.
           ++ apply IHa in H.
              unfold not. intro Ha.
              apply H. inversion Ha. easy.
       intros.
       case_eq(eqb s s2); intros.
       + rewrite eqb_eq in H0. subst.
         simpl.
         case_eq(eqb s0 s3); intros.
         ++ rewrite eqb_eq in H0. subst.
            case_eq(eqbs s1 s4); intros.
            +++ rewrite eqbs_eq in H0. subst.
                simpl. apply IHa.
                unfold not. intro Ha.
                apply H. subst. easy.
            +++ simpl. easy.
         ++ simpl. easy.
       + simpl. easy. 
Qed.

Lemma bpf_eqb_neq: forall a b, Bpf_eqb a b = false <-> a <> b.
Proof. intro a.
       induction a; intros.
       - case_eq b; intros.
         + simpl.
           case_eq(eqb s s2); intros.
           ++ rewrite eqb_eq in H0. subst.
              case_eq(eqb s0 s3); intros.
              +++ rewrite eqb_eq in H. subst.
                  case_eq(eqbs s1 s4); intros.
                  * rewrite eqbs_eq in H. subst.
                     simpl. rewrite IHa.
                     split. intro Ha. subst. unfold not.
                     intro Hb. inversion Hb. subst. easy.
                  * simpl. intro Ha. unfold not.
                    intro Hb. apply Ha. subst. easy.
              +++ simpl. split. intro Ha.
                  rewrite eqbs_neq in H. unfold not.
                  intro Hb. inversion Hb. subst. easy.
           ++ simpl. intro Ha. easy.
              rewrite eqb_neq in H. simpl. split.
              intro Ha. unfold not. intro Hb. inversion Hb. subst. easy.
              intro Ha. easy.
              simpl.
              split. intro Ha.
              rewrite eqb_neq in H0.
              unfold not. intro Hb.
              inversion Hb. subst. easy.
              easy.
         + simpl. easy.
         + simpl. easy.
       - case_eq b; intros.
         + simpl. easy.
         + simpl.
           case_eq(eqb s s2); intros.
           ++ rewrite eqb_eq in H0. subst.
              case_eq(eqb s0 s3); intros.
              +++ rewrite eqb_eq in H. subst.
                  case_eq(eqbs s1 s4); intros.
                  * rewrite eqbs_eq in H. subst.
                     simpl. rewrite IHa.
                     split. intro Ha. subst. unfold not.
                     intro Hb. inversion Hb. subst. easy.
                  * simpl. intro Ha. unfold not.
                    intro Hb. apply Ha. subst. easy.
              +++ simpl. split. intro Ha.
                  rewrite eqbs_neq in H. unfold not.
                  intro Hb. inversion Hb. subst. easy.
           ++ simpl. intro Ha. easy.
              rewrite eqb_neq in H. simpl. split.
              intro Ha. unfold not. intro Hb. inversion Hb. subst. easy.
              intro Ha. easy.
              simpl.
              split. intro Ha.
              rewrite eqb_neq in H0.
              unfold not. intro Hb.
              inversion Hb. subst. easy.
              easy.
         + simpl. easy.
         + case_eq b; simpl; easy.
Qed.

Lemma _39_1: forall a b p q w w1 w2,
  isInB a p = false ->
  isInB b q = false ->
  a <> b ->
  w = merge_bpf_cont a w1 ->
  w = merge_bpf_cont b w2 ->
  (
    (exists c, isInB c q = false /\
      w = merge_bpf_cont a (merge_bpf_cont c w2) /\ b = Bpf_merge a c /\ w1 = merge_bpf_cont c w2)
    \/
    (exists c, isInB c p = false /\
      w = merge_bpf_cont b (merge_bpf_cont c w1) /\ a = Bpf_merge b c /\ w2 = merge_bpf_cont c w1)
  ).
Proof. intro a.
       induction a; intros.
       - case_eq b; intros.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) w1)) in H3.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 b0) w2)) in H3. simpl in H3.
           inversion H3. subst.
           simpl in H.
           simpl in H0.
           assert(a <> b0).
           { unfold not. intros. subst. easy. }
           assert(merge_bpf_cont a w1 = merge_bpf_cont a w1) by easy.
           specialize(IHa b0 p q (merge_bpf_cont a w1) w1 w2 H H0 H2 H4 H7).
           destruct IHa as [IHa | IHa].
           ++ destruct IHa as (c,IHa).
              left. exists c.
              destruct IHa as (Ha,(Hb,(Hc,Hd))).
              split. easy.
              split.
              rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 a) (merge_bpf_cont c w2))). simpl.
              rewrite Hb. easy.
              split. rewrite Hc. easy.
              easy.
           ++ destruct IHa as (c,IHa).
              right. exists c.
              destruct IHa as (Ha,(Hb,(Hc,Hd))).
              split. easy.
              split.
              rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 b0) (merge_bpf_cont c w1))). simpl.
              rewrite Hb. easy.
              split. rewrite Hc. easy.
              easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) w1)) in H3.
           rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 b0) w2)) in H3. simpl in H3.
           easy.
         + subst. 
           rewrite bpfend_an in H3. simpl in H3.
           simpl in H.
           right. exists(bpf_receive s s0 s1 a).
           split. easy.
           split. rewrite bpfend_an. easy.
           split. simpl. easy.
           easy.
       - case_eq b; intros.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) w1)) in H3.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 b0) w2)) in H3.
           simpl in H3. easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) w1)) in H3.
           rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 b0) w2)) in H3. 
           simpl in H3.
           inversion H3. subst.
           simpl in H. 
           rewrite orbtf in H.
           destruct H as (Ha,Hb).
           simpl in H0.
           rewrite orbtf in H0.
           destruct H0 as (Hc,Hd).
           assert(a <> b0).
           { unfold not. intros. subst. easy. }
           assert(merge_bpf_cont a w1 = merge_bpf_cont a w1) by easy.
           specialize(IHa b0 p q (merge_bpf_cont a w1) w1 w2 Hb Hd H H0 H7).
           destruct IHa as [IHa | IHa].
           ++ destruct IHa as (c,IHa).
              left. exists c.
              destruct IHa as (He,(Hf,(Hg,Hi))).
              split. easy.
              split. 
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 a) (merge_bpf_cont c w2))).
              simpl.
              rewrite Hf. easy.
              split. simpl. rewrite Hg. easy.
              easy.
           ++ destruct IHa as (c,IHa).
              right. exists c.
              destruct IHa as (He,(Hf,(Hg,Hi))).
              split. easy.
              split. 
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 b0) (merge_bpf_cont c w1))).
              simpl.
              rewrite Hf. easy.
              split. simpl. rewrite Hg. easy.
              easy.
         + subst.
           right. exists(bpf_send s s0 s1 a).
           split. easy.
           split. rewrite bpfend_an. easy.
           split. simpl. easy.
           rewrite bpfend_an in H3. easy.
       - rewrite bpfend_an in H2.
         case_eq b; intros.
         + subst.
           left. exists(bpf_receive s s0 s1 b0).
           split. easy.
           split. rewrite bpfend_an. easy.
           split. simpl. easy.
           easy.
         + subst.
           left. exists(bpf_send s s0 s1 b0).
           split. easy.
           split. rewrite bpfend_an. easy.
           split. simpl. easy.
           easy.
         + subst. easy.
Qed.

Lemma _39_2: forall a b p q w w1 w2,
  isInA a p = false ->
  isInA b q = false ->
  a <> b ->
  w = merge_apf_cont a w1 ->
  w = merge_apf_cont b w2 ->
  (
    (exists c, isInA c q = false /\
      w = merge_apf_cont a (merge_apf_cont c w2) /\ b = Apf_merge a c /\ w1 = merge_apf_cont c w2)
    \/
    (exists c, isInA c p = false /\
      w = merge_apf_cont b (merge_apf_cont c w1) /\ a = Apf_merge b c /\ w2 = merge_apf_cont c w1)
  ).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H2.
         case_eq b; intros.
         + subst. easy.
         + subst. simpl in H0.
           left. exists (apf_receive s s0 s1 a).
           simpl.
           split. easy.
           split. rewrite !apfend_an. easy.
           split. easy.
           easy.
       - case_eq b; intros.
         + subst.
           right. exists(apf_receive s s0 s1 a).
           simpl. split. simpl in H. easy.
           split. rewrite apfend_an. easy.
           split. easy.
           rewrite apfend_an in H3.
           easy.
         + subst. 
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w1)) in H3.
           rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) w2)) in H3.
           simpl in H3.
           inversion H3. subst.
           specialize(IHa a0 p q (merge_apf_cont a w1) w1 w2).
           simpl in H, H0.
           rewrite orbtf in H0.
           rewrite orbtf in H.
           destruct H0 as (Ha,Hb).
           destruct H as (Hc,Hd).
           specialize(IHa Hd Hb).
           assert(a <> a0).
           { unfold not. intros. subst. easy. }
           assert(merge_apf_cont a w1 = merge_apf_cont a w1) by easy.
           specialize(IHa H H0 H7).
           destruct IHa as [IHa | IHa].
           ++ destruct IHa as (c, IHa).
              left. exists c. split. easy.
              destruct IHa as (Hf,(Hg,(Hi,Hj))).
              split.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a) w1)). simpl.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a) (merge_apf_cont c w2))). simpl.
              rewrite Hg. easy.
              split. simpl. rewrite Hi. easy.
              easy.
           ++ destruct IHa as (c, IHa).
              right. exists c.
              split. easy.
              destruct IHa as (Hf,(Hg,(Hi,Hj))).
              split.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a) w1)). simpl.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) (merge_apf_cont c w1))). simpl.
              rewrite Hg. easy.
              split. simpl. rewrite Hi. easy.
              easy.
Qed.

Lemma _39_3: forall b a p w w1 w2,
  isInB b p = false ->
  w = merge_bpf_cont b w1 ->
  w = merge_apf_cont a w2 ->
  isBpSend b = true ->
  (exists c,
   isInB c p = false /\
   w = merge_bpf_cont (Ap2BpSeq a) (merge_bpf_cont c w1) /\ b = Bpf_merge (Ap2BpSeq a) c /\ w2 = merge_bpf_cont c w1).
Proof. intro b.
       induction b; intros.
       - case_eq a; intros.
         + subst. rewrite apfend_an in H1.
           simpl in H. simpl. 
           exists(bpf_receive s s0 s1 b).
           split. simpl. easy. rewrite bpfend_an. easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w1)) in H1.
           rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) w2)) in H1.
           simpl in H1.
           inversion H1. subst.
           simpl.
           specialize(IHb a0 p (merge_bpf_cont b w1) w1 w2).
           simpl in H. simpl in H2.
(*            rewrite orbtf in H0.
           destruct H0 as (Ha, Hb). *)
           assert(merge_bpf_cont b w1 = merge_bpf_cont b w1) by easy.
(*            simpl in H3. *)
           specialize(IHb H H0 H6 H2).
           destruct IHb as (c,IHb).
           exists c.
           destruct IHb as (Hc,(Hd,(He,Hf))).
           split. easy.
           split. rewrite He. 
           rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 (Bpf_merge (Ap2BpSeq a0) c)) w1)). simpl.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 (Ap2BpSeq a0)) (merge_bpf_cont c w1))). simpl.
           rewrite <- Hd.
           rewrite He. easy.
           split. rewrite He. easy.
           easy.
       - case_eq a; intros.
         + subst. simpl.
           exists (bpf_send s s0 s1 b).
           split. simpl. simpl in H. easy. 
           split. rewrite bpfend_an. easy.
           split. easy. 
           rewrite apfend_an in H1. easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w1)) in H1.
           rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) w2)) in H1.
           simpl in H2. easy.
       - simpl in H2. easy.
Qed.

Lemma _39_4: forall a b p l s w w1 w2,
  a <> b ->
  w = merge_apf_cont a w1 ->
  w = merge_apf_cont b (p ! [(l, s, w2)]) ->
  exists c, b = Apf_merge a c /\ w1 = merge_apf_cont c (p ! [(l, s, w2)]).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         exists b. split. simpl. easy.
         rewrite <- H0. easy.
       - simpl.
         case_eq b; intros.
         + subst. 
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w1)) in H1. simpl in H1.
           rewrite apfend_an in H1. easy.
         + subst. 
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w1)) in H1.
           rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a0) (p ! [(l, s2, w2)]))) in H1.
           simpl in H1. inversion H1.
           subst.
           assert(a <> a0).
           { unfold not. intro Ha. apply H. subst. easy. }
           assert(merge_apf_cont a w1 = merge_apf_cont a w1) by easy.
           specialize(IHa a0 p l s2 (merge_apf_cont a w1) w1 w2 H0 H2 H5).
           destruct IHa as (c,(Ha1,Ha2)).
           exists c. split. rewrite Ha1. easy. easy.
Qed.

Lemma pneqq3: forall a p q l l' s s' w w' (H: p <> q),
  q & [(l, s, w)] = merge_apf_cont a (p & [(l', s', w')]) ->
  exists a', 
  w = merge_apf_cont a' (p & [(l', s', w')]) /\ a = apf_receive q l s a'.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         inversion H0. subst. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l', s', w')]))) in H0.
         simpl in H0.
         inversion H0. subst.
         exists a. split; easy.
Qed.

Lemma pneqq4: forall a p q l l' s s' w w' (H: p <> q),
  isInA a p = false ->
  q & [(l, s, w)] = merge_apf_cont a (p & [(l', s', w')]) ->
  exists a', isInA a' p = false /\ w = merge_apf_cont a' (p & [(l', s', w')]) /\ a = apf_receive q l s a'.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H1.
         inversion H1. subst. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l', s', w')]))) in H1.
         simpl in H1.
         inversion H1. subst.
         exists a. split.
         simpl in H0. rewrite orbtf in H0. easy.
         split; easy.
Qed.

(* Lemma pneqq4a: forall a p q l l' s s' w w',
  isInA a p = false ->
  q & [(l, s, w)] = merge_apf_cont a (p & [(l', s', w')]) ->
  exists a', isInA a' p = false /\ w = merge_apf_cont a' (p & [(l', s', w')]) /\ a = apf_receive q l s a'.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         inversion H0. subst.
         
          easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l', s', w')]))) in H1.
         simpl in H1.
         inversion H1. subst.
         exists a. split.
         simpl in H0. rewrite orbtf in H0. easy.
         split; easy.
Qed. *)


Lemma pneqq5: forall b p q l l' s s' w w' (H: p <> q),
  isInB b p = false ->
  q & [(l, s, w)] = merge_bpf_cont b (p ! [(l', s', w')]) ->
  exists b', isInB b' p = false /\ w = merge_bpf_cont b' (p ! [(l', s', w')]) /\ b = bpf_receive q l s b'.
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l', s', w')]))) in H1.
         simpl in H1.
         inversion H1. subst.
         simpl in H0.
         exists b. split. easy. split. easy. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l', s', w')]))) in H1.
         simpl in H1. easy.
       - rewrite bpfend_bn in H1. easy.
Qed.

Lemma pneqq6: forall b p q l l' s s' w w',
  isInB b p = false ->
  q & [(l, s, w)] = merge_bpf_cont b (p ! [(l', s', w')]) ->
  exists b', isInB b' p = false /\ w = merge_bpf_cont b' (p ! [(l', s', w')]) /\ b = bpf_receive q l s b'.
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l', s', w')]))) in H0.
         simpl in H0.
         inversion H0. subst.
         simpl in H.
         exists b. split. easy. split. easy. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l', s', w')]))) in H0.
         simpl in H0. easy.
       - rewrite bpfend_bn in H0. easy.
Qed.

Lemma pneqq7: forall b p q l l' s s' w w',
  p <> q ->
  isInB b p = false ->
  q ! [(l, s, w)] = merge_bpf_cont b (p ! [(l', s', w')]) ->
  exists b', isInB b' p = false /\ w = merge_bpf_cont b' (p ! [(l', s', w')]) /\ b = bpf_send q l s b'.
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l', s', w')]))) in H1.
         simpl in H1.
         inversion H1. subst.
         simpl in H0.
         exists b. split.
         rewrite orbtf in H0. easy. split.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l', s', w')]))) in H1. simpl in H1.
         inversion H1. 
         easy.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l', s', w')]))) in H1. simpl in H1.
         inversion H1. 
         easy.
       - rewrite bpfend_bn in H1.
         inversion H1. subst.
         easy.
Qed.

Lemma merge_same_aeq: forall a w w',
  merge_apf_cont a w = merge_apf_cont a w' -> w = w'.
Proof. intro a.
       induction a; intros.
       - rewrite !apfend_an in H. easy.
       - apply IHa.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)) in H.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w')) in H.
         simpl in H. inversion H. easy.
Qed.

Lemma merge_same_beq: forall a w w',
  merge_bpf_cont a w = merge_bpf_cont a w' -> w = w'.
Proof. intro a.
       induction a; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) w)) in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) w')) in H.
         simpl in H. inversion H. apply IHa. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) w)) in H.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) w')) in H.
         simpl in H. inversion H. apply IHa. easy.
       - rewrite !bpfend_bn in H. easy.
Qed.

Lemma inH0: forall a p l s w, coseqInl (p, rcv, l) (actl (merge_apf_cont a (p & [(l, s, w)]))).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an.
         rewrite(coseq_eq(actl (p & [(l, s, w)]))). unfold coseq_id. simpl.
         apply CoInSplit1l with (y := (p, rcv, l)) (ys := actl w).
         simpl. easy. easy.
       - rewrite(st_eq( (merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)])))). simpl.
         case_eq (eqb p s); intros.
         + rewrite eqb_eq in H.
           case_eq (eqb l s0); intros.
           ++ rewrite eqb_eq in H0.
              subst.
              rewrite(coseq_eq (actl (s & [(s0, s1, merge_apf_cont a (s & [(s0, s2, w)]))]))). unfold coseq_id. simpl.
              apply CoInSplit1l with (y := (s, rcv, s0)) (ys :=  (actl (merge_apf_cont a (s & [(s0, s2, w)])))).
              simpl. easy. easy.
           ++ rewrite eqb_neq in H0.
              apply CoInSplit2l with (y := (s, rcv, s0)) (ys :=  (actl (merge_apf_cont a (p & [(l, s2, w)])))).
              simpl. easy. subst.
              unfold not. intros. apply H0. inversion H. easy.
           apply IHa.
         + rewrite eqb_neq in H.
           rewrite(coseq_eq(actl (s & [(s0, s1, merge_apf_cont a (p & [(l, s2, w)]))]))). unfold coseq_id. simpl.
           apply CoInSplit2l with (y := (s, rcv, s0)) (ys := (actl (merge_apf_cont a (p & [(l, s2, w)])))).
           simpl. easy.
           unfold not. intros. apply H. inversion H0. easy.
           apply IHa.
Qed.

Lemma inH4: forall a b p l s w w',
  a <> b ->
  isInA a p = false ->
  isInA b p = true ->
  merge_apf_cont a (p & [(l, s, w)]) = merge_apf_cont b w' ->
  exists a1, b = Apf_merge a (apf_receive p l s a1) /\ w = merge_apf_cont a1 w'.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H2.
         simpl.
         case_eq b; intros.
         + subst. simpl in H1. easy.
         + subst. simpl in H1.
           rewrite Bool.orb_true_iff in H1.
           destruct H1 as [H1 | H1].
           * rewrite eqb_eq in H1. subst.
             rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a) w')) in H2. simpl in H2.
             inversion H2. subst.
             exists a. easy.
           * rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a) w')) in H2. simpl in H2.
             inversion H2. subst. exists a. easy.
       - simpl in H0.
         rewrite orbtf in H0.
         destruct H0 as (Ha, Hb).
         rewrite eqb_neq in Ha.
         simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H2. simpl in H2.
         case_eq b; intros.
         + subst. simpl in H1. easy.
         + subst. simpl in H. simpl in H1.
           rewrite Bool.orb_true_iff in H1.
           destruct H1 as [H1 | H1].
           * rewrite eqb_eq in H1. subst.
             rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a0) w')) in H2. simpl in H2.
             inversion H2. subst.
             easy.
           * rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a0) w')) in H2. simpl in H2.
             inversion H2. subst.
             assert(a <> a0).
             { unfold not. intros. apply H. subst. easy. }
             specialize(IHa a0 p l s2 w w' H0 Hb H1 H6).
             destruct IHa as (a1,(Ha1,Ha2)).
             exists a1. split. rewrite Ha1. easy. easy.
Qed.

Lemma inH5: forall a1 a2 b c p l s,
  isInA a1 p = false ->
  isInA b p ->
  Apf_merge a1 (apf_receive p l s a2) = Apf_merge b c ->
  exists a3, b = Apf_merge a1 (apf_receive p l s a3) /\ a2 = Apf_merge a3 c.
Proof. intro a1.
       induction a1; intros.
       - simpl in H1.
         case_eq b; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. simpl in H1.
           inversion H1. subst. simpl.
           exists a. split. easy. easy.
       - simpl in H. simpl in H1.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         case_eq b; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. simpl in H1.
           inversion H1. subst.
           rewrite Ha in H0. simpl in H0.
           specialize(IHa1 a2 a c p l s2 Hb H0 H5).
           destruct IHa1 as (a3,(Ha3,Ha4)).
           rewrite Ha3.
           simpl.
           exists a3. split. easy. easy.
Qed.

Lemma inH5B: forall a1 a2 b c p l s,
  isInB a1 p = false ->
  isInB b p ->
  Bpf_merge a1 (bpf_send p l s a2) = Bpf_merge b c ->
  exists a3, b = Bpf_merge a1 (bpf_send p l s a3) /\ a2 = Bpf_merge a3 c.
Proof. intro a1.
       induction a1; intros.
       - simpl in H1. simpl in H.
         case_eq b; intros.
         + subst. simpl in H0.
           simpl in H1.
           inversion H1. subst. simpl.
           apply IHa1 in H6; try easy.
           destruct H6 as (a3,(Ha1,Ha2)).
           exists a3. rewrite Ha1. rewrite Ha2. split; easy.
         + subst.
           simpl in H0. simpl in H1.
           inversion H1.
         + subst. simpl in H0. easy.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha,Hb).
         simpl in H1.
         case_eq b; intros.
         + subst. simpl in H1. inversion H1.
         + subst. simpl in H1.
           inversion H1. subst. simpl in H0.
           rewrite Ha in H0. simpl in H0.
           apply IHa1 in H5; try easy.
           destruct H5 as (a3,(Ha1,Ha2)).
           simpl. rewrite Ha1 Ha2.
           exists a3. split; easy.
         + subst. simpl in H0. easy.
       - simpl in H1. simpl.
         case_eq b; intros.
         + subst. simpl in H1. easy.
         + subst. simpl in H1. inversion H1.
           subst. exists b0. split; easy.
         + subst. simpl in H0. easy.
Qed.

Lemma inH6: forall a1 a2 b c p l s,
  isInA a1 p = false ->
  isInA b p = false ->
  Apf_merge a1 (apf_receive p l s a2) = Apf_merge b c ->
  exists a3, isInA a3 p = false /\ c = Apf_merge a3 (apf_receive p l s a2) /\ a1 = Apf_merge b a3.
Proof. intro a1.
       induction a1; intros.
       - simpl in H1.
         case_eq b; intros.
         + subst. simpl in H1. 
           exists apf_end. split. easy. simpl. split. easy. easy.
         + subst. simpl in H0. simpl in H1.
           inversion H1. subst. simpl.
           rewrite orbtf in H0.
           destruct H0 as (Ha,Hb).
           rewrite eqb_refl in Ha. easy.
       - simpl in H. simpl in H1.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         case_eq b; intros.
         + subst. simpl in H1. simpl.
           exists (apf_receive s s0 s1 a1).
           split. simpl. rewrite Ha. rewrite Hb. easy.
           split. simpl. easy. easy.
         + subst. simpl in H0. simpl in H1.
           inversion H1. subst.
           rewrite Ha in H0. simpl in H0.
           specialize(IHa1 a2 a c p l s2 Hb H0 H5).
           destruct IHa1 as (a3,(Ha3,(Ha4,Ha5))).
           exists a3.
           rewrite Ha3.
           simpl. split. easy. split. easy. rewrite Ha5. easy.
Qed.

Lemma inH6B: forall a1 a2 b c p l s,
  isInB a1 p = false ->
  isInB b p = false ->
  Bpf_merge a1 (bpf_send p l s a2) = Bpf_merge b c ->
  exists a3, isInB a3 p = false /\ c = Bpf_merge a3 (bpf_send p l s a2) /\ a1 = Bpf_merge b a3.
Proof. intro a1.
       induction a1; intros.
       - case_eq b; intros.
         + subst. simpl in H. simpl in H0.
           simpl in H1.
           inversion H1. subst.
           apply IHa1 in H6; try easy.
           destruct H6 as (a3,(Ha1,(Ha2,Ha3))).
           exists a3. simpl. rewrite Ha3. split; easy.
         + subst. simpl in H1. easy.
         + subst. simpl in H1.
           simpl in H.
           exists(bpf_receive s s0 s1 a1).
           split. simpl. easy. simpl. split; easy.
       - simpl in H.
         simpl in H1.
         case_eq b; intros.
         + subst. simpl in H1. easy.
         + subst. simpl in H1. inversion H1. subst.
           simpl in H0.
           rewrite orbtf in H.
           rewrite orbtf in H0.
           destruct H as (Ha,Hb).
           destruct H0 as (Hc,Hd).
           apply IHa1 in H6; try easy.
           destruct H6 as (a3,(Ha1,(Ha2,Ha3))).
           exists a3. rewrite Ha3. simpl. split; easy.
         + subst. simpl in H1.
           exists(bpf_send s s0 s1 a1). simpl.
           split; easy.
       - case_eq b; intros.
         + subst. simpl in H0.
           simpl in H1. easy.
         + subst. simpl in H1. simpl in H0.
           inversion H1. subst.
           rewrite eqb_refl in H0. easy.
         + subst. simpl in H1. 
           exists bpf_end. simpl. split; easy.
Qed.

Lemma inH7: forall b a p l s w w',
  isInB b p = false ->
  merge_bpf_cont b (p ! [(l, s, w)]) = merge_apf_cont a w' ->
  exists c, isInB c p = false /\ b = Bpf_merge (Ap2BpSeq a) c /\ w' = merge_bpf_cont c (p ! [(l, s, w)]).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))) in H0. simpl in H0.
         case_eq a; intros.
         + subst. rewrite apfend_an in H0.
           simpl.
           exists(bpf_receive s s0 s1 b). split.
           simpl. easy.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
           easy.
         + subst. simpl in H.
           rewrite(st_eq( merge_apf_cont (apf_receive s3 s4 s5 a0) w')) in H0. simpl in H0.
           inversion H0. subst.
           simpl.
           specialize(IHb a0 p l s2 w w' H H5).
           destruct IHb as (c,(IHb1,(IHb2,IHb3))).
           exists c. rewrite IHb1. split. easy. split. rewrite IHb2. easy. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H0. simpl in H0.
         case_eq a; intros.
         + subst. rewrite apfend_an in H0. simpl.
           exists(bpf_send s s0 s1 b). split. easy. split. easy.  
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
           easy.
         + subst.
           rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a0) w')) in H0. simpl in H0.
           easy.
       - rewrite bpfend_bn in H0.
         case_eq a; intros.
         + subst.
           rewrite apfend_an in H0.
           exists bpf_end. simpl. split. easy. rewrite bpfend_bn. easy.
         + subst. 
           rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 a0) w')) in H0. simpl in H0.
           easy.
Qed.

Lemma inH8: forall a b p w w',
  isInB a p  = false ->
  isInB b p = true ->
  merge_bpf_cont a w = merge_bpf_cont b w' ->
  exists c, isInB c p = true /\ b = Bpf_merge a c /\ w = merge_bpf_cont c w'.
Proof. intro a.
       induction a; intros.
       - simpl in H.
         case_eq b; intros.
         + subst. simpl in H0.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) w)) in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 b0) w')) in H1. simpl in H1.
           inversion H1. subst.
           simpl.
           specialize(IHa b0 p w w' H H0 H6).
           destruct IHa as (c,(Hc1,(Hc2,Hc3))).
           exists c. split. easy. rewrite Hc2. easy.
         + subst. 
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) w)) in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 b0) w')) in H1. simpl in H1. easy.
         + subst. simpl in H0. easy.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         case_eq b; intros.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) w)) in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 b0) w')) in H1. simpl in H1. easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) w)) in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 b0) w')) in H1. simpl in H1.
           inversion H1. subst.
           simpl in H0.
           rewrite Ha in H0.
           simpl in H0.
           specialize(IHa b0 p w w' Hb H0 H5).
           destruct IHa as (c,(Hc1,(Hc2,Hc3))).
           exists c. split. easy. rewrite Hc2. easy.
         + subst. simpl in H0. easy.
       - rewrite bpfend_bn in H1.
         exists b. split. easy. split. simpl. easy. easy.
Qed.

Lemma InMergeF: forall a b p,
  isInA (Apf_merge a b) p = false <->
  isInA a p = false /\ isInA b p = false.
Proof. split.
       revert b p.
       induction a; intros.
       - simpl in H. simpl. rewrite H. easy.
       - simpl in H. simpl.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite Ha. simpl.
         apply IHa. easy.

       revert p b.
       induction a; intros.
       - simpl in H. simpl. easy.
       - simpl in H. simpl.
         destruct H as (Ha, Hb).
         rewrite orbtf in Ha.
         rewrite orbtf.
         split. easy.
         apply IHa. split; easy.
Qed.

Lemma InMergeFS: forall a b p,
  isInB (Bpf_merge a b) p = false <->
  isInB a p = false /\ isInB b p = false.
Proof. split.
       intro Ha.
       induction a; intros.
       - simpl. simpl in Ha.
         apply IHa in Ha. easy.
       - simpl. simpl in Ha.
         rewrite orbtf in Ha.
         destruct Ha as (Ha, Hb).
         rewrite Ha. simpl. apply IHa. easy.
       - simpl in Ha. rewrite Ha. simpl. easy.
       intro Ha.
       induction a; intros.
       - simpl. simpl in Ha.
         apply IHa in Ha. easy.
       - simpl. simpl in Ha.
         rewrite orbtf in Ha.
         destruct Ha as ((Ha,Hb),Hc).
         rewrite Ha. simpl. apply IHa. easy.
       - simpl. easy.
Qed.

Lemma isInDec: forall a p, isInA a p = false \/ isInA a p.
Proof. intro a.
       induction a; intros.
       - simpl. left. easy.
       - simpl.
         case_eq(eqb p s); intros.
         + simpl. right. easy.
         + simpl. easy.
Qed.

Lemma isInDecS: forall a p, isInB a p = false \/ isInB a p.
Proof. intro a.
       induction a; intros.
       - simpl. apply IHa.
       - simpl.
         case_eq (eqb p s); intros.
         + simpl. right; easy.
         + simpl. apply IHa.
       - simpl. left; easy.
Qed.

Lemma InMerge: forall a b p,
  isInA (Apf_merge a b) p =
  isInA a p || isInA b p.
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl.
         case_eq(eqb p s); intros.
         + simpl. easy.
         + simpl. easy.
Qed.

Lemma InMergeS: forall a b p,
  isInB (Bpf_merge a b) p =
  isInB a p || isInB b p.
Proof. intro a.
       induction a; intros.
       - simpl. apply IHa.
       - simpl.
         case_eq(eqb p s); intros.
         + simpl. easy.
         + simpl. apply IHa.
       - simpl. easy.
Qed.

Lemma InMergeN: forall a p, isInA a p = isInA (Apf_merge a a) p.
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl.
         rewrite IHa.
         case_eq(eqb p s); intros.
         + simpl. easy.
         + simpl.
           setoid_rewrite InMerge at 2.
           simpl. rewrite H. simpl.
           rewrite InMerge. easy.
Qed.

Lemma InMergeNSS: forall a b p q l s,
  isInB (Bpf_merge a (bpf_receive q l s b)) p = isInB (Bpf_merge a b) p.
Proof. intro a.
       induction a; intros.
       - simpl. apply IHa.
       - simpl. rewrite IHa. easy.
       - simpl. easy.
Qed.

Lemma InMergeNS: forall a p, isInB a p = isInB (Bpf_merge a a) p.
Proof. intro a.
       induction a; intros.
       - simpl. rewrite InMergeNSS. apply IHa.
       - simpl. rewrite InMergeS. simpl.
         case_eq(eqb p s); intros.
         + simpl. easy.
         + simpl.
           destruct(isInB a p); easy.
       - simpl. easy.
Qed.

Lemma InN: forall n a p, n > 0 -> isInA a p = isInA (ApnA3 a n) p.
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl.
         destruct n.
         easy.
         rewrite InMerge.
         rewrite <- IHn.
         destruct(isInA a p); easy.
         easy.
Qed.

Lemma InNS: forall n a p, n > 0 -> isInB a p = isInB (BpnB3 a n) p.
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl.
         destruct n.
         easy.
         rewrite InMergeS.
         rewrite <- IHn.
         destruct(isInB a p); easy.
         easy.
Qed.

Lemma reOrg1: forall a1 a2 a3 p l s,
  Apf_merge (Apf_merge a1 (apf_receive p l s a2)) a3 =
  Apf_merge a1 (apf_receive p l s (Apf_merge a2 a3)).
Proof. intro a1.
       induction a1; intros.
       - simpl. easy.
       - simpl. rewrite IHa1. easy.
Qed.

Lemma apf_merge_assoc: forall a1 a2 a3,
  Apf_merge (Apf_merge a1 a2) a3 =
  Apf_merge a1 (Apf_merge a2 a3).
Proof. intro a1.
       induction a1; intros.
       - simpl. easy.
       - simpl. rewrite IHa1. easy.
Qed.

Lemma bpf_merge_assoc: forall a1 a2 a3,
  Bpf_merge (Bpf_merge a1 a2) a3 =
  Bpf_merge a1 (Bpf_merge a2 a3).
Proof. intro a1.
       induction a1; intros.
       - simpl. rewrite IHa1. easy.
       - simpl. rewrite IHa1. easy.
       - simpl. easy.
Qed.

Lemma reOrg2: forall a1 a2 p l s w,
  merge_apf_cont (Apf_merge a1 (apf_receive p l s a2)) w =
  merge_apf_cont a1 (p & [(l, s, merge_apf_cont a2 w)]).
Proof. intro a1.
       induction a1; intros.
       - simpl. rewrite apfend_an.
         rewrite(st_eq(merge_apf_cont (apf_receive p l s a2) w )). simpl. easy.
       - simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 (Apf_merge a1 (apf_receive p l s2 a2))) w)).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a1) (p & [(l, s2, merge_apf_cont a2 w)]))). simpl.
         rewrite IHa1. easy.
Qed.

Lemma noPre: forall c p l s w w',
  isInA c p = false ->
  p & [(l, s, w)] = merge_apf_cont c w' ->
  c = apf_end.
Proof. intro c.
       induction c; intros.
       - easy.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha,Hb).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 c) w')) in H0.
         simpl in H0. inversion H0.
         subst. rewrite eqb_refl in Ha. easy.
Qed.

Lemma noPreS: forall c p l s w w',
  isInB c p = false ->
  p ! [(l, s, w)] = merge_bpf_cont c w' ->
  c = bpf_end.
Proof. intro c.
       induction c; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 c) w')) in H0. simpl in H0.
         easy.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 c) w')) in H0. simpl in H0.
         inversion H0. subst. rewrite eqb_refl in H. easy.
       - easy.
Qed.

Lemma apf_eqb_refl: forall a, Apf_eqb a a.
Proof. intro a.
       induction a; intros.
       - easy.
       - simpl. apply Bool.andb_true_iff.
         split. apply Bool.andb_true_iff.
         split. apply Bool.andb_true_iff.
         split. rewrite eqb_refl. easy.
         rewrite eqb_refl. easy.
         destruct s1; easy.
         easy.
Qed.

Lemma bpf_eqb_refl: forall a, Bpf_eqb a a.
Proof. intro a.
       induction a; intros.
       - simpl. rewrite !eqb_refl.
         rewrite eqbs_refl. simpl. easy.
       - simpl. rewrite !eqb_refl.
         rewrite eqbs_refl. simpl. easy.
       - simpl. easy.
Qed.

Lemma reOrd1: forall a1 a2 p l s w',
  merge_apf_cont (Apf_merge a1 (apf_receive p l s a2)) w' =
  merge_apf_cont a1 (merge_apf_cont (apf_receive p l s a2) w').
Proof. intro a1.
       induction a1; intros.
       - simpl. rewrite apfend_an. easy.
       - simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 (Apf_merge a1 (apf_receive p l s2 a2))) w')).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a1) (merge_apf_cont (apf_receive p l s2 a2) w'))).
         simpl.
         rewrite IHa1. easy.
Qed.

Lemma reOrd2: forall a q p l s l' s' w,
  p <> q ->
  isInA a p = false ->
  merge_apf_cont a (q & [(l, s, p & [(l', s', w)])]) =
  merge_apf_cont (Apf_merge a (apf_receive q l s apf_end)) (p & [(l', s', w)]).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive q l s apf_end) (p & [(l', s', w)]))). simpl.
         rewrite apfend_an. easy.
       - simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (q & [(l, s2, p & [(l', s', w)])]))).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 (Apf_merge a (apf_receive q l s2 apf_end))) (p & [(l', s', w)]))).
         simpl.
         simpl in H0.
         rewrite orbtf in H0.
         destruct H0 as (Ha,Hb).
         specialize(IHa q p l s2 l' s' w H Hb).
         rewrite IHa. easy.
Qed.

Lemma merge_merge: forall a1 a2 w,
  merge_apf_cont a1 (merge_apf_cont a2 w) =
  merge_apf_cont (Apf_merge a1 a2) w.
Proof. intro a1.
       induction a1; intros.
       - simpl. rewrite apfend_an. easy.
       - simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a1) (merge_apf_cont a2 w))).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 (Apf_merge a1 a2)) w)). simpl.
         rewrite IHa1.
         easy.
Qed.

Lemma merge_mergeS: forall a1 a2 w,
  merge_bpf_cont a1 (merge_bpf_cont a2 w) =
  merge_bpf_cont (Bpf_merge a1 a2) w.
Proof. intro a1.
       induction a1; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a1) (merge_bpf_cont a2 w))).
         rewrite(st_eq(merge_bpf_cont (Bpf_merge (bpf_receive s s0 s1 a1) a2) w)). simpl.
         rewrite IHa1. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a1) (merge_bpf_cont a2 w))).
         rewrite(st_eq(merge_bpf_cont (Bpf_merge (bpf_send s s0 s1 a1) a2) w)). simpl.
         rewrite IHa1. easy.
       - simpl. rewrite bpfend_bn. easy.
Qed.

Lemma isInFE1: forall a1 a2 p q l s,
  p <> q ->
  isInA (Apf_merge a1 (apf_receive p l s a2)) q = false ->
  isInA (Apf_merge a1 a2) q = false.
Proof. intro a1.
       induction a1; intros.
       - simpl. simpl in H0.
         rewrite orbtf in H0. easy.
       - simpl. simpl in H0.
         rewrite orbtf in H0. 
         destruct H0 as (Ha, Hb).
         rewrite Ha. simpl.
         specialize(IHa1 a2 p q l s2).
         apply IHa1; easy.
Qed.

Lemma mergeR: forall a, Apf_merge a apf_end = a.
Proof. intro a.
       induction a; intros.
       - simpl. easy.
       - simpl. rewrite IHa. easy.
Qed.

Lemma mergeRS: forall a, Bpf_merge a bpf_end = a.
Proof. intro a.
       induction a; intros.
       - simpl. rewrite IHa. easy.
       - simpl. rewrite IHa. easy.
       - simpl. easy.
Qed.

Lemma reOrg3: forall a p q l s l' s' w w',
  p <> q ->
  isInA a q = false -> 
  p & [(l, s, w)] = merge_apf_cont a (q & [(l', s', w')]) ->
  exists c, isInA c q = false /\ a = apf_receive p l s c /\ w = merge_apf_cont c (q & [(l', s', w')]).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H1.
         inversion H1. subst. easy.
       - simpl in H0. rewrite orbtf in H0.
         destruct H0 as (Ha, Hb).
         rewrite eqb_neq in Ha.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (q & [(l', s', w')]))) in H1. simpl in H1.
         inversion H1. subst.
         exists a.
         split. easy. split. easy. easy.
Qed.

Lemma apf_endN: forall n, ApnA3 apf_end n = apf_end.
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - rewrite ApnA3C IHn. simpl. easy.
Qed.

Lemma apf_endNS: forall n, BpnB3 bpf_end n = bpf_end.
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - rewrite BpnB3C IHn. simpl. easy.
Qed.

Lemma breOrg1: forall b b2 p l s w,
  merge_bpf_cont (Bpf_merge b (bpf_send p l s b2)) w =
  merge_bpf_cont b (p ! [(l, s, merge_bpf_cont b2 w)]).
Proof. intro b.
       induction b; intros.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Bpf_merge b (bpf_send p l s2 b2))) w )).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, merge_bpf_cont b2 w)]))). simpl.
         rewrite IHb. easy.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 (Bpf_merge b (bpf_send p l s2 b2))) w )).
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, merge_bpf_cont b2 w)]))). simpl.
         rewrite IHb. easy.
       - simpl. rewrite bpfend_bn.
         rewrite(st_eq(merge_bpf_cont (bpf_send p l s b2) w )). simpl. easy.
Qed.

Lemma breOrg2: forall b b2 p l s w,
  merge_bpf_cont (Bpf_merge b (bpf_receive p l s b2)) w =
  merge_bpf_cont b (p & [(l, s, merge_bpf_cont b2 w)]).
Proof. intro b.
       induction b; intros.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Bpf_merge b (bpf_receive p l s2 b2))) w )).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p & [(l, s2, merge_bpf_cont b2 w)]))). simpl.
         rewrite IHb. easy.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 (Bpf_merge b (bpf_receive p l s2 b2))) w )).
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p & [(l, s2, merge_bpf_cont b2 w)]))). simpl.
         rewrite IHb. easy.
       - simpl. rewrite bpfend_bn.
         rewrite(st_eq(merge_bpf_cont (bpf_receive p l s b2) w )). simpl. easy.
Qed.

Lemma breOrg3: forall a b w,
  merge_bpf_cont (Bpf_merge a b) w =
  merge_bpf_cont a (merge_bpf_cont b w).
Proof. intro a.
       induction a; intros.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Bpf_merge a b)) w)).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 a) (merge_bpf_cont b w))). simpl.
         rewrite IHa. easy.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 (Bpf_merge a b)) w)).
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 a) (merge_bpf_cont b w))). simpl.
         rewrite IHa. easy.
       - simpl. rewrite bpfend_bn. easy.
Qed.

Lemma bareOrg1: forall a c w, merge_bpf_cont (Bpf_merge (Ap2BpSeq a) c) w = merge_apf_cont a (merge_bpf_cont c w).
Proof. intro a.
       induction a; intros.
       - simpl. rewrite apfend_an. easy.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Bpf_merge (Ap2BpSeq a) c)) w )).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (merge_bpf_cont c w))). simpl.
         rewrite IHa. easy.
Qed.

Lemma bareOrg2: forall a p l s w, 
  merge_bpf_cont (Ap2BpSeq a) (p & [(l, s, w)]) =
  merge_bpf_cont (Ap2BpSeq (Apf_merge a (apf_receive p l s apf_end))) w.
Proof. intro a.
       induction a; intros.
       - simpl. rewrite bpfend_bn.
         rewrite(st_eq(merge_bpf_cont (bpf_receive p l s bpf_end) w)). simpl.
         rewrite bpfend_bn. easy.
       - simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Ap2BpSeq a)) (p & [(l, s2, w)]))).
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 (Ap2BpSeq (Apf_merge a (apf_receive p l s2 apf_end)))) w)).
         simpl. rewrite IHa. easy.
Qed.

Lemma BisInAF: forall c p, isInB (Ap2BpSeq c) p = false.
Proof. intro c.
       induction c; intros.
       - simpl. easy.
       - simpl. apply IHc.
Qed.

Lemma inH9: forall c p l s w w',
  isInB c p = true ->
  p ! [(l, s, w)] = merge_bpf_cont c w' ->
  exists b : Bpf, c = (bpf_send p l s b) /\ w = merge_bpf_cont b w'.
Proof. intro c.
       induction c; intros.
       - rewrite(st_eq( merge_bpf_cont (bpf_receive s s0 s1 c) w')) in H0.
         simpl in H0. easy.
       - rewrite(st_eq( merge_bpf_cont (bpf_send s s0 s1 c) w')) in H0.
         simpl in H0. inversion H0. subst.
         exists c. esplit; easy.
       - simpl in H. easy.
Qed.

Lemma InvertBA: forall b a p l s w w', 
  isInB b p = false ->
  paco2 refinementR3 bot2 (merge_bpf_cont b (p ! [(l, s, w)])) (merge_apf_cont a w') ->
  exists b1 w1 s', isInB b1 p = false /\ subsort s s' /\ w' = merge_bpf_cont b1 (p ! [(l, s', w1)]).
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))) in H0. simpl in H0.
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
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s' b1) (p ! [(l, s'', w2)]))). simpl.
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
              * specialize(_39_3 b1 a1 p w'0 (p ! [(l, s'', w2)]) w' Ha Hc Hin4b H4); intro HR.
                destruct HR as (c,(Hd,(He,(Hf,Hg)))).
                exists c. exists w2. exists s''.
                split. easy. split. easy. easy.
              * specialize(mcBp2Ap b1 (p ! [(l, s'', w2)]) H4); intro HN.
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
              (s & [(s0, s', w'0)])
              w' H3 H2 H1 H5 H4
              ); intro HR.
              destruct HR as [HR | HR].
              * destruct HR as (c,(Hd,(He,(Hf,Hg)))).
                rewrite Hc in Hg.
                assert(c = apf_end).
                { apply noPre with (p := s) (l := s0) (s := s') (w := merge_bpf_cont b1 (p ! [(l, s'', w2)])) (w' := w'); easy. }
                rewrite H10 in Hg. rewrite apfend_an in Hg.
                exists (bpf_receive s s0 s' b1). exists w2. exists s''.
                split. simpl. easy. split. easy.
                rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s' b1) (p ! [(l, s'', w2)]))). simpl.
                easy.
              * destruct HR as (c,(Hd,(He,(Hf,Hg)))).
                rewrite Hc in Hg.
                exists (Bpf_merge (Ap2BpSeq c) (bpf_receive s s0 s' b1)). exists w2. exists s''.
                split.
                apply InMergeFS. split. rewrite BisInAF. easy. simpl. easy.
                split. easy.
                rewrite mcAp2Bp2 in Hg.
                rewrite breOrg2. easy.
                apply refinementR3_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite eqb_neq in Ha.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H0. simpl in H0.
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
           assert(w'0 = (p ! [(l, s'', w1)])).
           { apply merge_same_beq in HHc. easy. }
           rewrite H3 in Hc3.
           assert(merge_bpf_cont c (s ! [(s0, s', p ! [(l, s'', w1)])]) =
                  merge_bpf_cont (Bpf_merge c (bpf_send s s0 s' bpf_end)) (p ! [(l, s'', w1)])).
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
             specialize(inH8 b1 c p (p ! [(l, s'', w1)]) w'0 
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
           assert(merge_bpf_cont (Bpf_merge b1 (bpf_send p l s'' b2)) (s ! [(s0, s', w'0)]) =
                  merge_bpf_cont b1 (p! [(l, s'', (merge_bpf_cont b2 (s ! [(s0, s', w'0)])))])).
           { rewrite breOrg1. easy. }
           rewrite H3 in Hc3.
           exists b1. exists(merge_bpf_cont b2 (s ! [(s0, s', w'0)])). exists s''.
           split. easy. split. easy. easy.
           rename H1 into HH1.
           assert(c <> b1).
           { apply bpf_eqb_neq in HH1. easy. }
           specialize(_39_1 c b1 p p (merge_bpf_cont c w'0) w'0 (p ! [(l, s'', w1)])
           HHN HHa H1 H2 HHc
           ); intro HR.
           destruct HR as [HR | HR].
           ++ destruct HR as (d,(Hr1,(Hr2,(Hr3,Hr4)))).
              rewrite Hr4 in Hc3.
              assert(merge_bpf_cont c (s ! [(s0, s', merge_bpf_cont d (p ! [(l, s'', w1)]))]) =
                     merge_bpf_cont (Bpf_merge c (bpf_send s s0 s' d)) (p ! [(l, s'', w1)])).
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
              assert(merge_bpf_cont (Bpf_merge b1 bpf_end) (s ! [(s0, s', p ! [(l, s'', w1)])]) =
                    merge_bpf_cont (Bpf_merge b1 (bpf_send s s0 s' bpf_end)) (p ! [(l, s'', w1)])).
              { rewrite breOrg1. rewrite bpfend_bn. rewrite mergeRS. easy. }
              rewrite H11 in Hc3.
              exists (Bpf_merge b1 (bpf_send s s0 s' bpf_end)). exists w1. exists s''.
              split. 
              apply InMergeFS. split. easy. simpl. 
              apply eqb_neq in Ha. rewrite Ha. easy.
              split. easy. easy.
         + specialize(mcBp2Ap (BpnB3 b0 n) (s ! [(s0, s', w'0)]) H9); intro HR.
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
              rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w1)]))). simpl. easy.
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
              assert(merge_apf_cont c (s ! [(s0, s', merge_bpf_cont b1 (p ! [(l, s'', w1)]))]) =
                     merge_bpf_cont (Bpf_merge (Ap2BpSeq c) (bpf_send s s0 s' b1)) (p ! [(l, s'', w1)])).
              { rewrite mcAp2Bp2. rewrite breOrg1. easy. }
              rewrite H3 in HHb.
              exists (Bpf_merge (Ap2BpSeq c) (bpf_send s s0 s' b1)). exists w1. exists s''.
              split. simpl.
              apply InMergeFS. split. rewrite BisInAF. easy. simpl.
              apply eqb_neq in Ha. rewrite Ha. easy.
              split. easy.
              easy.
         apply refinementR3_mon. 
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
         apply refinementR3_mon.
Qed.

Lemma abContra: forall a b1 b2 p l s,
  Ap2BpSeq a = Bpf_merge b1 (bpf_send p l s b2) -> False.
Proof. induction a; intros.
       - simpl in H.
         case_eq b1; intros.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
         + subst. simpl in H. easy.
       - simpl in H.
         case_eq b1; intros.
         + subst. simpl in H.
           inversion H. subst.
           specialize(IHa b b2 p l s2).
           apply IHa. easy.
         + subst. simpl in H.
           inversion H. subst.
           specialize(IHa bpf_end b2 p l s2).
           apply IHa. easy.
Qed.

Lemma InvertBB: forall a b p l s w w', 
  isInB a p = false ->
  paco2 refinementR3 bot2 (merge_bpf_cont a (p ! [(l, s, w)])) (merge_bpf_cont b w') ->
  (exists a1 a2 s', isInB a1 p = false /\ subsort s s' /\ b = Bpf_merge a1 (bpf_send p l s' a2))
  \/
  (exists a1  w1 s', isInB a1 p = false /\ subsort s s' /\ isInB b p = false /\ w' = merge_bpf_cont a1 (p ! [(l, s', w1)])).
Proof. intro a.
       induction a; intros.
       - simpl in H.
         rewrite(st_eq (merge_bpf_cont (bpf_receive s s0 s1 a) (p ! [(l, s2, w)]))) in H0. simpl in H0.
         pinversion H0.
         subst.
         rewrite <- meqAp3 in H5, H8, H9.
         assert((merge_apf_cont (ApnA3 a0 n) w'0) = (merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) w'0)).
         { rewrite mcAp2Bp2. easy. }
         rewrite H1 in H8.
         specialize(IHa (Ap2BpSeq (ApnA3 a0 n)) p l s2 w w'0 H H8).
         assert(merge_apf_cont (ApnA3 a0 n) (s & [(s0, s', w'0)]) =
                merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) (s & [(s0, s', w'0)])).
         { rewrite mcAp2Bp2. easy. }
         rewrite H2 in H5.
         case_eq(Bpf_eqb (Ap2BpSeq (ApnA3 a0 n)) b); intros.
         + assert(Ap2BpSeq (ApnA3 a0 n) = b).
           { apply bpf_eqb_eq. easy. }
           assert((s & [(s0, s', w'0)]) = w').
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
              rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s' b1) (p ! [(l, s'', w1)]))). simpl.
              easy.
         + assert(Ap2BpSeq (ApnA3 a0 n) <> b).
           { apply bpf_eqb_neq. easy. }
           destruct IHa as [IHa | IHa].
           ++ destruct IHa as (b1,(b2,(s'',(Hb1,(Hb2,Hb3))))).
              apply abContra in Hb3. easy.
           ++ destruct IHa as (b1,(w1,(s'',(Hb1,(Hb2,(Hb3,Hb4)))))).
              simpl in Hb3.
              case_eq (isInB b p); intros.
              * assert(merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) (s & [(s0, s', w'0)]) =
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
                specialize(inH8 b1 c p (p ! [(l, s'', w1)]) w' Hb1 HP1 HP3); intro HP.
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
              * assert(merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) (s & [(s0, s', w'0)]) =
                       merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) w'0).
                { rewrite bareOrg2. easy. }
                rewrite H11 in H5.
                rewrite Hb4 in H5.
                assert(merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) (merge_bpf_cont b1 (p ! [(l, s'', w1)])) =
                       merge_bpf_cont (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1) (p ! [(l, s'', w1)])).
                { rewrite bareOrg1. rewrite mcAp2Bp2. easy.  }
                rewrite H12 in H5.
                case_eq(Bpf_eqb b (Bpf_merge (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s' apf_end))) b1)); intros.
                ** assert((p ! [(l, s'', w1)]) = w').
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
                   p p (merge_bpf_cont b w') w' (p ! [(l, s'', w1)]) H10 H14 H15 H16 H5
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
         apply refinementR3_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite eqb_neq in Ha.
         rewrite(st_eq (merge_bpf_cont (bpf_send s s0 s1 a) (p ! [(l, s2, w)]))) in H0. simpl in H0.
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
                (s ! [(s0, s', w'0)]) w' H3 H2 H4
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
                (s ! [(s0, s', w'0)]) w' H3 H2 H1 H4 H9
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
                       assert(merge_bpf_cont (Bpf_merge c2 (bpf_send p l s'' b2)) (s ! [(s0, s', w'0)]) =
                              merge_bpf_cont c2 (p ! [(l, s'', merge_bpf_cont b2 (s ! [(s0, s', w'0)]))])).
                       { rewrite breOrg1. easy. }
                       rewrite H11 in HP4.
                       right. 
                       exists c2. exists(merge_bpf_cont b2 (s ! [(s0, s', w'0)])). exists s''.
                       split. easy. split. easy. split; easy.
         + destruct IHa as (b1,(w2,(s'',(Hb1,(Hb2,(Hb3,Hb4)))))).
           case_eq(Bpf_eqb (BpnB3 b0 n) b); intros.
           ++ assert((BpnB3 b0 n) = b).
              { apply bpf_eqb_eq. easy. } 
             rewrite H1 in H4.
             assert((s ! [(s0, s', w'0)]) = w').
             { apply merge_same_beq in H4. easy. }
             rewrite Hb4 in H2.
             assert(s ! [(s0, s', merge_bpf_cont b1 (p ! [(l, s'', w2)]))] =
                    merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w2)])).
             { rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w2)]))). simpl. easy. }
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
                specialize(inH8 (BpnB3 b0 n) b s (s ! [(s0, s', w'0)]) w'
                H3 H2 H4
                ); intro HP.
                destruct HP as (c,(HP1,(HP2,HP3))).
                rewrite Hb4 in HP3.
                assert(s ! [(s0, s', merge_bpf_cont b1 (p ! [(l, s'', w2)]))] =
                      merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w2)])).
                { rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w2)]))). simpl. easy. }
                rewrite H9 in HP3.
                case_eq(Bpf_eqb (bpf_send s s0 s' b1) c); intros.
                ** assert((bpf_send s s0 s' b1) = c).
                   { apply bpf_eqb_eq. easy. }
                   assert((p ! [(l, s'', w2)]) = w').
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
                       p (p ! [(l, s'', w2)]) w' H13 H12 HP3
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
                       (merge_bpf_cont c w') (p ! [(l, s'', w2)]) w' H13 H12 H11 HP3 H14
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
                (merge_bpf_cont b w') (s ! [(s0, s', w'0)]) w' H3 H2 H1 H4 H9
                ); intro HP.
                destruct HP as [HP | HP].
                ** destruct HP as (c,(HP4,(HP5,(HP6,HP7)))).
                   assert(c = bpf_end).
                   { apply noPreS in HP7; easy. }
                   rewrite H10 in HP7. rewrite bpfend_bn in HP7.
                   rewrite Hb4 in HP7.
                   assert(s ! [(s0, s', merge_bpf_cont b1 (p ! [(l, s'', w2)]))] =
                          merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w2)])).
                   { rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s' b1) (p ! [(l, s'', w2)]))). simpl. easy. }
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
                   assert(merge_bpf_cont c (s ! [(s0, s', merge_bpf_cont b1 (p ! [(l, s'', w2)]))]) =
                          merge_bpf_cont (Bpf_merge c (bpf_send s s0 s' b1)) (p ! [(l, s'', w2)])).
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
         apply refinementR3_mon.
       - rewrite bpfend_bn in H0.
         pinversion H0.
         subst.
         rewrite <- meqBp3 in H5, H8, H9.
         case_eq(Bpf_eqb (BpnB3 b0 n) b); intros.
         + assert((BpnB3 b0 n) = b).
           { apply bpf_eqb_eq. easy. }
           assert((p ! [(l, s', w'0)]) = w').
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
              specialize(inH8 (BpnB3 b0 n) b p(p ! [(l, s', w'0)]) w'
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
              (merge_bpf_cont b w') (p ! [(l, s', w'0)]) w' H4 H3 H2 H5 H10
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
         apply refinementR3_mon.
Qed.

Lemma InvertAA: forall a b p l s w w', 
  isInA a p = false ->
  paco2 refinementR3 bot2 (merge_apf_cont a (p & [(l, s, w)])) (merge_apf_cont b w') ->
  (exists a1 a2 s', isInA a1 p = false /\ subsort s' s /\ b = Apf_merge a1 (apf_receive p l s' a2))
  \/
  (exists a1  w1 s', isInA a1 p = false /\ subsort s' s /\ isInA b p = false /\ w' = merge_apf_cont a1 (p & [(l, s', w1)])).
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
                (p & [(l, s', w'0)]) w'
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
                apply refinementR3_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H0. simpl in H0.
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
                (s & [(s0, s', w'0)]) w'
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
                assert(w' = merge_apf_cont a3 (p & [(l, s'', merge_apf_cont a2 (s & [(s0, s', w'0)]))])).
                { rewrite Hi.
                  rewrite reOrg2. easy.
                }
                exists a3. exists (merge_apf_cont a2 (s & [(s0, s', w'0)])). exists s''.
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
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s' a1) (p & [(l, s'', w1)]))). simpl.
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
             specialize(inH4 (ApnA3 a0 n) b s s0 s' (merge_apf_cont a1 (p & [(l, s'', w1)])) w' H2 H3 H1 H4); intro Hin.
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
                   (merge_apf_cont a3 w') (p & [(l, s'', w1)]) w'
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
                   (s & [(s0, s', merge_apf_cont a1 (p & [(l, s'', w1)]))]) w'
                   H3 H1 H2 H4 H9
                   ); intro Hin.
             destruct Hin as [Hin | Hin].
             ++ destruct Hin as (c,(Hc,(Hd,(He,Hf)))).
                assert(c = apf_end).
                { apply noPre with (p := s) (l := s0) (s := s') (w := merge_apf_cont a1 (p & [(l, s'', w1)])) (w' := w'); easy.
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
                rewrite(st_eq(merge_apf_cont (apf_receive s s0 s' a1) (p & [(l, s'', w1)]))). simpl.
                easy.
             ++ destruct Hin as (c,(Hc,(Hd,(He,Hf)))).
                assert(w' =  merge_apf_cont (Apf_merge c (apf_receive s s0 s' a1)) (p & [(l, s'', w1)])).
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
                apply refinementR3_mon.
Qed.

Lemma dropRA: forall a b p l s s' w w',
  isInA a p = false ->
  isInA b p = false ->
  subsort s' s ->
  paco2 refinementR3 bot2 (merge_apf_cont a (p & [(l, s, w)])) (merge_apf_cont b (p & [(l, s', w')])) ->
  paco2 refinementR3 bot2 (merge_apf_cont a w) (merge_apf_cont b w').
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H2.
         rewrite apfend_an.
         pinversion H2.
         + subst.
           rewrite <- meqAp3 in H7, H10, H11.
           assert(isInA (ApnA3 a n) p = false).
           { case_eq n; intros.
             - simpl. easy.
             - rewrite <- InN; easy.
           }
           case_eq(Apf_eqb (ApnA3 a n) b); intros Hcs.
           * apply apf_eqb_eq in Hcs. subst.
             apply merge_same_aeq in H7.
             inversion H7. subst. easy.
           * assert((ApnA3 a n) <> b).
             { apply apf_eqb_neq. easy. } 
             symmetry in H7.
             assert(merge_apf_cont b (p & [(l, s', w')]) = merge_apf_cont b (p & [(l, s', w')])) by easy.
             specialize(_39_2 (ApnA3 a n) b p p
             (merge_apf_cont b (p & [(l, s', w')]))
             (p & [(l, s'0, w'0)])
             (p & [(l, s', w')]) H3 H0 H4 H7 H5
             ); intro HP.
             destruct HP as [HP | HP].
             * destruct HP as (c,(Ha,(Hb,(Hc,Hd)))).
               assert(c = apf_end) as HC.
               { specialize (noPre c p l s'0 w'0 (p & [(l, s', w')]) Ha Hd); intros.
                 easy.
               }
               rewrite HC in Hd. rewrite apfend_an in Hd. 
               rewrite HC in Hc.
               assert(b = ApnA3 a n).
               { rewrite mergeR in Hc. easy. }
               rewrite <- H6 in H10.
               inversion Hd. subst.
               easy.
             * destruct HP as (c,(Ha,(Hb,(Hc,Hd)))).
               assert(c = apf_end) as HC.
               { specialize (noPre c p l s' w' (p & [(l, s'0, w'0)]) Ha Hd); intros.
                 easy.
               }
               rewrite HC in Hd. rewrite apfend_an in Hd.
               inversion Hd. subst.
               assert(b = ApnA3 a n).
               { rewrite mergeR in Hc. easy. }
               rewrite H6. easy.
             apply refinementR3_mon.
       - pinversion H2.
         + rewrite <- meqAp3 in H4, H7, H8.
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H3. simpl in H3.
           inversion H3. subst.
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
           assert(isInA (ApnA3 a0 n) s = false).
           { case_eq n; intros.
             - simpl. easy.
             - rewrite <- InN; easy.
           }
           case_eq(Apf_eqb (ApnA3 a0 n) b); intros Hcs.
           * apply apf_eqb_eq in Hcs. subst.
             apply merge_same_aeq in H4.
             inversion H4. subst. simpl in H. rewrite eqb_refl in H. easy.
           * assert((ApnA3 a0 n) <> b).
             { apply apf_eqb_neq. easy. } 
             symmetry in H4.
             assert(merge_apf_cont b (p & [(l, s', w')]) = merge_apf_cont b (p & [(l, s', w')])) by easy.
             specialize(_39_2 (ApnA3 a0 n) b s p 
             (merge_apf_cont b (p & [(l, s', w')]))
             (s & [(s0, s'0, w'0)])
             (p & [(l, s', w')]) H9 H0 H10 H4 H11
             ); intro HP.
             destruct HP as [HP | HP].
             * destruct HP as (c,(Ha,(Hb,(Hc,Hd)))).
               assert(s <> p).
               { simpl in H. rewrite orbtf in H.
                 destruct H as (Hu, Hv).
                 rewrite eqb_neq in Hu. easy.
               }
               specialize(reOrg3 c s p s0 s'0 l s' w'0 w' H12 Ha Hd); intro HR.
               destruct HR as (d,(He,(Hf,Hg))).
               rewrite Hf in Hc.
               rewrite Hc.
               assert((merge_apf_cont (Apf_merge (ApnA3 a0 n) (apf_receive s s0 s'0 d)) w') = 
                       merge_apf_cont (ApnA3 a0 n) (s & [(s0, s'0, merge_apf_cont d w')])).
               { rewrite reOrg2. easy. }
               rewrite H13.
               pfold.
                specialize(ref3_a (upaco2 refinementR3 bot2) (merge_apf_cont a w) (merge_apf_cont d w')
                s s0 s1 s'0 (ApnA3 a0 n)
                1 H5
                ); intro HR.
                simpl in HR.
                apply HR.
                easy.
                left.
                rewrite merge_merge.
                rewrite Hg in H7.
                rewrite merge_merge in H7.
                specialize(IHa (Apf_merge (ApnA3 a0 n) d) p l s2 s' w w').
                apply IHa. 
                simpl in H. rewrite orbtf in H. easy.
                apply InMergeF. 
                split. rewrite Hc in H0.
                apply InMergeF in H0. easy.
                easy.
                easy. easy.
                admit.
             * destruct HP as (c,(Ha,(Hb,(Hc,Hd)))).
                assert(p <> s).
                { simpl in H. rewrite orbtf in H.
                  destruct H as (Hu, Hv).
                  rewrite eqb_neq in Hu. easy.
                }
                specialize(reOrg3 c p s l s' s0 s'0 w' w'0 H12 Ha Hd); intro HR.
                destruct HR as (d,(He,(Hf,Hg))).
                rewrite Hg.
                pfold.
                assert((merge_apf_cont b (merge_apf_cont d (s & [(s0, s'0, w'0)]))) = 
                       (merge_apf_cont (Apf_merge b d) (s & [(s0, s'0, w'0)]))).
                { rewrite merge_merge. easy. }
                rewrite H13.
                specialize(ref3_a (upaco2 refinementR3 bot2) (merge_apf_cont a w) w'0
                s s0 s1 s'0 (Apf_merge b d)
                1 H5
                ); intro HR.
                simpl in HR.
                apply HR.
                apply InMergeF.
                split.
                assert(isInA (ApnA3 a0 n) s = false).
                { case_eq n; intros.
                  - simpl. easy.
                  - rewrite <- InN. easy. easy.
                }
                rewrite Hc in H14.
                apply InMergeF in H14. easy. easy.
                left.
                assert((merge_apf_cont (Apf_merge b d) w'0) =
                      (merge_apf_cont b (merge_apf_cont d w'0))).
                { rewrite merge_merge. easy. }
                rewrite H14.
                specialize(IHa b p l s2 s' w (merge_apf_cont d w'0)).
                apply IHa.
                simpl in H. rewrite orbtf in H. easy.
                easy.
                easy.
                rewrite Hc Hf in H7.
                rewrite reOrg2 in H7.
                easy.
                admit.
         + rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H3.
           simpl in H3.
           easy.
         + rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H4.
           simpl in H4.
           easy.
       apply refinementR3_mon.
Admitted.

Lemma dropBA: forall b b2 p l s s' w w',
  isInB b p = false ->
  isInB b2 p = false ->
  paco2 refinementR3 bot2 (merge_bpf_cont b (p ! [(l, s, w)])) (merge_bpf_cont b2 (p ! [(l, s', w')])) ->
  paco2 refinementR3 bot2 (merge_bpf_cont b w) (merge_bpf_cont b2 w').
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))) in H1.
         case_eq b2; intros.
         + subst. 
           rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b0) (p ! [(l, s', w')]))) in H1.
           simpl in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)).
           rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b0) w')). simpl.
           simpl in H. simpl in H0.
           pinversion H1.
           subst.
           rewrite <- meqAp3 in H6, H9, H10.
           symmetry in H6.
           case_eq (eqb s s3); intros.
           ++ rewrite eqb_eq in H2. subst.
              assert((ApnA3 a n) = apf_end).
              { apply noPre in H6. easy.
                case_eq n; intros.
                - simpl. easy.
                - rewrite <- InN; easy.
              }
              rewrite H2 in H6.
              rewrite apfend_an in H6. inversion H6. subst.
              rewrite H2 in H9. rewrite apfend_an in H9.
              pfold.
              specialize(ref3_a (upaco2 refinementR3 bot2) (merge_bpf_cont b w)
              (merge_bpf_cont b0 w') s3 s0 s1 s'0 apf_end 1 H7
              ); intro HR.
              simpl in HR.
              rewrite !apfend_an in HR.
              apply HR.
              easy. left.
              apply IHb with (p := p) (l := l) (s := s2) (s' := s').
              easy. easy. easy.
              admit.
           ++ rewrite eqb_neq in H2.
              assert(isInA (ApnA3 a n) s = false).
              { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InN; easy.
              }
              specialize(pneqq4 (ApnA3 a n) s s3 s4 s0 s5 s'0 
              (merge_bpf_cont b0 (p ! [(l, s', w')]))
              w'0 H2 H3 H6
              ); intro HP.
              destruct HP as (a1,(HPa,(HPb,HPc))).
              case_eq(isBpSend b0); intros.
              * assert(merge_bpf_cont b0 (p ! [(l, s', w')]) = merge_bpf_cont b0 (p ! [(l, s', w')])) by easy.
                specialize(_39_3 b0 a1 p
                (merge_bpf_cont b0 (p ! [(l, s', w')]))
                (p ! [(l, s', w')])
                (s & [(s0, s'0, w'0)]) H0 H5 HPb H4
                ); intro HR2.
                destruct HR2 as (c,(Hc1,(Hc2,(Hc3,Hc4)))).
                specialize(pneqq6 c p s s0 l s'0 s' w'0 w' Hc1 Hc4); intro HQ.
                destruct HQ as (b2,(HQ1,(HQ2,HQ3))).
                rewrite Hc3. rewrite HQ3.
                assert((s3 & [(s4, s5, merge_bpf_cont (Bpf_merge (Ap2BpSeq a1) (bpf_receive s s0 s'0 b2)) w')]) =
                       merge_apf_cont (apf_receive s3 s4 s5 a1) (s & [(s0, s'0, merge_bpf_cont b2 w')])).
                { rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a1) (s & [(s0, s'0, merge_bpf_cont b2 w')]))). simpl.
                  rewrite bareOrg1. 
                  rewrite(st_eq (merge_bpf_cont (bpf_receive s s0 s'0 b2) w')). simpl.
                  easy.
                }
                rewrite H11.
                pfold.
                specialize(ref3_a (upaco2 refinementR3 bot2)
                (merge_bpf_cont b w)
                (merge_bpf_cont b2 w') s s0 s1 s'0
                (apf_receive s3 s4 s5 a1) 1 H7
                ); intro HR.
                simpl in HR.
                apply HR.
                apply eqb_neq in H2. rewrite H2. rewrite HPa. easy.
                left.
                assert((merge_apf_cont (apf_receive s3 s4 s5 a1) (merge_bpf_cont b2 w')) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 a1)) b2) w')).
                { rewrite bareOrg1. easy. }
                rewrite H12.
                apply IHb  with (p := p) (l := l) (s := s2) (s' := s').
                easy.
                apply InMergeFS. rewrite BisInAF. easy.
                rewrite HQ2 in H9.
                rewrite HPc in H9.
                assert((merge_apf_cont (apf_receive s3 s4 s5 a1) (merge_bpf_cont b2 (p ! [(l, s', w')]))) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 a1)) b2) (p ! [(l, s', w')]))).
                { rewrite bareOrg1. easy. }
                rewrite H13 in H9.
                easy.
                admit.
              * specialize(mcBp2Ap b0 (p ! [(l, s', w')]) H4); intro HP.
                destruct HP as (a2,(HP1,HP2)).
                rewrite HP1 in HPb.
                case_eq(Apf_eqb a2 a1); intros.
                ** apply apf_eqb_eq in H5. subst.
                   apply merge_same_aeq in HPb. easy.
                ** apply apf_eqb_neq in H5.
                   assert(merge_apf_cont a1 (s & [(s0, s'0, w'0)]) = merge_apf_cont a1 (s & [(s0, s'0, w'0)])) by easy.
                   assert(a1 <> a2) by easy.
                   symmetry in HPb.
                   specialize(_39_4 a1 a2 p l s'
                   (merge_apf_cont a1 (s & [(s0, s'0, w'0)]))
                   (s & [(s0, s'0, w'0)])
                   w' H12 H11 HPb
                   ); intro HQ.
                   destruct HQ as (c,(HQ1,HQ2)).
                   assert(merge_apf_cont c (p ! [(l, s', w')]) = 
                          merge_bpf_cont (Ap2BpSeq c) (p ! [(l, s', w')])).
                   { rewrite mcAp2Bp2. easy. }
                   rewrite H13 in HQ2.
                   assert(isInB (Ap2BpSeq c) p = false).
                   { rewrite BisInAF. easy. }
                   specialize(pneqq6 (Ap2BpSeq c) p s s0 l s'0 s' w'0 w' H14 HQ2); intro HP.
                   destruct HP as (b2,(Hb2,(Hb3,Hb4))).
                   rewrite HP2.
                   rewrite HQ1.
                   assert((Ap2BpSeq (Apf_merge a1 c))  = (Bpf_merge (Ap2BpSeq a1) (Ap2BpSeq c))).
                   { rewrite Ap2BpSeq2. easy. }
                   rewrite H15. rewrite Hb4.
                   assert((s3 & [(s4, s5, merge_bpf_cont (Bpf_merge (Ap2BpSeq a1) (bpf_receive s s0 s'0 b2)) w')]) =
                          merge_apf_cont (apf_receive s3 s4 s5 a1) (s & [(s0, s'0, merge_bpf_cont b2 w')])
                          ).
                   { rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a1) (s & [(s0, s'0, merge_bpf_cont b2 w')]))). simpl.
                     rewrite bareOrg1.
                     rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s'0 b2) w')). simpl. easy.
                   } 
                   rewrite H16.
                specialize(ref3_a (upaco2 refinementR3 bot2)
                (merge_bpf_cont b w)
                (merge_bpf_cont b2 w') s s0 s1 s'0
                (apf_receive s3 s4 s5 a1) 1 H7
                ); intro HR.
                simpl in HR.
                pfold.
                apply HR.
                apply eqb_neq in H2. rewrite H2. rewrite HPa. easy.
                left.
                assert((merge_apf_cont (apf_receive s3 s4 s5 a1) (merge_bpf_cont b2 w')) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 a1)) b2) w')).
                { rewrite bareOrg1. easy. }
                rewrite H17.
                apply IHb  with (p := p) (l := l) (s := s2) (s' := s').
                easy.
                apply InMergeFS. rewrite BisInAF. easy.
                rewrite HPc in H9.
                rewrite Hb3 in H9.
                assert((merge_apf_cont (apf_receive s3 s4 s5 a1) (merge_bpf_cont b2 (p ! [(l, s', w')]))) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 a1)) b2) (p ! [(l, s', w')]))).
                { rewrite bareOrg1. easy. }
                rewrite H18 in H9.
                easy.
                admit.
                apply refinementR3_mon.
         + subst.
           rewrite(st_eq (merge_bpf_cont (bpf_send s3 s4 s5 b0) (p ! [(l, s', w')]))) in H1. simpl in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)).
           rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 b0) w')). simpl.
           simpl in H. simpl in H0.
           pinversion H1.
           subst.
           rewrite <- meqAp3 in H6.
           case_eq((ApnA3 a n)); intros.
           rewrite H2 in H6. rewrite apfend_an in H6. easy.
           rewrite H2 in H6.
           rewrite(st_eq(merge_apf_cont (apf_receive s6 s7 s8 a0) (s & [(s0, s'0, w'0)]))) in H6. simpl in H6. easy.
           apply refinementR3_mon.
         + rewrite H2 in H1. rewrite bpfend_bn in H1. simpl in H1.
           rewrite bpfend_bn.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
           pinversion H1.
           subst. 
           rewrite <- meqAp3 in H7.
           case_eq((ApnA3 a n)); intros.
           rewrite H2 in H7. rewrite apfend_an in H7. easy.
           rewrite H2 in H7.
           rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a0) (s & [(s0, s'0, w'0)]))) in H7. simpl in H7.
           easy.
           apply refinementR3_mon.
       - case_eq b2; intros.
         + subst. simpl in H. simpl in H0.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b0) (p ! [(l, s', w')]))) in H1. simpl in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)).
           rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b0) w')). simpl.
           pinversion H1.
           subst.
           rewrite <- meqBp3 in H6, H9, H10.
           symmetry in H6.
           rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite eqb_neq in Ha.
           assert(isInB (BpnB3 b1 n) s = false).
           { case_eq n; intros.
             - simpl. easy.
             - rewrite <- InNS; easy.
           }
           specialize(pneqq6 (BpnB3 b1 n) s s3 s4 s0 s5 s'0
           (merge_bpf_cont b0 (p ! [(l, s', w')]))
           w'0 H H6
           ); intro HP.
           destruct HP as (b2,(HP1,(HP2,HP3))).
           case_eq(Bpf_eqb b0 b2); intros.
           ++ assert(b0 = b2).
              { apply bpf_eqb_eq. easy. }
              subst.
              assert((p ! [(l, s', w')]) = (s ! [(s0, s'0, w'0)])).
              { apply merge_same_beq in HP2. easy. }
              inversion H3. subst. easy.
           ++ assert(b0 <> b2).
              { apply bpf_eqb_neq. easy. }
              assert(merge_bpf_cont b0 (p ! [(l, s', w')]) = merge_bpf_cont b0 (p ! [(l, s', w')]) ) by easy.
              specialize(_39_1 b0 b2 p s
              (merge_bpf_cont b0 (p ! [(l, s', w')]))
              (p ! [(l, s', w')])
              (s ! [(s0, s'0, w'0)]) H0 HP1 H3 H4 HP2
              ); intro HQ.
              destruct HQ as [HQ | HQ].
              * destruct HQ as (c,(HQ1,(HQ2,(HQ3,HQ4)))).
                assert(s <> p) by easy.
                specialize(pneqq7 c s p l s0 s' s'0 w' w'0 H5 HQ1 HQ4); intro HP.
                destruct HP as (b3,(HPa,(HPb,HPc))).
                assert((s3 & [(s4, s5, merge_bpf_cont b0 w')]) = 
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) b0) w')).
                { rewrite(st_eq(merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) b0) w')). simpl.
                  easy.
                }
                rewrite H11.
                rewrite HPb.
                assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) b0) (merge_bpf_cont b3 (s ! [(s0, s'0, w'0)]))) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) (Bpf_merge b0 b3)) (s ! [(s0, s'0, w'0)]))).
                { rewrite !bareOrg1.
                  rewrite breOrg3. easy.
                }
                rewrite H12.
                pfold.
                specialize(ref3_b (upaco2 refinementR3 bot2)
                (merge_bpf_cont b w) w'0 s s0 s1 s'0
                (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) (Bpf_merge b0 b3)) 1 H7
                ); intro HR.
                simpl in HR.
                apply HR.
                apply InMergeFS.
                rewrite HQ3 in HP1.
                apply InMergeFS in HP1. easy.
                left.
                assert((merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b0 b3)) w'0) =
                       (merge_bpf_cont (bpf_receive s3 s4 s5 b0) (merge_bpf_cont b3 w'0))).
                { rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b0 b3)) w'0)).
                  rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b0) (merge_bpf_cont b3 w'0))). simpl.
                  rewrite breOrg3. easy.
                }
                rewrite H13.
                apply IHb  with (p := p) (l := l) (s := s2) (s' := s').
                easy. simpl. easy.
                rewrite HP3 in H9.
                rewrite HQ3 in H9.
                rewrite HPc in H9.
                assert((merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b0 (bpf_send p l s' b3))) w'0) =
                       (merge_bpf_cont (bpf_receive s3 s4 s5 b0) (p ! [(l, s', merge_bpf_cont b3 w'0)]))
                ).
                { rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b0 (bpf_send p l s' b3))) w'0)).
                  rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b0) (p ! [(l, s', merge_bpf_cont b3 w'0)]))).
                  simpl.
                  rewrite breOrg3.
                  rewrite(st_eq(merge_bpf_cont (bpf_send p l s' b3) w'0)).
                  simpl. easy.
                }
                rewrite H14 in H9.
                easy.
                admit.
              * destruct HQ as (c,(HQ1,(HQ2,(HQ3,HQ4)))).
                assert(s <> p) by easy.
                specialize(pneqq7 c p s s0 l s'0 s' w'0 w' Ha HQ1 HQ4); intro HP.
                destruct HP as (b3,(HPa,(HPb,HPc))).
                assert((s3 & [(s4, s5, merge_bpf_cont b0 w')]) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) b0) w')).
                { rewrite breOrg3. simpl.
                  rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 bpf_end) (merge_bpf_cont b0 w'))). simpl.
                  rewrite bpfend_bn. easy.
                }
                rewrite H11.
                rewrite HQ3.
                rewrite HPc.
                assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) (Bpf_merge b2 (bpf_send s s0 s'0 b3))) w') =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) b2) (s ! [(s0, s'0, merge_bpf_cont b3 w')]))).
                { rewrite !bareOrg1.
                  rewrite breOrg3.
                  rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s'0 b3) w')). simpl.
                  easy.
                }
                rewrite H12.
                
                pfold.
                specialize(ref3_b (upaco2 refinementR3 bot2)
                (merge_bpf_cont b w) (merge_bpf_cont b3 w') s s0 s1 s'0
                ((Bpf_merge (Ap2BpSeq (apf_receive s3 s4 s5 apf_end)) b2) ) 1 H7
                ); intro HR.
                simpl in HR.
                apply HR.
                easy.
                left.
                assert((merge_bpf_cont (bpf_receive s3 s4 s5 b2) (merge_bpf_cont b3 w')) =
                       (merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b2 b3)) w')).
                { rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b2) (merge_bpf_cont b3 w'))).
                  rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b2 b3)) w')). simpl.
                  rewrite breOrg3.
                  easy.
                }
                rewrite H13.
                apply IHb  with (p := p) (l := l) (s := s2) (s' := s').
                easy.
                simpl.
                apply InMergeFS. rewrite HQ3 in H0.
                apply InMergeFS in H0. easy.

                rewrite HP3 in H9.
                rewrite HPb in H9.
                assert((merge_bpf_cont (bpf_receive s3 s4 s5 b2) (merge_bpf_cont b3 (p ! [(l, s', w')]))) =
                       (merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b2 b3)) (p ! [(l, s', w')])) ).
                { rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 b2) (merge_bpf_cont b3 (p ! [(l, s', w')])))).
                  rewrite(st_eq(merge_bpf_cont (bpf_receive s3 s4 s5 (Bpf_merge b2 b3)) (p ! [(l, s', w')]))). simpl.
                  rewrite breOrg3. easy.
                }
                rewrite H14 in H9.
                easy.
                admit.
                apply refinementR3_mon.
         + subst.
           simpl in H. simpl in H0.
           rewrite orbtf in H0.
           destruct H0 as (Ha, Hb).
           rewrite eqb_neq in Ha.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 b0) (p ! [(l, s', w')]))) in H1. simpl in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 b0) w')).
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
           rewrite orbtf in H.
           destruct H as (Hc,Hd).
           rewrite eqb_neq in Hc.
           pinversion H1.
           subst.
           rewrite <- meqBp3 in H4, H7, H8.
           case_eq(eqb s s3); intros.
           ++ rewrite eqb_eq in H. subst.
              assert((BpnB3 b1 n) = bpf_end).
              { symmetry in H4. apply noPreS in H4. easy.
                case_eq n; intros.
                - simpl. easy.
                - rewrite <- InNS; easy.
              }
              rewrite H in H4.
              rewrite bpfend_bn in H4.
              inversion H4. subst.
              rewrite H in H7. 
              rewrite bpfend_bn in H7.
              specialize(ref3_b (upaco2 refinementR3 bot2)
              (merge_bpf_cont b w) (merge_bpf_cont b0 w') s3 s4 s1 s5
              bpf_end 1 H5
              ); intro HR.
              simpl in HR.
              rewrite !bpfend_bn in HR.
              pfold.
              apply HR.
              easy.
              left.
              apply IHb  with (p := p) (l := l) (s := s2) (s' := s'). 
              easy. easy. easy.
              admit.
           ++ rewrite eqb_neq in H.
              symmetry in H4.
              assert(isInB (BpnB3 b1 n) s = false).
              { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InNS; easy.
              }
              specialize(pneqq7 (BpnB3 b1 n) s s3 s4 s0 s5 s'0 
              (merge_bpf_cont b0 (p ! [(l, s', w')])) w'0 H H0 H4); intro HQ.
              destruct HQ as (b2,(HQ1,(HQ2,HQ3))).
              case_eq(Bpf_eqb b0 b2); intros.
              * assert (b0 = b2).
                { apply bpf_eqb_eq. easy. }
                subst.
                assert((p ! [(l, s', w')]) = (s ! [(s0, s'0, w'0)])).
                { apply merge_same_beq in HQ2. easy. }
                inversion H3. subst. easy.
              * assert (b0 <> b2).
                { apply bpf_eqb_neq. easy. }
                assert(merge_bpf_cont b0 (p ! [(l, s', w')]) = merge_bpf_cont b0 (p ! [(l, s', w')])) by easy.
                specialize(_39_1 b0 b2 p s
                (merge_bpf_cont b0 (p ! [(l, s', w')]))
                (p ! [(l, s', w')])
                (s ! [(s0, s'0, w'0)]) Hb HQ1 H3 H9 HQ2
                ); intro HP.
                destruct HP as [HP | HP].
                ** destruct HP as (c,(HPa,(HPb,(HPc,HPd)))).
                   assert(s <> p) by easy.
                   specialize(pneqq7 c s p l s0 s' s'0 w' w'0 H10 HPa HPd); intro HQ.
                   destruct HQ as (b3,(HQa,(HQb,HQc))).
                   rewrite HQb.
                   assert((s3 ! [(s4, s5, merge_bpf_cont b0 (merge_bpf_cont b3 (s ! [(s0, s'0, w'0)])))]) =
                          (merge_bpf_cont (bpf_send s3 s4 s5 (Bpf_merge b0 b3)) (s ! [(s0, s'0, w'0)]))).
                   { rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 (Bpf_merge b0 b3)) (s ! [(s0, s'0, w'0)]))). simpl.
                     rewrite breOrg3. easy.
                   }
                   rewrite H11.
                   pfold.
                   specialize(ref3_b (upaco2 refinementR3 bot2)
                   (merge_bpf_cont b w) w'0 s s0 s1 s'0
                   (bpf_send s3 s4 s5 (Bpf_merge b0 b3)) 1 H5
                   ); intro HR.
                   simpl in HR.
                   apply HR.
                   apply eqb_neq in H. rewrite H. simpl.
                   apply InMergeFS.
                   rewrite HPc in HQ1.
                   apply InMergeFS in HQ1.
                   easy.
                   left.
                   assert((merge_bpf_cont (bpf_send s3 s4 s5 (Bpf_merge b0 b3)) w'0) =
                          (merge_bpf_cont (bpf_send s3 s4 s5 b0) (merge_bpf_cont b3 w'0))).
                   { rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 (Bpf_merge b0 b3)) w'0)).
                     rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 b0) (merge_bpf_cont b3 w'0))). simpl.
                     rewrite breOrg3. easy.
                   }
                   rewrite H12.
                   apply IHb  with (p := p) (l := l) (s := s2) (s' := s').
                   easy. simpl.
                   apply eqb_neq in Ha. rewrite Ha. simpl. easy.
                   rewrite HQ3 in H7.
                   rewrite HPc in H7.
                   rewrite HQc in H7.
                   assert((merge_bpf_cont (bpf_send s3 s4 s5 (Bpf_merge b0 (bpf_send p l s' b3))) w'0) =
                          (merge_bpf_cont (bpf_send s3 s4 s5 b0) (p ! [(l, s', merge_bpf_cont b3 w'0)]))).
                   { rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 (Bpf_merge b0 (bpf_send p l s' b3))) w'0)).
                     rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 b0) (p ! [(l, s', merge_bpf_cont b3 w'0)]))). simpl.
                     rewrite breOrg3.
                     rewrite(st_eq(merge_bpf_cont (bpf_send p l s' b3) w'0)). simpl. easy.
                   }
                   rewrite H13 in H7. easy.
                   admit.
                ** destruct HP as (c,(HPa,(HPb,(HPc,HPd)))).
                   specialize(pneqq7 c p s s0 l s'0 s' w'0 w' Hc HPa HPd); intro HQ.
                   destruct HQ as (b3,(HQa,(HQb,HQc))).
                   rewrite HPc.
                   rewrite HQc.
                   assert((s3 ! [(s4, s5, merge_bpf_cont (Bpf_merge b2 (bpf_send s s0 s'0 b3)) w')]) =
                          (merge_bpf_cont (bpf_send s3 s4 s5 b2) (s ! [(s0, s'0, merge_bpf_cont b3 w')]))).
                   { rewrite(st_eq(merge_bpf_cont (bpf_send s3 s4 s5 b2) (s ! [(s0, s'0, merge_bpf_cont b3 w')]))). simpl.
                     rewrite breOrg3.
                     rewrite(st_eq (merge_bpf_cont (bpf_send s s0 s'0 b3) w')). simpl. easy.
                   }
                   rewrite H10.
                   pfold.
                   specialize(ref3_b (upaco2 refinementR3 bot2)
                   (merge_bpf_cont b w) (merge_bpf_cont b3 w') s s0 s1 s'0
                   (bpf_send s3 s4 s5 b2) 1 H5
                   ); intro HR.
                   simpl in HR.
                   apply HR.
                   apply eqb_neq in H. rewrite H. easy.
                   left.
                   assert((merge_bpf_cont (bpf_send s3 s4 s5 b2) (merge_bpf_cont b3 w')) =
                          (merge_bpf_cont (Bpf_merge (bpf_send s3 s4 s5 b2) b3) w')).
                   { rewrite breOrg3. easy. }
                   rewrite H11.
                   apply IHb  with (p := p) (l := l) (s := s2) (s' := s').
                   easy. simpl.
                   apply eqb_neq in Ha. rewrite Ha. simpl.
                   apply InMergeFS.
                   rewrite HPc in Hb.
                   apply InMergeFS in Hb.
                   easy.
                   rewrite HQ3 in H7.
                   rewrite HQb in H7.
                   assert((merge_bpf_cont (bpf_send s3 s4 s5 b2) (merge_bpf_cont b3 (p ! [(l, s', w')]))) =
                          (merge_bpf_cont (Bpf_merge (bpf_send s3 s4 s5 b2) b3) (p ! [(l, s', w')]))
                   ).
                   { rewrite breOrg3. easy. }
                   rewrite H12 in H7. easy.
                   admit.
                   apply refinementR3_mon.
         + subst.
           simpl in H.
           rewrite orbtf in H.
           destruct H as (Ha, Hb).
           rewrite eqb_neq in Ha.
           rewrite bpfend_bn in H1.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H1. simpl in H1.
           rewrite bpfend_bn.
           rewrite(st_eq (merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
           pinversion H1.
           subst.
           rewrite <- meqBp3 in H5, H8, H9.
           symmetry in H5.
           assert(s <> p) by easy.
           assert(isInB (BpnB3 b0 n) s = false).
           { case_eq n; intros.
             - simpl. easy.
             - rewrite <- InNS; easy.
           }
           specialize(pneqq7 (BpnB3 b0 n) s p l s0 s' s'0 w' w'0 H H2 H5); intro HQ.
           destruct HQ as (b3,(HQa,(HQb,HQc))).
           rewrite HQb.
           pfold.
           specialize(ref3_b (upaco2 refinementR3 bot2) (merge_bpf_cont b w)
           w'0 s s0 s1 s'0 b3 1 H6 HQa
           ); intro HR.
           simpl in HR.
           apply HR.
           left.
           specialize(IHb bpf_end p l s2 s' w (merge_bpf_cont b3 w'0)).
           rewrite !bpfend_bn in IHb.
           apply IHb. easy. easy.
           rewrite HQc in H8.
           rewrite(st_eq(merge_bpf_cont (bpf_send p l s' b3) w'0)) in H8. simpl in H8.
           easy.
           admit.
           apply refinementR3_mon.
      - rewrite bpfend_bn.
        rewrite bpfend_bn in H1.
        pinversion H1.
        subst.
        rewrite <- meqBp3 in H6, H9, H10.
        case_eq(Bpf_eqb (BpnB3 b n) b2); intros.
        + assert((BpnB3 b n) = b2).
          { apply bpf_eqb_eq. easy. }
          subst.
          assert((p ! [(l, s'0, w'0)]) = (p ! [(l, s', w')])).
          { apply merge_same_beq in H6. easy. }
          inversion H3. subst.
          easy.
        + assert((BpnB3 b n) <> b2).
          { apply bpf_eqb_neq. easy. }
          assert(merge_bpf_cont b2 (p ! [(l, s', w')]) = merge_bpf_cont b2 (p ! [(l, s', w')])) by easy.
          symmetry in H6.
          assert(isInB (BpnB3 b n) p = false).
           { case_eq n; intros.
             - simpl. easy.
             - rewrite <- InNS; easy.
           }
          assert(b2 <> BpnB3 b n) by easy.
          specialize(_39_1 b2 (BpnB3 b n) p p
          (merge_bpf_cont b2 (p ! [(l, s', w')]))
          (p ! [(l, s', w')])
          (p ! [(l, s'0, w'0)]) H0 H5 H11 H4 H6
          ); intro HP.
          destruct HP as [HP | HP].
          ++ destruct HP as (c,(HPa,(HPb,(HPc,HPd)))).
             assert(c = bpf_end).
             { apply noPreS in HPd; easy. }
             rewrite H12 in HPd.
             rewrite bpfend_bn in HPd.
             inversion HPd. subst.
             rewrite HPc in H9.
             assert((merge_bpf_cont (Bpf_merge b2 bpf_end) w'0) =
                    (merge_bpf_cont b2 w'0)).
             { rewrite breOrg3. rewrite bpfend_bn. easy. }
             rewrite H12 in H9.
             easy.
          ++ destruct HP as (c,(HPa,(HPb,(HPc,HPd)))).
             assert(c = bpf_end).
             { apply noPreS in HPd; easy. }
             rewrite H12 in HPd.
             rewrite bpfend_bn in HPd.
             inversion HPd. subst.
             assert((merge_bpf_cont (Bpf_merge (BpnB3 b n) bpf_end) w') =
                    (merge_bpf_cont (BpnB3 b n) w')).
             { rewrite breOrg3. rewrite bpfend_bn. easy. }
             rewrite H12.
             easy.
             apply refinementR3_mon.
Admitted.

Lemma end_send_false: forall b p l s w,
  end = merge_bpf_cont b (p ! [(l, s, w)]) -> False.
Proof. intros.
       case_eq b; intros.
       - subst. rewrite(st_eq(merge_bpf_cont (bpf_receive s0 s1 s2 b0) (p ! [(l, s, w)]))) in H.
         simpl in H. easy.
       - subst. rewrite(st_eq(merge_bpf_cont (bpf_send s0 s1 s2 b0) (p ! [(l, s, w)]))) in H.
         simpl in H. easy.
       - subst. rewrite bpfend_bn in H. easy.
Qed.

Lemma refTrans: Transitive (refinement3).
Proof. red. pcofix CIH.
       intros x y z Ha Hb.
       pinversion Ha.
       - subst. pinversion Hb.
         + subst. 
           case_eq(eqb p0 p); intros.
           + rewrite eqb_eq in H8. subst.
             rewrite <- meqAp3 in H1, H3, H6, H7.
             assert(isInA (ApnA3 a n) p = false).
             { case_eq n; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             assert((ApnA3 a n) = apf_end).
             { apply noPre in H3; easy. }
             rewrite H9 in H3.
             rewrite apfend_an in H3.
             inversion H3. subst.
             rewrite <- meqAp3.
             rewrite H9 in H1.
             rewrite apfend_an in H1.
             pfold.
             specialize(ref3_a (upaco2 refinementR3 r) w w'0 p l s s'0
             (ApnA3 a0 n0) 1 
             ); intro HR.
             simpl in HR.
             apply HR.
             apply ssTrans with (s2 := s'); easy.
             case_eq n0; intros.
             - simpl. easy.
             - rewrite <- InN; easy.
             right.
             apply CIH with (y := w').
             easy. easy.
             admit.
           + rewrite eqb_neq in H8.
             rename p0 into q.
             rewrite <- meqAp3 in H3.
             assert(p <> q) by easy.
             assert(isInA (ApnA3 a n) p = false).
             { case_eq n; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             specialize(pneqq4 (ApnA3 a n) p q l0 l s0 s' w0 w' H9 H10 H3); intros HR.
             destruct HR as (a',(Hnin,(HR1,HR2))).

             rewrite <- meqAp3.
             rewrite <- meqAp3 in H6, H7, H1, H2.
             rewrite HR1 in H6.

             subst.

             specialize(InvertAA a' (ApnA3 a0 n0) p l s' w' w'0 Hnin H6); intro HIn.

             destruct HIn as [HIn | HIn].
             destruct HIn as (a1,(a2,(s'',(Hc,(Hd,He))))).
             rewrite He.
             rewrite reOrd1.
             rewrite(st_eq(merge_apf_cont (apf_receive p l s'' a2) (q & [(l0, s'0, w'0)]))).
             simpl.
             pfold.
             assert(subsort s'' s).
             { apply ssTrans with (s2 := s'); easy. }
             specialize(ref3_a (upaco2 refinementR3 r) w (merge_apf_cont a2 (q & [(l0, s'0, w'0)]))
             p l s s'' a1 1 H11 Hc
             ); intro HR.
             simpl in HR.
             apply HR.

             rewrite HR2 in H1.
             rewrite(st_eq(merge_apf_cont (apf_receive q l0 s0 a') w')) in H1. simpl in H1.
             right.
             apply CIH with (y:= (q & [(l0, s0, merge_apf_cont a' w')])).
             easy.
             rewrite merge_merge.
             assert(isInA (ApnA3 a0 n0) q = false).
             { case_eq n0; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             assert(isInA (Apf_merge a1 a2) q = false).
             { rewrite He in H12.
               simpl in H12.
               apply isInFE1 with (p := p) (l := l) (s := s''); easy.
             }
             pfold.
             specialize(ref3_a (upaco2 refinementR3 bot2) (merge_apf_cont a' w') w'0
               q l0 s0 s'0 (Apf_merge a1 a2) 1 H4 H13
             ); intro HR3.
             simpl in HR3.
             apply HR3.
             rewrite He in H6.
             rewrite reOrg2 in H6.
             apply dropRA in H6.
             left.
             assert((merge_apf_cont a1 (merge_apf_cont a2 w'0)) =  (merge_apf_cont (Apf_merge a1 a2) w'0)).
             { rewrite merge_merge. easy. }
             rewrite <- H14.
             easy. easy. easy. easy.

             admit.
             admit.

             destruct HIn as (a1,(w1,(s'',(Hc,(Hd,(He,Hf)))))).
             rewrite Hf.
             assert(
             merge_apf_cont (ApnA3 a0 n0) (q & [(l0, s'0, merge_apf_cont a1 (p & [(l, s'', w1)]))]) =
             merge_apf_cont (Apf_merge (ApnA3 a0 n0) (apf_receive q l0 s'0 a1)) (p & [(l, s'', w1)])
             ).
             { rewrite reOrg2. easy. }
             rewrite H11.

             assert(subsort s'' s).
             { apply ssTrans with (s2 := s'); easy. }
             specialize(ref3_a (upaco2 refinementR3 r) w w1
             p l s s'' (Apf_merge (ApnA3 a0 n0) (apf_receive q l0 s'0 a1))
             1 H12
             ); intro HR.
             simpl in HR.
             pfold.
             apply HR.
             apply InMergeF.
             split. easy.
             simpl. rewrite orbtf. split.
             rewrite eqb_neq. easy. easy.

             rewrite HR2 in H1.
             rewrite(st_eq(merge_apf_cont (apf_receive q l0 s0 a') w')) in H1. simpl in H1.
             right.
             assert(
               merge_apf_cont (Apf_merge (ApnA3 a0 n0) (apf_receive q l0 s'0 a1)) w1 =
               merge_apf_cont (ApnA3 a0 n0) (q & [(l0, s'0, merge_apf_cont a1 w1)])
             ).
             { rewrite reOrg2. easy. }
             rewrite H13.
             apply CIH with (y := (q & [(l0, s0, merge_apf_cont a' w')])).
             easy.
             rewrite Hf in H6.
             rewrite merge_merge in H6.
             apply dropRA in H6.
             pfold.
             assert(isInA (ApnA3 a0 n0) q = false).
             { case_eq n0; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
             }
             specialize(ref3_a (upaco2 refinementR3 bot2) (merge_apf_cont a' w') (merge_apf_cont a1 w1)
               q l0 s0 s'0 (ApnA3 a0 n0) 1 H4 H14
             ); intro HR3.
             simpl in HR3.
             apply HR3.
             left.
             rewrite merge_merge.
             easy.
             admit. 
             easy.
             apply InMergeF. split. easy. easy.
             easy.
             admit.

             rewrite <- meqAp3 in H3.
             case_eq a; intros.
             - subst. rewrite apf_endN in H3.
               rewrite apfend_an in H3. easy.
             - subst.
               case_eq n; intros.
               + subst. simpl in H3. rewrite apfend_an in H3. easy.
               + subst. rewrite ApnA3C in H3. simpl in H3.
                 rewrite(st_eq(merge_apf_cont (apf_receive s1 s2 s3 (Apf_merge a0 (ApnA3 (apf_receive s1 s2 s3 a0) n1)))
                        (p & [(l, s', w')]))) in H3.
               simpl in H3. easy.
             subst.
             rewrite <- meqAp3 in H4.
             case_eq a; intros.
             - subst. rewrite apf_endN in H4.
               rewrite apfend_an in H4. easy.
             - subst.
               case_eq n; intros.
               + subst. simpl in H4. rewrite apfend_an in H4. easy.
               + subst. rewrite ApnA3C in H4. simpl in H4.
                 rewrite(st_eq(merge_apf_cont (apf_receive s0 s1 s2 (Apf_merge a0 (ApnA3 (apf_receive s0 s1 s2 a0) n0)))
                        (p & [(l, s', w')]))) in H4.
               simpl in H4. easy.
             apply refinementR3_mon.
             subst.

             (*send case*)
             subst.
             pinversion Hb.
             subst.
             rewrite <- meqBp3 in H3.
             rewrite <- meqAp3.
             specialize(mcAp2Bp2 (ApnA3 a n0) (p0 & [(l0, s'0, w'0)])); intro HHa.
             rewrite HHa.
             rename p0 into q.
             case_eq(eqb p q); intros.
             + rewrite eqb_eq in H8. subst.
               assert(isInB (BpnB3 b n) q = false).
               { case_eq n; intros.
                 - simpl. easy.
                 - rewrite <- InNS; easy.
               }
               specialize(pneqq6 (BpnB3 b n) q q l0 l s0 s' w0 w' H8 H3); intro HP.
               destruct HP as (b2,(HP1,(HP2,HP3))).
               rewrite <- meqAp3 in H6, H7.
               rewrite <- meqBp3 in H1, H2.
               assert(merge_bpf_cont (Ap2BpSeq (ApnA3 a n0)) (q & [(l0, s'0, w'0)]) =
                      merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) (bpf_receive q l0 s'0 bpf_end)) w'0).
               { rewrite breOrg3.
                 rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s'0 bpf_end) w'0)). simpl. 
                 rewrite bpfend_bn. easy.
               }
               rewrite H9.
               rewrite HP2 in H6.
               specialize(InvertBA b2 (ApnA3 a n0) q l s' w' w'0 HP1 H6); intro HQ.
               destruct HQ as (b1,(w1,(s1,(Hb1,(Hb2,Hb3))))).
               rewrite Hb3.
               pfold.
               assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) (bpf_receive q l0 s'0 bpf_end)) (merge_bpf_cont b1 (q ! [(l, s1, w1)]))) =
                      (merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) (bpf_receive q l0 s'0 b1)) (q ! [(l, s1, w1)]))).
               { rewrite !breOrg3.
                 rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s'0 bpf_end) (merge_bpf_cont b1 (q ! [(l, s1, w1)])))).
                 rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s'0 b1) (q ! [(l, s1, w1)]))).
                 simpl.
                 rewrite bpfend_bn. easy.
               }
               rewrite H10.
               specialize(ref3_b (upaco2 refinementR3 r) w w1 q l s s1
               (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) (bpf_receive q l0 s'0 b1)) 1
               ); intro HR.
               simpl in HR.
               apply HR.
               apply ssTrans with (s2 := s'); easy.
               simpl.
               apply InMergeFS. simpl. rewrite BisInAF. easy.
               right.
               apply CIH with (y := (merge_bpf_cont (BpnB3 b n) w')).
               easy.
               rewrite HP3.
               pfold.
               rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s0 b2) w')). simpl.
               assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) (bpf_receive q l0 s'0 b1)) w1) =
                      (merge_apf_cont (Apf_merge (ApnA3 a n0) (apf_receive q l0 s'0 apf_end)) (merge_bpf_cont b1 w1))).
               { rewrite bareOrg1.
                 rewrite reOrd1.
                 rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s'0 b1) w1)).
                 rewrite(st_eq(merge_apf_cont (apf_receive q l0 s'0 apf_end) (merge_bpf_cont b1 w1))).
                 simpl. rewrite apfend_an. easy.
               }
               rewrite H11.
               assert((merge_apf_cont (Apf_merge (ApnA3 a n0) (apf_receive q l0 s'0 apf_end)) (merge_bpf_cont b1 w1)) =
                      (merge_apf_cont (ApnA3 a n0) (q & [(l0, s'0, (merge_bpf_cont b1 w1))]))).
               { rewrite reOrd1.
                 rewrite(st_eq(merge_apf_cont (apf_receive q l0 s'0 apf_end) (merge_bpf_cont b1 w1))). simpl.
                 rewrite apfend_an. easy.
               }
               rewrite H12.
               rewrite Hb3 in H6.
               assert((merge_apf_cont (ApnA3 a n0) (merge_bpf_cont b1 (q ! [(l, s1, w1)]))) =
                      (merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) b1) (q ! [(l, s1, w1)]))).
               { rewrite bareOrg1. easy. }
               rewrite H13 in H6.
               apply dropBA in H6.
               specialize(ref3_a (upaco2 refinementR3 bot2) (merge_bpf_cont b2 w') (merge_bpf_cont b1 w1)
               q l0 s0 s'0 (ApnA3 a n0) 1 H4
               ); intro HR2.
               simpl in HR2.
               apply HR2.
               case_eq n0; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
               left.
               assert((merge_apf_cont (ApnA3 a n0) (merge_bpf_cont b1 w1)) = 
                      (merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) b1) w1)).
               { rewrite bareOrg1. easy. }
               rewrite H14. easy.
               admit.
               easy.
               apply InMergeFS. rewrite BisInAF. simpl. easy.
               admit.
             + rewrite eqb_neq in H8.
               assert(isInB (BpnB3 b n) p = false).
               { case_eq n; intros.
                - simpl. easy.
                - rewrite <- InNS; easy.
               }
               specialize(pneqq5 (BpnB3 b n) p q l0 l s0 s' w0 w' H8 H9 H3); intros HR.
               destruct HR as (b',(Hnin,(HR1,HR2))).
               rewrite HR1 in H6.
               rewrite <- meqAp3 in H6.
               rewrite <- meqBp3 in H1.
               specialize(InvertBA b' (ApnA3 a n0) p l s' w' w'0 Hnin H6); intro HIn.
               destruct HIn as (b2,(w1,(s'',(Hc,(Hd,He))))).
               (* use "InLBA" here *)
               rewrite He.
               assert((merge_bpf_cont (Ap2BpSeq (ApnA3 a n0))  (q & [(l0, s'0, merge_bpf_cont b2 (p ! [(l, s'', w1)]))])) =
                      (merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0))  (bpf_receive q l0 s'0 b2)) (p ! [(l, s'', w1)]))).
               { rewrite breOrg3.
                 rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s'0 b2) (p ! [(l, s'', w1)]))). simpl.
                 easy.
               }
               rewrite H10.
               rewrite HR2 in H1.
               rewrite He in H6.
               assert((merge_apf_cont (ApnA3 a n0) (merge_bpf_cont b2 (p ! [(l, s'', w1)]))) =
                      (merge_bpf_cont (Ap2BpSeq (ApnA3 a n0)) (merge_bpf_cont b2 (p ! [(l, s'', w1)])))).
               { rewrite mcAp2Bp2. easy. }
               rewrite H11 in H6.
(*                rewrite <- H8 in H6. *)
               pfold.
               specialize(ref3_b (upaco2 refinementR3 r) w w1 p l s s''
               (Bpf_merge (Ap2BpSeq (ApnA3 a n0))  (bpf_receive q l0 s'0 b2)) 1
               ); intro HR3.
               simpl in HR3.
               apply HR3.
               apply ssTrans with (s2 := s'); easy.
               simpl.
               apply InMergeFS. rewrite BisInAF. simpl. easy.
               right.
               apply CIH with (y := (merge_bpf_cont (bpf_receive q l0 s0 b') w')).
               easy.
               assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) (bpf_receive q l0 s'0 b2)) w1) =
                      (merge_apf_cont (ApnA3 a n0) (merge_bpf_cont (bpf_receive q l0 s'0 b2) w1))).
               { rewrite mcAp2Bp2.
                 rewrite breOrg3. easy.
               }
               rewrite H12.
               assert((merge_bpf_cont (Ap2BpSeq (ApnA3 a n0)) (merge_bpf_cont b2 (p ! [(l, s'', w1)]))) =
                      (merge_apf_cont (ApnA3 a n0) (merge_bpf_cont b2 (p ! [(l, s'', w1)])))).
               { rewrite mcAp2Bp2. easy. }
               rewrite H13 in H6.
               unfold refinement3.
               rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s0 b') w')).
               rewrite(st_eq(merge_bpf_cont (bpf_receive q l0 s'0 b2) w1)). simpl.
               specialize(ref3_a (upaco2 refinementR3 bot2) (merge_bpf_cont b' w') (merge_bpf_cont b2 w1)
               q l0 s0 s'0 (ApnA3 a n0) 1 H4
               ); intro HR4.
               simpl in HR4.
               pfold.
               apply HR4.
               case_eq n0; intros.
               - simpl. easy.
               - rewrite <- InN; easy.
               left.
               assert( (merge_apf_cont (ApnA3 a n0) (merge_bpf_cont b2 (p ! [(l, s'', w1)]))) =
                       (merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) b2) (p ! [(l, s'', w1)]))).
               { rewrite mcAp2Bp2. rewrite breOrg3. easy. }
               rewrite H14 in H6.
               apply dropBA in H6.
               assert((merge_bpf_cont (Bpf_merge (Ap2BpSeq (ApnA3 a n0)) b2) w1) = 
                      (merge_apf_cont (ApnA3 a n0) (merge_bpf_cont b2 w1))).
               { rewrite mcAp2Bp2. rewrite breOrg3. easy. }
                rewrite H15 in H6. easy.
                easy.
                apply InMergeFS. rewrite BisInAF. easy.
                admit.
                admit.

             subst.
             rewrite <- meqBp3 in H1, H3, H6, H7.
             rewrite <- meqBp3.
             case_eq(eqb p0 p); intros.
             + rewrite eqb_eq in H8. subst.
               assert((BpnB3 b n) = bpf_end).
               { apply noPreS in H3. easy.
                 case_eq n; intros.
                 - simpl. easy.
                 - rewrite <- InNS; easy.
               }
               rewrite H8 in H3.
               rewrite bpfend_bn in H3.
               inversion H3. subst.
               pfold.
               specialize(ref3_b (upaco2 refinementR3 r) w w'0
               p l s s'0 (BpnB3 b0 n0) 1
               ); intro HR.
               simpl in HR.
               apply HR.
               apply ssTrans with (s2 := s'); easy.
               case_eq n0; intros.
               - simpl. easy.
               - rewrite <- InNS; easy.
               right.
               apply CIH with (y := (merge_bpf_cont (BpnB3 b n) w')).
               easy.
               rewrite H8. rewrite bpfend_bn. easy.
               admit.
             + rewrite eqb_neq in H8.
               assert(p <> p0) by easy.
               assert(isInB (BpnB3 b n) p = false).
               { case_eq n; intros.
                 - simpl. easy.
                 - rewrite <- InNS; easy.
               }
               specialize(pneqq7 (BpnB3 b n) p p0 l0 l s0 s' w0 w' H9 H10 H3); intro HP.
               destruct HP as (b1,(HPa,(HPb,HPc))).
               rewrite HPb in H6.
               specialize(InvertBB b1 (BpnB3 b0 n0) p l s' w' w'0 HPa H6); intro HBB.
               destruct HBB as [HBB | HBB].
               ++ destruct HBB as (b2,(b3,(s2,(HBa,(HBb,HBc))))).
                  rewrite HBc.
                  assert((merge_bpf_cont (Bpf_merge b2 (bpf_send p l s2 b3)) (p0 ! [(l0, s'0, w'0)])) =
                         (merge_bpf_cont b2 (p ! [(l, s2, merge_bpf_cont b3  (p0 ! [(l0, s'0, w'0)]))]))).
                  { rewrite breOrg3.
                    rewrite(st_eq(merge_bpf_cont (bpf_send p l s2 b3) (p0 ! [(l0, s'0, w'0)]))). simpl.
                    easy.
                  }
                  rewrite H11.
                  pfold.
                  specialize(ref3_b (upaco2 refinementR3 r)
                  w (merge_bpf_cont b3 (p0 ! [(l0, s'0, w'0)]))
                  p l s s2 b2 1
                  ); intro HR.
                  simpl in HR.
                  apply HR.
                  apply ssTrans with (s2 := s'); easy.
                  easy.
                  right.
                  apply CIH with (y := (merge_bpf_cont (BpnB3 b n) w')).
                  easy.
                  rewrite HPc.
                  rewrite(st_eq(merge_bpf_cont (bpf_send p0 l0 s0 b1) w')). simpl.
                  assert((merge_bpf_cont b2 (merge_bpf_cont b3 (p0 ! [(l0, s'0, w'0)]))) =
                         (merge_bpf_cont (Bpf_merge b2 b3) (p0 ! [(l0, s'0, w'0)]))).
                  { rewrite breOrg3. easy. }
                  rewrite H12.
                  pfold.
                  specialize(ref3_b (upaco2 refinementR3 bot2) 
                  (merge_bpf_cont b1 w') w'0 p0 l0 s0 s'0
                  (Bpf_merge b2 b3) 1 H4
                  ); intros HR2.
                  simpl in HR2.
                  apply HR2.
                  apply InMergeFS.
                  assert(isInB (BpnB3 b0 n0) p0 = false) as Hp0.
                  { case_eq n0; intros.
                    - simpl. easy.
                    - rewrite <- InNS; easy.
                  }
                  rewrite HBc in Hp0.
                  apply InMergeFS in Hp0. simpl in Hp0.
                  destruct Hp0 as (Hp0, Hp0').
                  rewrite orbtf in Hp0'. easy.
                  left. 
                  rewrite HBc in H6.
                  assert((merge_bpf_cont (Bpf_merge b2 (bpf_send p l s2 b3)) w'0) =
                         (merge_bpf_cont b2 (p ! [(l, s2, merge_bpf_cont b3 w'0)]))).
                  { rewrite breOrg1. easy. }
                  rewrite H13 in H6.
                  apply dropBA in H6.
                  assert((merge_bpf_cont b2 (merge_bpf_cont b3 w'0)) =
                         merge_bpf_cont (Bpf_merge b2 b3) w'0).
                  { rewrite breOrg3. easy. }
                  rewrite H14 in H6. easy.
                  easy. easy.
                  admit.
                  admit.
               ++ destruct HBB as (b2,(w2,(s2,(HBa,(HBb,(HBc,HBd)))))).
                  rewrite HBd.
                  assert((merge_bpf_cont (BpnB3 b0 n0) (p0 ! [(l0, s'0, merge_bpf_cont b2 (p ! [(l, s2, w2)]))])) =
                         (merge_bpf_cont (Bpf_merge (BpnB3 b0 n0) (bpf_send p0 l0 s'0 b2)) (p ! [(l, s2, w2)]))).
                  { rewrite breOrg3.
                    rewrite(st_eq(merge_bpf_cont (bpf_send p0 l0 s'0 b2) (p ! [(l, s2, w2)]))). simpl. easy.
                  }
                  rewrite H11.
                  pfold.
                  specialize(ref3_b (upaco2 refinementR3 r) w w2 p l s s2
                  (Bpf_merge (BpnB3 b0 n0) (bpf_send p0 l0 s'0 b2)) 1
                  ); intro HR.
                  simpl in HR.
                  apply HR.
                  apply ssTrans with (s2 := s'); easy.
                  simpl.
                  apply InMergeFS.
                  simpl. rewrite HBa. apply eqb_neq in H9. rewrite H9. simpl. easy.
                  right.
                  apply CIH with (y := (merge_bpf_cont (BpnB3 b n) w')).
                  easy.
                  rewrite HPc.
                  rewrite(st_eq(merge_bpf_cont (bpf_send p0 l0 s0 b1) w')). simpl.
                  assert((merge_bpf_cont (Bpf_merge (BpnB3 b0 n0) (bpf_send p0 l0 s'0 b2)) w2) =
                         (merge_bpf_cont (BpnB3 b0 n0) (p0 ! [(l0, s'0, merge_bpf_cont b2 w2)]))).
                  { rewrite breOrg3.
                    rewrite(st_eq (merge_bpf_cont (bpf_send p0 l0 s'0 b2) w2)). simpl. easy.
                  }
                  rewrite H12.
                  pfold.
                  specialize(ref3_b (upaco2 refinementR3 bot2) (merge_bpf_cont b1 w')
                  (merge_bpf_cont b2 w2) p0 l0 s0 s'0
                  (BpnB3 b0 n0) 1 H4
                  ); intro HR2.
                  simpl in HR2.
                  apply HR2.
                  case_eq n0; intros.
                  - simpl. easy.
                  - rewrite <- InNS; easy.
                  left.
                  rewrite HBd in H6.
                  assert((merge_bpf_cont (BpnB3 b0 n0) (merge_bpf_cont b2 (p ! [(l, s2, w2)]))) =
                         (merge_bpf_cont (Bpf_merge (BpnB3 b0 n0) b2) (p ! [(l, s2, w2)]))).
                  { rewrite breOrg3. easy. }
                  rewrite H13 in H6.
                  apply dropBA in H6.
                  assert((merge_bpf_cont (Bpf_merge (BpnB3 b0 n0) b2) w2) =
                         (merge_bpf_cont (BpnB3 b0 n0) (merge_bpf_cont b2 w2))).
                  { rewrite breOrg3. easy. }
                  rewrite H14 in H6. easy. easy.
                  apply InMergeFS. easy.
                  admit.
                  admit.
             subst.
             rewrite <- meqBp3 in H4.
             apply end_send_false in H4. easy.
             apply refinementR3_mon.
             (*end case*)
             subst.
             pinversion Hb.
             pfold.
             constructor.
             apply refinementR3_mon.
             apply refinementR3_mon.
Admitted.
