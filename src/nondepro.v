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

Lemma ApnA3C: forall n a, ApnA3 a n.+1 =  Apf_merge a (ApnA3 a n).
Proof. intros.
       simpl.
       case_eq n; intros.
       - simpl. rewrite mergel. easy.
       - easy.
Qed.

Lemma apfend_an: forall w, merge_apf_cont apf_end w = w.
Proof. intros.
       case_eq w; intros.
       - rewrite(st_eq(merge_apf_cont apf_end (end))). simpl. easy.
       - rewrite(st_eq(merge_apf_cont apf_end (s & l) )). simpl. easy.
       - rewrite(st_eq(merge_apf_cont apf_end (s ! l))). simpl. easy.
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

Lemma meqAp3: forall n a w, merge_apf_cont (ApnA3 a n) w = merge_apf_contn a w n.
Proof. intro n.
       induction n; intros.
       - simpl. rewrite apfend_an. easy.
       - rewrite ApnA3C.
         rewrite meqApH. rewrite IHn.
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

Lemma _39_1: forall a b p q w w1 w2,
  isInB a p = false ->
  isInB b q = false ->
  a <> b ->
  w = merge_bpf_cont a w1 ->
  w = merge_bpf_cont b w2 ->
  (
    (exists c, isInB c q = false ->
      w = merge_bpf_cont a (merge_bpf_cont c w2) /\ b = Bpf_merge a c /\ w1 = merge_bpf_cont c w2)
    \/
    (exists c, isInB c p = false ->
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
              intro Ha.
              specialize(IHa Ha).
              destruct IHa as (Hb,(Hc,Hd)).
              split.
              rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_receive s2 s3 s4 a) (merge_bpf_cont c w2))). simpl.
              rewrite Hb. easy.
              split. rewrite Hc. easy.
              easy.
           ++ destruct IHa as (c,IHa).
              right. exists c.
              intro Ha.
              specialize(IHa Ha).
              destruct IHa as (Hb,(Hc,Hd)).
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
           intro Ha.
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
              intro He.
              specialize(IHa He).
              destruct IHa as (Hf,(Hg,Hi)).
              split. 
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 a) (merge_bpf_cont c w2))).
              simpl.
              rewrite Hf. easy.
              split. simpl. rewrite Hg. easy.
              easy.
           ++ destruct IHa as (c,IHa).
              right. exists c.
              intro He.
              specialize(IHa He).
              destruct IHa as (Hf,(Hg,Hi)).
              split. 
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 a) w1)).
              rewrite(st_eq(merge_bpf_cont (bpf_send s2 s3 s4 b0) (merge_bpf_cont c w1))).
              simpl.
              rewrite Hf. easy.
              split. simpl. rewrite Hg. easy.
              easy.
         + subst.
           right. exists(bpf_send s s0 s1 a).
           intro Ha.
           split. rewrite bpfend_an. easy.
           split. simpl. easy.
           rewrite bpfend_an in H3. easy.
       - rewrite bpfend_an in H2.
         case_eq b; intros.
         + subst.
           left. exists(bpf_receive s s0 s1 b0).
           intro Ha.
           split. rewrite bpfend_an. easy.
           split. simpl. easy.
           easy.
         + subst.
           left. exists(bpf_send s s0 s1 b0).
           intro Ha.
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
    (exists c, isInA c q = false ->
      w = merge_apf_cont a (merge_apf_cont c w2) /\ b = Apf_merge a c /\ w1 = merge_apf_cont c w2)
    \/
    (exists c, isInA c p = false ->
      w = merge_apf_cont b (merge_apf_cont c w1) /\ a = Apf_merge b c /\ w2 = merge_apf_cont c w1)
  ).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H2.
         case_eq b; intros.
         + subst. easy.
         + subst. simpl in H0.
           left. exists (apf_receive s s0 s1 a).
           simpl. intro Ha.
           split. rewrite !apfend_an. easy.
           split. easy.
           easy.
       - case_eq b; intros.
         + subst.
           right. exists(apf_receive s s0 s1 a).
           intro Ha.
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
              left. exists c.
              intro He.
              specialize(IHa He).
              destruct IHa as (Hf,(Hg,Hi)).
              split.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a) w1)). simpl.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a) (merge_apf_cont c w2))). simpl.
              rewrite Hf. easy.
              split. simpl. rewrite Hg. easy.
              easy.
           ++ destruct IHa as (c, IHa).
              right. exists c.
              intro He.
              specialize(IHa He).
              destruct IHa as (Hf,(Hg,Hi)).
              split.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a) w1)). simpl.
              rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) (merge_apf_cont c w1))). simpl.
              rewrite Hf. easy.
              split. simpl. rewrite Hg. easy.
              easy.
Qed.

Lemma _39_3: forall b a p q w w1 w2,
  isInB b p = false ->
  isInA a q = false ->
  w = merge_bpf_cont b w1 ->
  w = merge_apf_cont a w2 ->
  isBpSend b = true ->
  (exists c,
   isInB c p = false ->
   w = merge_bpf_cont (Ap2BpSeq a) (merge_bpf_cont c w1) /\ b = Bpf_merge (Ap2BpSeq a) c /\ w2 = merge_bpf_cont c w1).
Proof. intro b.
       induction b; intros.
       - case_eq a; intros.
         + subst. rewrite apfend_an in H2.
           simpl in H. simpl. 
           exists(bpf_receive s s0 s1 b).
           intro Ha.
           split. rewrite bpfend_an. easy.
           split. easy.
           easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w1)) in H2.
           rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) w2)) in H2.
           simpl in H2.
           inversion H2. subst.
           simpl.
           specialize(IHb a0 p q (merge_bpf_cont b w1) w1 w2).
           simpl in H. simpl in H0.
           rewrite orbtf in H0.
           destruct H0 as (Ha, Hb).
           assert(merge_bpf_cont b w1 = merge_bpf_cont b w1) by easy.
           simpl in H3.
           specialize(IHb H Hb H0 H7 H3).
           destruct IHb as (c,IHb).
           exists c.
           intro Hc.
           specialize(IHb Hc).
           destruct IHb as (Hd,(He,Hf)).
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
           intro Ha.
           split. rewrite bpfend_an. easy.
           split. easy. 
           rewrite apfend_an in H2. easy.
         + subst.
           rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w1)) in H2.
           rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) w2)) in H2.
           simpl in H2. easy.
       - simpl in H3. easy.
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

Lemma inH1: forall b a p l s w w',
   merge_apf_cont a (p & [(l, s, w)]) = merge_apf_cont b w' ->
   isInAl b p l = false -> 
   coseqInl (p, rcv, l) (actl w').
Proof. intro b.
       induction b; intros.
       - rewrite apfend_an in H.
         rewrite <- H.
         apply inH0.
       - case_eq a; intros.
         + subst.
           rewrite apfend_an in H.
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 b) w')) in H.
           simpl in H.
           inversion H. subst.
            
           simpl in H0.
           rewrite orbtf in H0. 
           destruct H0.
           rewrite !eqb_refl in H0. easy.
         + subst.
           rewrite(st_eq(merge_apf_cont (apf_receive s3 s4 s5 a0) (p & [(l, s2, w)]))) in H.
           rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 b) w')) in H.
           simpl in H.
           inversion H. subst.
           simpl in H0.

           rewrite orbtf in H0.
           destruct H0 as (Ha, Hb).
           specialize(IHb a0 p l s2 w w' H5 Hb).
           easy.
Qed.

Lemma inH2: forall b a p l w w', 
  merge_apf_cont a w = merge_apf_cont b w' ->
  isInAl a p l ->
  isInAl b p l \/ coseqInl (p, rcv, l) (actl w').
Proof. intro b.
       induction b; intros.
       - case_eq a; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. 
           rewrite apfend_an in H.
           apply Bool.orb_true_iff in H0.
           destruct H0 as [Ha | Ha].
           ++ apply Bool.andb_true_iff in Ha.
              destruct Ha as (Ha,Hb).
              rewrite eqb_eq in Ha.
              rewrite eqb_eq in Hb.
              subst.
              admit.
           ++ simpl.
              rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a0) w )) in H.
              simpl in H.
              admit.
       - simpl. 
         case_eq a; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0.
           rewrite(st_eq(merge_apf_cont (apf_receive s2 s3 s4 a0) w)) in H.
           rewrite(st_eq( merge_apf_cont (apf_receive s s0 s1 b) w')) in H.
           simpl in H.
           inversion H. subst.
           apply Bool.orb_true_iff in H0.
           destruct H0 as [Ha | Ha].
           ++ left. admit.
           ++ specialize(IHb a0 p l w w' H5 Ha).
              destruct IHb as [IHb | IHb].
              * left. rewrite IHb.
                apply Bool.orb_true_iff. right. easy.
              * right. easy.
Admitted.

Lemma inH3: forall b a p l w w', 
  merge_apf_cont a w = merge_apf_cont b w' ->
  coseqInl (p, rcv, l) (actl w) ->
  isInAl b p l \/ coseqInl (p, rcv, l) (actl w').
Admitted.

Lemma InL: forall a b p l s w w', 
  isInA a p = false ->
  paco2 refinementR3 bot2 (merge_apf_cont a (p & [(l, s, w)])) (merge_apf_cont b w') ->
  isInAl b p l \/ coseqInl (p, rcv, l) (actl w').
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
              rewrite(coseq_eq(actl (p & [(l, s', w'0)]))). unfold coseq_id. simpl.
              apply CoInSplit1l with (y := (p, rcv, l)) (ys := (actl w'0)). simpl. easy. easy.
              case_eq(isInAl b p l); intros.
              * left. easy.
              * assert (isInA b p = false) by admit.
                right.
                specialize(inH1 b (ApnA3 a n) p l s' w'0 w' H5 H2); intro Hin.
                easy.
                admit.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H0.
         simpl in H0. simpl in H.
         pinversion H0.
         subst.
         rewrite <- meqAp3 in H5, H8, H9.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         specialize(IHa (ApnA3 a0 n) p l s2 w w'0 Hb H8).
         destruct IHa as [IHa | IHa].
         ++ specialize(inH2 b (ApnA3 a0 n) p l (s & [(s0, s', w'0)]) w' H5 IHa); intro Hin. easy.
         ++ specialize(inH3 b (ApnA3 a0 n) p l (s & [(s0, s', w'0)]) w' H5 ); intro Hin.
            apply Hin.
            rewrite(coseq_eq(actl (s & [(s0, s', w'0)]))). unfold coseq_id. simpl.
            apply CoInSplit2l with (y := (s, rcv, s0)) (ys := (actl w'0)).
            simpl. easy. 
            rewrite eqb_neq in Ha.
            unfold not. intros. apply Ha. inversion H. easy.
            easy.
            admit.
Admitted.

Lemma refTrans: Transitive (refinement3).
Proof. red. pcofix CIH.
       intros x y z Ha Hb.
       pinversion Ha.
       - subst. pinversion Hb.
         + subst. 
           case_eq(eqb p0 p); intros.
           + rewrite eqb_eq in H8. subst.
             admit.
           + rewrite eqb_neq in H8.
             rename p0 into q.
             rewrite <- meqAp3 in H3.
             assert(p <> q) by easy.
             specialize(pneqq3 (ApnA3 a n) p q l0 l s0 s' w0 w' H9 H3); intros HR.
             destruct HR as (a',(HR1,HR2)).
             assert(isInA a' p = false) by admit.
             rewrite <- meqAp3.
             rewrite <- meqAp3 in H6, H7, H1, H2.
Admitted.

