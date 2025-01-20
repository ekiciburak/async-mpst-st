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


