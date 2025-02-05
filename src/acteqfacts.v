Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.reorderingfacts ST.src.siso ST.types.local ST.subtyping.refinement.
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

Lemma orbtf: forall b1 b2 : bool, b1 || b2 = false <-> b1 = false /\ b2 = false.
Proof. intro b1.
       case_eq b1; intros.
       - simpl. split; easy.
       - case_eq b2; intros.
         + split; easy.
         + split; easy.
Defined.


Fixpoint dropE (l: list (string*dir)) (a: string*dir): list (string*dir) :=
  match l with
    | nil       => nil
    | (p,d)::xs => if (eqb p (fst a) && direqb d (Datatypes.snd a)) then dropE xs a else (p,d)::dropE xs a
  end. 

Definition sdir_eqb (a1 a2: string * dir): bool :=
  match (a1, a2) with
    | ((p1,d1), (p2,d2)) => eqb p1 p2 && direqb d1 d2
  end.

Lemma dlN: forall l x a, x <> a -> (dropE (x :: l) a) = x :: (dropE l a).
Proof. intro l.
       induction l; intros.
       - destruct x as (p,d).
         destruct a as (p1,d1). simpl.
         case_eq(eqb p p1); intros.
         + simpl. rewrite eqb_eq in H0. subst.
           case_eq(direqb d d1); intros.
           ++ apply dir_eqb_eq in H0. subst. easy.
           ++ easy.
         + simpl. easy.
       - destruct x as (p,d).
         destruct a as (p1,d1).
         destruct a0 as (p2,d2). simpl.
         case_eq(eqb p p2); intros.
         + rewrite eqb_eq in H0. subst. simpl.
           case_eq(direqb d d2); intros.
           ++ apply dir_eqb_eq in H0. subst. easy.
           ++ easy.
         + simpl. easy.
Qed.

Lemma direqb_refl: forall d, direqb d d = true.
Proof. destruct d; easy. Qed.

Lemma dl: forall l a, dropE (a :: l) a = (dropE l a).
Proof. intros.
       destruct a as (p,d). simpl.
       rewrite eqb_refl. 
       rewrite direqb_refl.
       simpl. easy.
Qed.

Lemma sdir_eqb_eq: forall x a, sdir_eqb x a = true <-> x = a.
Proof. intros x a.
       destruct x as (p,d).
       destruct a as (p1,d1).
       split.
       - intro Ha. unfold sdir_eqb in Ha.
         rewrite Bool.andb_true_iff in Ha.
         destruct Ha as (Ha,Hb).
         rewrite eqb_eq in Ha.
         apply dir_eqb_eq in Hb.
         subst. easy.
       - intro Hb.
         unfold sdir_eqb.
         inversion Hb.
         subst.
         rewrite eqb_refl.
         simpl.
         rewrite direqb_refl; easy.
Qed.

Lemma sdir_eqb_neq: forall x a, sdir_eqb x a = false <-> x <> a.
Proof. intros.
       destruct x as (p,d).
       destruct a as (p1,d1).
       split.
       - intro Ha.
         unfold sdir_eqb in Ha.
         rewrite Bool.andb_false_iff in Ha.
         destruct Ha as [Ha | Ha].
         + rewrite eqb_neq in Ha.
           unfold not. intro Hb.
           apply Ha.
           inversion Hb; easy.
         + apply dir_neqb_neq in Ha.
           unfold not. intro Hb.
           apply Ha.
           inversion Hb; easy.
       - intro Ha.
         unfold sdir_eqb.
         case_eq(eqb p p1); intros.
         + simpl.
           rewrite eqb_eq in H. subst.
           destruct d; destruct d1; subst; easy.
         + simpl. easy.
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

Lemma dropEList: forall l x a,
  In x l ->
  x <> a ->
  In x (dropE l a).
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - simpl in H.
         destruct H as [H | H].
         + subst.
           assert((dropE (x :: l) a0) = x :: (dropE l a0)).
           { apply dlN; easy. }
           rewrite H.
           simpl. left. easy.
         + case_eq(sdir_eqb x a); intros.
           ++ assert(a = x).
              { apply sdir_eqb_eq in H1; easy. }
              subst. 
              assert((dropE (x :: l) a0) = x :: (dropE l a0)).
              { apply dlN; easy. }
              rewrite H2. simpl. left. easy.
           ++ assert(a <> x).
              { apply sdir_eqb_neq in H1; easy. }
              case_eq(sdir_eqb a0 a); intros.
              * assert(a = a0).
                { apply sdir_eqb_eq in H3; easy. }
                subst.
                assert((dropE (a0 :: l) a0) = (dropE l a0)).
                { rewrite dl. easy. }
                rewrite H4.
                apply IHl; easy.
              * assert(a <> a0).
                { apply sdir_eqb_neq in H3; easy. }
                assert((dropE (a :: l) a0) = a::(dropE l a0)).
                { rewrite dlN; easy. }
                rewrite H5.
                simpl. right.
                apply IHl; easy.
Qed.

Lemma coseq2InLCS: forall l1 p s,
  (coseqIn (p, snd) s -> False) -> 
  In (p, snd) l1 ->
  paco2 coseqInL bot2 s l1 ->
  coseqInLC s (dropE l1 (p, snd)).
Proof. pcofix CIH.
       intros.
       pinversion H2.
       - subst.
         pfold.
         constructor.
       - subst. pfold.
         constructor.
         assert(x <> (p, snd)).
         { unfold not. intro Ha.
           apply H0. subst. 
           apply CoInSplit1 with (y := (p, snd)) (ys := xs); easy.
         }
         apply dropEList; easy.
         right.
         apply CIH.
         intro Ha.
         apply H0.
         apply CoInSplit2 with (y := x) (ys := xs).
         simpl. easy.
         unfold not. intro Hb.
         apply H0.
         subst.
         apply CoInSplit1 with (y := (p, snd)) (ys := xs); easy.
         easy. easy.
         easy.
         apply coseqInLC_mon.
Qed.

Lemma coseq2InLCR: forall l1 p s,
  (coseqIn (p, rcv) s -> False) -> 
  In (p, rcv) l1 ->
  paco2 coseqInL bot2 s l1 ->
  coseqInLC s (dropE l1 (p, rcv)).
Proof. pcofix CIH.
       intros.
       pinversion H2.
       - subst.
         pfold.
         constructor.
       - subst. pfold.
         constructor.
         assert(x <> (p, rcv)).
         { unfold not. intro Ha.
           apply H0. subst. 
           apply CoInSplit1 with (y := (p, rcv)) (ys := xs); easy.
         }
         apply dropEList; easy.
         right.
         apply CIH.
         intro Ha.
         apply H0.
         apply CoInSplit2 with (y := x) (ys := xs).
         simpl. easy.
         unfold not. intro Hb.
         apply H0.
         subst.
         apply CoInSplit1 with (y := (p, rcv)) (ys := xs); easy.
         easy. easy.
         easy.
         apply coseqInLC_mon.
Qed.

Lemma coseq_ninS: forall b a p l s w,
  a <> (p, snd) ->
  coseqIn a (act (merge_bpf_cont b (p ! [(l, s, w)]))) ->
  coseqIn a (act (merge_bpf_cont b w)).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq (merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))) in H0. simpl in H0.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))) in H0. unfold coseq_id in H0.
         simpl in H0.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         inversion H0.
         + subst. simpl in H1.
           inversion H1. subst.
           apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w))).
           simpl. easy. easy.
         + subst. simpl in H1.
           inversion H1. subst.
           apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w))).
           easy. easy.
           apply IHb with (p := p) (l := l) (s := s2); easy.
       - rewrite(st_eq (merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H0. simpl in H0.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))) in H0. unfold coseq_id in H0.
         simpl in H0.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         inversion H0.
         + subst. simpl in H1.
           inversion H1. subst.
           apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))).
           simpl. easy. easy.
         + subst. simpl in H1.
           inversion H1. subst.
           apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))).
           easy. easy.
           apply IHb with (p := p) (l := l) (s := s2); easy.
       - rewrite bpfend_bn.
         rewrite bpfend_bn in H0.
         inversion H0.
         + subst. inversion H1. subst. easy.
         + subst. simpl in H1. inversion H1. subst. easy.
Qed.

Lemma coseq_inS: forall b p w,
  coseqIn (p, snd) (act w) ->
  coseqIn (p, snd) (act (merge_bpf_cont b w)).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
         rewrite(coseq_eq (act (s & [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w))).
         simpl. easy. easy.
         apply IHb. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
         rewrite(coseq_eq (act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         case_eq(eqb p s); intros.
         + rewrite eqb_eq in H0.
           subst.
           apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))).
           simpl. easy. easy.
         + rewrite eqb_neq in H0.
           apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w))).
           simpl. easy.
           unfold not. intro Ha.
           apply H0. inversion Ha. easy.
           apply IHb. easy.
       - rewrite bpfend_bn.
         easy.
Qed.

Lemma coseq_ninSR: forall b a p l s w,
  coseqIn a (act (merge_bpf_cont b w)) ->
  coseqIn a (act (merge_bpf_cont b (p ! [(l, s, w)]))).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq (act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         inversion H.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         apply IHb. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq (act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         inversion H.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         apply IHb. easy.
       - rewrite bpfend_bn. rewrite bpfend_bn in H.
         rewrite(coseq_eq(act (p ! [(l, s, w)]))). unfold coseq_id. simpl.
         case_eq a; intros.
         + rename s0 into q.
           destruct d.
           ++ subst. 
              apply CoInSplit2 with (y := (p, snd)) (ys := (act w) ). simpl. easy. easy. easy.
           ++ subst. 
              case_eq(eqb p q); intros.
              * rewrite eqb_eq in H0. subst.
                apply CoInSplit1 with (y := (q, snd)) (ys := (act w) ). simpl. easy. easy.
              * rewrite eqb_neq in H0.
                apply CoInSplit2 with (y := (p, snd)) (ys := (act w) ). simpl. easy.
                unfold not. intro Ha. apply H0. inversion Ha. easy.
                easy.
Qed.

Lemma coseq_ninRR: forall b a p l s w,
  coseqIn a (act (merge_apf_cont b w)) ->
  coseqIn a (act (merge_apf_cont b (p & [(l, s, w)]))).
Proof. intro b.
       induction b; intros.
       - rewrite apfend_an. rewrite apfend_an in H.
         rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
         case_eq a; intros.
         + rename s0 into q.
           destruct d.
           ++ subst. 
              case_eq(eqb p q); intros.
              * rewrite eqb_eq in H0. subst.
                apply CoInSplit1 with (y := (q, rcv)) (ys := (act w) ). simpl. easy. easy.
              * rewrite eqb_neq in H0.
                apply CoInSplit2 with (y := (p, rcv)) (ys := (act w) ). simpl. easy.
                unfold not. intro Ha. apply H0. inversion Ha. easy.
                easy.
           ++ subst. 
              apply CoInSplit2 with (y := (p, rcv)) (ys := (act w) ). simpl. easy. easy. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 b) (p & [(l, s2, w)]))). simpl.
         rewrite(coseq_eq (act (s & [(s0, s1, merge_apf_cont b (p & [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         inversion H.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_apf_cont b (p & [(l, s2, w)]))) ). simpl. easy. easy.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_apf_cont b (p & [(l, s2, w)]))) ). simpl. easy. easy.
         apply IHb. easy.
Qed.

Lemma coseq_inR: forall a p w,
  coseqIn (p, rcv) (act w) ->
  coseqIn (p, rcv) (act (merge_apf_cont a w)).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         case_eq(eqb p s); intros.
         + rewrite eqb_eq in H0. subst.
           apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w))). simpl. easy. easy.
         + rewrite eqb_neq in H0.
           apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w))). simpl. easy.
           unfold not. intro Ha. apply H0. inversion Ha. easy.
           apply IHa. easy.
Qed.

Lemma coseq_ninR: forall a x p l s w,
  x <> (p, rcv) ->
  coseqIn x (act (merge_apf_cont a (p & [(l, s, w)]))) ->
  coseqIn x (act (merge_apf_cont a w)).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. rewrite apfend_an in H0.
         inversion H0.
         subst. simpl in H1. inversion H1. subst. easy.
         subst. simpl in H1. inversion H1. subst. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H0. simpl in H0.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a (p & [(l, s2, w)]))]))) in H0. unfold coseq_id in H0. simpl in H0.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         inversion H0.
         subst. simpl in H1. inversion H1. subst.
         apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w))). simpl. easy. easy.
         subst. simpl in H1. inversion H1. subst.
         apply IHa in H3. 
         apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w))). simpl. easy. easy. easy. easy.
Qed.

Lemma coseqING: forall a s l,
coseqIn a s ->
coseqInLC s l ->
In a l.
Proof. intros.
       induction H; intros.
       - subst.
         pinversion H0.
         + subst. easy.
         + subst. simpl in H. inversion H. subst. easy.
           apply coseqInLC_mon.
       - pinversion H0.
         + subst. easy.
         + subst. simpl in H. inversion H. subst.
           apply IHcoseqIn. easy.
           apply coseqInLC_mon.
Qed.

Lemma coseqINGA: forall a s l,
coseqInLC s l ->
coseqInLC s (a :: l).
Proof. pcofix CIH. intros.
       pinversion H0.
       subst. pfold. constructor.
       subst. pfold. constructor. simpl. right. easy.
       right. apply CIH. 
       easy.
       apply coseqInLC_mon.
Qed.

Lemma coseqINGAR: forall a s l,
coseqInLC s (a :: l) ->
~ coseqIn a s ->
coseqInLC s l.
Proof. pcofix CIH. intros.
       pinversion H0.
       subst. pfold. constructor.
       subst.
       simpl in H.
       destruct H as [H | H].
       - subst.
         contradict H1.
         apply CoInSplit1 with (y := x) (ys := xs). easy. easy.
       - pfold. constructor. easy.
         right. apply CIH with (a := a). easy.
         unfold not. intro Ha.
         apply H1.
         case_eq(sdir_eqb a x); intros.
         + rewrite sdir_eqb_eq in H3. subst.
           apply CoInSplit1 with (y := x) (ys := xs). easy. easy.
         + rewrite sdir_eqb_neq in H3.
           apply CoInSplit2 with (y := x) (ys := xs). easy. easy.
           easy.
       apply coseqInLC_mon.
Qed.

Lemma coseqNINGA: forall l s a,
coseqInR l s ->
~ coseqIn a s ->
~ In a l.
Proof. intro l.
       induction l; intros.
       - easy.
       - simpl. unfold not.
         intro Ha.
         destruct Ha as [Ha | Ha].
         + subst.
           apply H0.
           inversion H. subst. easy.
         + apply H0.
           inversion H.
           subst.
           specialize(IHl _ _ H5 H0). easy. 
Qed.

Lemma coseqINGC: forall s l,
  coseqInLC s l ->
  (forall a, coseqIn a s -> In a l).
Proof. intros.
       induction H0; intros.
       - subst.
         pinversion H.
         + subst. easy.
         + subst. simpl in H0. inversion H0. subst. easy.
           apply coseqInLC_mon.
       - pinversion H.
         + subst. easy.
         + subst. simpl in H0. inversion H0. subst.
           apply IHcoseqIn. easy.
           apply coseqInLC_mon.
Qed.

Lemma coseqInB: forall b l p w,
  coseqIn (p, snd) (act w) ->
  coseqInLC (act (merge_bpf_cont b w)) l ->
  In (p, snd) l. 
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H0. simpl in H0.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         pinversion H0.
         subst.
         specialize(IHb l p w H H5). easy.
         apply coseqInLC_mon.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H0. simpl in H0.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         pinversion H0.
         subst.
         specialize(IHb l p w H H5). easy.
         apply coseqInLC_mon.
       - rewrite bpfend_bn in H0.
         apply coseqING with (s := act w); easy.
Qed.

Lemma coseqInBP: forall b l p w,
  isInB b p ->
  coseqInLC (act (merge_bpf_cont b w)) l ->
  In (p, snd) l. 
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H0. simpl in H0.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         pinversion H0.
         subst.
         apply IHb with (w := w); easy.
         apply coseqInLC_mon.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H0. simpl in H0.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         pinversion H0.
         subst.
         apply Bool.orb_true_iff in H.
         destruct H as [H | H].
         + rewrite eqb_eq in H.
           subst. easy.
         + apply IHb with (w := w); easy.
         apply coseqInLC_mon.
       - simpl in H. easy.
Qed.

Lemma coseqInA: forall a l p w,
  coseqIn (p, rcv) (act w) ->
  coseqInLC (act (merge_apf_cont a w)) l ->
  In (p, rcv) l. 
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H0.
         apply coseqING with (s := (act w)); easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)) in H0. simpl in H0.
         rewrite(coseq_eq (act (s & [(s0, s1, merge_apf_cont a w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         pinversion H0.
         subst. apply IHa with (w := w); easy.
         apply coseqInLC_mon.
Qed.

Lemma coseqInAP: forall a l p w,
  isInA a p ->
  coseqInLC (act (merge_apf_cont a w)) l ->
  In (p, rcv) l. 
Proof. intro a.
       induction a; intros.
       - simpl in H. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)) in H0. simpl in H0.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         pinversion H0.
         subst. simpl in H.
         apply Bool.orb_true_iff in H.
         destruct H as [H | H].
         + rewrite eqb_eq in H. subst. easy.
         + specialize(IHa l p w H H5). easy.
         apply coseqInLC_mon.
Qed.

Lemma listInG: forall l a s,
  In a l ->
  coseqInR l s ->
  coseqIn a s.
Proof. intros.
       induction H0; intros.
       - simpl in H. easy.
       - simpl in H.
         destruct H as [H | H].
         + subst. easy.
         + apply IHcoseqInR. easy.
Qed.

Lemma csInA: forall a p l s w, 
  coseqIn a (act (p & [(l, s, w)])) ->
  a = (p, rcv) \/ coseqIn a (act w).
Proof. intros.
       rewrite(coseq_eq(act (p & [(l, s, w)]))) in H. unfold coseq_id in H. simpl in H.
       inversion H.
       - subst. simpl in H0. inversion H0. subst. left. easy.
       - subst. simpl in H0. inversion H0. subst. right. easy.
Qed.

Lemma csInB: forall a p l s w, 
  coseqIn a (act (p ! [(l, s, w)])) ->
  a = (p, snd) \/ coseqIn a (act w).
Proof. intros.
       rewrite(coseq_eq(act (p ! [(l, s, w)]))) in H. unfold coseq_id in H. simpl in H.
       inversion H.
       - subst. simpl in H0. inversion H0. subst. left. easy.
       - subst. simpl in H0. inversion H0. subst. right. easy.
Qed.

Lemma csInRAG: forall a p w,
  coseqIn (p,rcv) (act (merge_apf_cont a w)) ->
  isInA a p = true \/ coseqIn (p,rcv) (act w).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H. right. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))) in H. unfold coseq_id in H. simpl in H.
         inversion H.
         + subst. simpl in H0. simpl. inversion H0. subst.
           rewrite eqb_refl. simpl. left. easy.
         + subst. simpl in H0. inversion H0. subst.
           simpl.
           assert(p <> s).
           { unfold not. intro Ha. apply H1. subst. easy. }
           apply eqb_neq in H3. rewrite H3. simpl.
           apply IHa. easy.
Qed.

Lemma csInRARevG: forall a p w,
  isInA a p = true \/ coseqIn (p,rcv) (act w) ->
  coseqIn (p,rcv) (act (merge_apf_cont a w)).
Proof. intro a.
       induction a; intros.
       - destruct H as [H | H].
         + simpl in H. easy.
         + rewrite apfend_an. easy.
       - simpl in H.
         destruct H as [H | H].
         + rewrite Bool.orb_true_iff in H.
           destruct H as [H | H].
           ++ rewrite eqb_eq in H. subst.
              rewrite(st_eq (merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
              rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
              apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w)) ). simpl. easy. easy.
           ++ rewrite(st_eq (merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
              rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
              case_eq (eqb p s); intros.
              * rewrite eqb_eq in H0. subst.
                apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w)) ). simpl. easy. easy.
              * apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w)) ). simpl. easy.
                apply eqb_neq in H0.
                unfold not. intro Ha.
                apply H0. inversion Ha. easy.
                apply IHa. left. easy.
         + rewrite(st_eq (merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
           rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
            case_eq (eqb p s); intros.
            ++ rewrite eqb_eq in H0. subst.
               apply CoInSplit1 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w)) ). simpl. easy. easy.
            ++ apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_apf_cont a w)) ). simpl. easy.
               apply eqb_neq in H0.
               unfold not. intro Ha.
               apply H0. inversion Ha. easy.
               apply IHa. right. easy.
Qed.

Lemma csInSBG: forall b p w,
  coseqIn (p,snd) (act (merge_bpf_cont b w)) ->
  isInB b p = true \/ coseqIn (p,snd) (act w).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         simpl.
         inversion H.
         + subst. simpl in H0. easy.
         + subst. simpl in H0. subst.
           inversion H0. subst.
           apply IHb. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         simpl.
         inversion H.
         + subst. simpl in H0. 
           inversion H0. subst. rewrite eqb_refl. simpl. left. easy.
         + subst. simpl in H0. subst.
           inversion H0. subst.
           assert(p <> s).
           { intro not.
             apply H1. subst. easy. 
           }
           apply eqb_neq in H3. rewrite H3. simpl.
           apply IHb. easy.
       - rewrite bpfend_bn in H. right. easy.
Qed.

Lemma csInSBRevG: forall b p w,
  isInB b p = true \/ coseqIn (p,snd) (act w) ->
  coseqIn (p,snd) (act (merge_bpf_cont b w)).
Proof. intro b.
       induction b; intros.
       - simpl in H.
         destruct H as [H | H].
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
           rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy. easy.
           apply IHb. left. easy.
         + rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
           rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
           apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy. easy.
           apply IHb. right. easy.
       - simpl in H.
         destruct H as [H | H].
         + rewrite Bool.orb_true_iff in H.
           destruct H as [H | H].
           ++ rewrite eqb_eq in H. subst.
              rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
              rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
              apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy. easy.
              rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
              rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
              case_eq (eqb p s); intros.
              * rewrite eqb_eq in H0. subst.
                apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy. easy.
              * apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy.
                apply eqb_neq in H0.
                unfold not. intro Ha.
                apply H0. inversion Ha. easy.
                apply IHb. left. easy.
           ++ rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
              rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
              case_eq (eqb p s); intros.
              * rewrite eqb_eq in H0. subst.
                apply CoInSplit1 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy. easy.
              * apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b w)) ). simpl. easy.
                apply eqb_neq in H0.
                unfold not. intro Ha.
                apply H0. inversion Ha. easy.
                apply IHb. right. easy.
       - rewrite bpfend_bn.
         destruct H as [H | H].
         + simpl in H. easy.
         + easy.
Qed.

Lemma coseqInRAddS: forall b q p l s w,
  coseqIn (q, rcv) (act (merge_bpf_cont b w)) ->
  coseqIn (q, rcv) (act (merge_bpf_cont b (p ! [(l, s, w)]))).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         inversion H.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit1 with (y := (q, rcv)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit2 with (y := (s, rcv)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         apply IHb. easy.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H. simpl in H.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H. unfold coseq_id in H. simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         inversion H.
         subst. simpl in H0. easy.
         subst. simpl in H0. inversion H0. subst.
         apply CoInSplit2 with (y := (s, snd)) (ys := (act (merge_bpf_cont b (p ! [(l, s2, w)]))) ). simpl. easy. easy.
         apply IHb. easy.
       - rewrite bpfend_bn. rewrite bpfend_bn in H.
         rewrite(coseq_eq(act (p ! [(l, s, w)]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := (p, snd)) (ys := (act w) ). simpl. easy. easy.
         easy.
Qed.

(*from here on*)

Lemma actdSE: forall b l1 p l s w,
  isInB b p = false ->
  coseqIn (p, snd) (act w) ->
  coseqInLC (act (merge_bpf_cont b (p ! [(l, s, w)]))) l1 ->
  coseqInLC (act (merge_bpf_cont b w)) l1. 
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         apply IHb in H6.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         pfold.
         constructor. easy.
         left. easy. easy. easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H1. simpl in H1.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))) in H1. unfold coseq_id in H1. simpl in H1.
         simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         pinversion H1.
         subst.
         apply IHb in H5.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         pfold.
         constructor. easy. left. easy.
         easy. easy.
         apply coseqInLC_mon.
       - rewrite bpfend_bn.
         rewrite bpfend_bn in H1.
         rewrite(coseq_eq(act (p ! [(l, s, w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1. subst.
         easy.
         apply coseqInLC_mon.
Qed.

(*yeni*)
Lemma actdSER: forall b l1 p l s w,
  isInB b p = false ->
  coseqIn (p, snd) (act w) ->
  coseqInLC (act (merge_bpf_cont b w)) l1 ->
  coseqInLC (act (merge_bpf_cont b (p ! [(l, s, w)]))) l1.
Proof. intro b.
       induction b; intros.
       - simpl in H.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq (act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor. easy.
         left.
         apply IHb. easy. easy. easy.
         apply coseqInLC_mon.
       - simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq (act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H1. simpl in H1.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor. easy.
         left.
         apply IHb. easy. easy. easy.
         apply coseqInLC_mon.
       - rewrite bpfend_bn. rewrite bpfend_bn in H1.
         rewrite(coseq_eq(act (p ! [(l, s, w)]))). unfold coseq_id. simpl.
         pfold. constructor.
         apply coseqING with (s := act w); easy.
         left. easy.
Qed.

Lemma IactdSE: forall l1 b p l s w,
  isInB b p = false ->
  coseqIn (p, snd) (act w) ->
  coseqInR l1 (act (merge_bpf_cont b (p ! [(l, s, w)]))) ->
  coseqInR l1 (act (merge_bpf_cont b w)).
Proof. intro l1.
       induction l1; intros.
       - simpl. constructor.
       - case_eq(sdir_eqb a (p, snd)); intros.
         + apply sdir_eqb_eq in H2.
           subst.
           inversion H1.
           ++ subst.
              constructor.
              apply coseq_inS; easy.
           ++ apply IHl1 with (p := p) (l := l) (s := s); easy.
         + apply sdir_eqb_neq in H2.
           inversion H1. subst.
           constructor.
           apply coseq_ninS with (p := p) (l := l) (s := s); easy.
           apply IHl1 with (p := p) (l := l) (s := s); easy.
Qed.

Lemma IactdSER: forall l1 b p l s w,
  isInB b p = false ->
  coseqIn (p, snd) (act w) ->
  coseqInR l1 (act (merge_bpf_cont b w)) ->
  coseqInR l1 (act (merge_bpf_cont b (p ! [(l, s, w)]))).
Proof. intro l1.
       induction l1; intros.
       - constructor.
       - inversion H1. subst.
         constructor.
         apply IHl1 with (p := p) (l := l) (s := s) in H6; try easy.
         apply coseq_ninSR. easy.
         apply IHl1; easy.
Qed.

Lemma actdSNE: forall b l1 p l s w,
  isInB b p = false ->
  (coseqIn (p, snd) (act w) -> False) ->
  coseqInLC (act (merge_bpf_cont b (p ! [(l, s, w)]))) l1 ->
  coseqInLC (act (merge_bpf_cont b w)) (dropE l1 (p, snd)). 
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         apply IHb in H6.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         pfold.
         constructor.
         simpl in H.
         apply dropEList; easy.
         left. easy. easy. easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))) in H1. simpl in H1.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))) in H1. unfold coseq_id in H1. simpl in H1.
         simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         pinversion H1.
         subst.
         apply IHb in H5.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)). simpl.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))). unfold coseq_id. simpl.
         pfold.
         constructor.
         apply dropEList. easy.
         rewrite eqb_neq in Ha.
         unfold not. intro Hc.
         apply Ha. inversion Hc; subst; easy.
         left. easy.
         easy. easy.
         apply coseqInLC_mon.
       - rewrite bpfend_bn.
         rewrite bpfend_bn in H1.
         rewrite(coseq_eq(act (p ! [(l, s, w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1. subst.
         apply coseq2InLCS; easy.
         apply coseqInLC_mon.
Qed.

Lemma actdSNER: forall b l1 p l s w,
  isInB b p = false ->
  (coseqIn (p, snd) (act w) -> False) ->
  coseqInLC (act (merge_bpf_cont b w)) l1 ->
  coseqInLC (act (merge_bpf_cont b (p ! [(l, s, w)]))) ((p,snd)::l1).
Proof. intro b.
       induction b; intros.
       - rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_receive s s0 s1 b) w)) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_bpf_cont b w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor. simpl. right. easy.
         left.
         apply IHb. simpl in H. easy. easy. easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) (p ! [(l, s2, w)]))). simpl.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b (p ! [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_bpf_cont (bpf_send s s0 s1 b) w)) in H1. simpl in H1.
         rewrite(coseq_eq(act (s ! [(s0, s1, merge_bpf_cont b w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor. simpl. right. easy.
         left.
         apply IHb. simpl in H. rewrite orbtf in H. easy. easy. easy.
         apply coseqInLC_mon.
       - rewrite bpfend_bn. rewrite bpfend_bn in H1.
         rewrite(coseq_eq(act (p ! [(l, s, w)])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left. apply coseqINGA; easy.
Qed.

(*yeni*)
Lemma IactdSNER: forall l1 b p l s w,
  isInB b p = false ->
  (coseqIn (p, snd) (act w) -> False) ->
  coseqInR l1 (act (merge_bpf_cont b w)) ->
  coseqInR ((p,snd)::l1) (act (merge_bpf_cont b (p ! [(l, s, w)]))).
Proof. intro l1.
       induction l1; intros.
       - simpl. constructor.
         apply csInSBRevG. right. 
         rewrite(coseq_eq(act (p ! [(l, s, w)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w) ). simpl. easy. easy.
         constructor.
       - constructor.
         apply csInSBRevG. right. 
         rewrite(coseq_eq(act (p ! [(l, s, w)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, snd)) (ys := (act w) ). simpl. easy. easy.
         inversion H1.
         subst.
         constructor.
         case_eq a; intros.
         + rename s0 into q.
           destruct d.
           ++ subst.
              apply coseq_ninSR. easy.
           ++ subst.
              apply csInSBG in H4.
              destruct H4 as [H4 | H4].
              * apply csInSBRevG. left. easy.
              * apply csInSBRevG. right.
                rewrite(coseq_eq(act (p ! [(l, s, w)]))). unfold coseq_id. simpl.
                case_eq(eqb p q); intros.
                ** rewrite eqb_eq in H2. subst.
                   apply CoInSplit1 with (y := (q, snd)) (ys := (act w) ). simpl. easy. easy.
                ** rewrite eqb_neq in H2.
                   apply CoInSplit2 with (y := (p, snd)) (ys := (act w) ). simpl. easy.
                   unfold not. intro Ha. apply H2. inversion Ha. easy.
                   easy.
         apply IHl1 with (p := p) (l := l) (s := s) in H6.
         inversion H6. subst. easy.
         easy. easy.
Qed.

Lemma IactdSNE: forall l1 b p l s w,
  isInB b p = false ->
  (coseqIn (p, snd) (act w) -> False) ->
  coseqInR l1 (act (merge_bpf_cont b (p ! [(l, s, w)]))) ->
  coseqInR (dropE l1 (p, snd)) (act (merge_bpf_cont b w)).
Proof. intro l1.
       induction l1; intros.
       - simpl. constructor.
       - case_eq(sdir_eqb a (p, snd)); intros.
         + apply sdir_eqb_eq in H2.
           subst. rewrite dl.
           apply IHl1 with (l := l) (s := s).
           easy. easy.
           inversion H1.
           subst. easy.
           apply sdir_eqb_neq in H2.
           rewrite dlN; try easy.
           constructor.
           inversion H1. subst.
           apply coseq_ninS with (p := p) (l := l) (s := s). easy. easy.
           apply IHl1 with (l := l) (s := s).
           easy. easy.
           inversion H1.
           subst. easy.
Qed.

(*ap*)

Lemma actdRE: forall a l1 p l s w,
  isInA a p = false ->
  coseqIn (p, rcv) (act w) ->
  coseqInLC (act (merge_apf_cont a (p & [(l, s, w)]))) l1 ->
  coseqInLC (act (merge_apf_cont a w)) l1.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. rewrite apfend_an in H1.
         pinversion H1.
         subst.  
         rewrite(coseq_eq(act (p & [(l, s, w)]))) in H3. unfold coseq_id in H3. simpl in H3.
         easy.
         subst.
         rewrite(coseq_eq(act (p & [(l, s, w)]))) in H2. unfold coseq_id in H2. simpl in H2.
         simpl in H2. inversion H2. subst.
         easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a (p & [(l, s2, w)]))]))) in H1. unfold coseq_id in H1. simpl in H1.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         pinversion H1.
         subst.
         apply IHa in H6.
         pfold. constructor. easy. left. easy.
         simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         easy. easy.
         apply coseqInLC_mon.
Qed.

(*yeni*)
Lemma actdRER: forall a l1 p l s w,
  isInA a p = false ->
  coseqIn (p, rcv) (act w) ->
  coseqInLC (act (merge_apf_cont a w)) l1 ->
  coseqInLC (act (merge_apf_cont a (p & [(l, s, w)]))) l1.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. rewrite apfend_an in H1.  
         rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
         pfold. constructor.
         apply coseqING with (s := act w); easy.
         left. easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a (p & [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq (merge_apf_cont (apf_receive s s0 s1 a) w)) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor. easy.
         left.
         apply IHa.
         simpl in H. rewrite orbtf in H. easy.
         easy. easy.
         apply coseqInLC_mon.
Qed.

Lemma IactdRE: forall l1 a p l s w,
  isInA a p = false ->
  coseqIn (p, rcv) (act w) ->
  coseqInR l1 (act (merge_apf_cont a (p & [(l, s, w)]))) ->
  coseqInR l1 (act (merge_apf_cont a w)).
Proof. intro l1.
       induction l1; intros.
       - simpl. constructor.
       - case_eq(sdir_eqb a (p, rcv)); intros.
         + apply sdir_eqb_eq in H2.
           subst.
           inversion H1.
           ++ subst.
              constructor.
              apply coseq_inR; easy.
           ++ apply IHl1 with (p := p) (l := l) (s := s); easy.
         + apply sdir_eqb_neq in H2.
           inversion H1. subst.
           constructor.
           apply coseq_ninR with (p := p) (l := l) (s := s); easy.
           apply IHl1 with (p := p) (l := l) (s := s); easy.
Qed.

Lemma IactdRER: forall l1 a p l s w,
  isInA a p = false ->
  coseqIn (p, rcv) (act w) ->
  coseqInR l1 (act (merge_apf_cont a w)) ->
  coseqInR l1 (act (merge_apf_cont a (p & [(l, s, w)]))).
Proof. intro l1. 
       induction l1; intros.
       - constructor.
       - inversion H1. subst.
         constructor.
         apply IHl1 with (p := p) (l := l) (s := s) in H6; try easy.
         apply coseq_ninRR. easy.
         apply IHl1; easy.
Qed.

Lemma actdRNE: forall a l1 p l s w,
  isInA a p = false ->
  (coseqIn (p, rcv) (act w) -> False) ->
  coseqInLC (act (merge_apf_cont a (p & [(l, s, w)]))) l1 ->
  coseqInLC (act (merge_apf_cont a w)) (dropE l1 (p, rcv)).
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an in H1. rewrite apfend_an.
         rewrite(coseq_eq(act (p & [(l, s, w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         apply coseq2InLCR; easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a (p & [(l, s2, w)]))]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor.
         simpl in H.
         rewrite orbtf in H.
         destruct H as (Ha, Hb).
         rewrite eqb_neq in Ha.
         apply dropEList. easy.
         unfold not. intro Hc. apply Ha. inversion Hc. easy.
         apply IHa in H6.
         left. easy.
         simpl in H.
         rewrite orbtf in H. easy. easy.
         apply coseqInLC_mon.
Qed.

Lemma actdRNER: forall a l1 p l s w,
  isInA a p = false ->
  (coseqIn (p, rcv) (act w) -> False) ->
  coseqInLC (act (merge_apf_cont a w)) l1 ->
  coseqInLC (act (merge_apf_cont a (p & [(l, s, w)]))) ((p,rcv)::l1).
Proof. intro b.
       induction b; intros.
       - rewrite apfend_an. rewrite apfend_an in H1.
         rewrite(coseq_eq(act (p & [(l, s, w)])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left. apply coseqINGA; easy.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 b) (p & [(l, s2, w)]))). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont b (p & [(l, s2, w)]))]))). unfold coseq_id. simpl.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 b) w)) in H1. simpl in H1.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont b w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         pinversion H1.
         subst.
         pfold. constructor. simpl. right. easy.
         left.
         apply IHb. simpl in H. rewrite orbtf in H. easy. easy. easy.
         apply coseqInLC_mon.
Qed.

Lemma IactdRNE: forall l1 a p l s w,
  isInA a p = false ->
  (coseqIn (p, rcv) (act w) -> False) ->
  coseqInR l1 (act (merge_apf_cont a (p & [(l, s, w)]))) ->
  coseqInR (dropE l1 (p, rcv)) (act (merge_apf_cont a w)).
Proof. intro l1.
       induction l1; intros.
       - simpl. constructor.
       - case_eq(sdir_eqb a (p, rcv)); intros.
         + apply sdir_eqb_eq in H2.
           subst. rewrite dl.
           apply IHl1 with (l := l) (s := s).
           easy. easy.
           inversion H1.
           subst. easy.
           apply sdir_eqb_neq in H2.
           rewrite dlN; try easy.
           constructor.
           inversion H1. subst.
           apply coseq_ninR with (p := p) (l := l) (s := s). easy. easy.
           apply IHl1 with (l := l) (s := s).
           easy. easy.
           inversion H1.
           subst. easy.
Qed.

(*yeni*)
Lemma IactdRNER: forall l1 a p l s w,
  isInA a p = false ->
  (coseqIn (p, rcv) (act w) -> False) ->
  coseqInR l1 (act (merge_apf_cont a w)) ->
  coseqInR ((p,rcv)::l1) (act (merge_apf_cont a (p & [(l, s, w)]))).
Proof. intro l1.
       induction l1; intros.
       - simpl. constructor.
         apply csInRARevG. right. 
         rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w) ). simpl. easy. easy.
         constructor.
       - constructor.
         apply csInRARevG. right. 
         rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p, rcv)) (ys := (act w) ). simpl. easy. easy.
         inversion H1.
         subst.
         constructor.
         case_eq a; intros.
         + rename s0 into q.
           destruct d.
           ++ subst.
              apply csInRAG in H4.
              destruct H4 as [H4 | H4].
              * apply csInRARevG. left. easy.
              * apply csInRARevG. right.
                rewrite(coseq_eq(act (p & [(l, s, w)]))). unfold coseq_id. simpl.
                case_eq(eqb p q); intros.
                ** rewrite eqb_eq in H2. subst.
                   apply CoInSplit1 with (y := (q, rcv)) (ys := (act w) ). simpl. easy. easy.
                ** rewrite eqb_neq in H2.
                   apply CoInSplit2 with (y := (p, rcv)) (ys := (act w) ). simpl. easy.
                   unfold not. intro Ha. apply H2. inversion Ha. easy.
                   easy.
           ++ subst.
              assert((merge_apf_cont a0 w) = (merge_bpf_cont (Ap2BpSeq a0) w)).
              { rewrite mcAp2Bp2. easy. }
              rewrite H2 in H4.
              apply csInSBG in H4.
              destruct H4 as [H4 | H4].
              * rewrite BisInAF in H4. easy.
              * assert((merge_apf_cont a0 (p & [(l, s, w)])) =
                       (merge_bpf_cont (Ap2BpSeq (Apf_merge a0 (apf_receive p l s apf_end))) w)).
                { rewrite mcAp2Bp2.
                  rewrite bareOrg2. easy.
                }
                rewrite H3.
                apply csInSBRevG. right. easy.
         apply IHl1 with (p := p) (l := l) (s := s) in H6.
         inversion H6. subst. easy.
         easy. easy.
Qed.

Lemma actionExL: forall a w w',
  coseqIn a (act w) ->
  paco2 refinementR3 bot2 w w' ->
  coseqIn a (act w').
Proof. intros.
       pinversion H0.
       - destruct H4 as (l1,(l2,(Ha,(Hb,(Hc,(Hd,He)))))).
         rewrite <- meqAp3 in H3, H6, Hb, Hd.
         rewrite <- H5 in H.
         apply csInA in H.
         destruct H as [H | H].
         + subst.
           rewrite <- meqAp3.
           apply csInRARevG.
           right.
           rewrite(coseq_eq(act (p & [(l, s', w'0)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, rcv)) (ys := (act w'0) ). simpl. easy. easy.
         + specialize(coseqING _ _ _ H Ha); intro HI.
           rewrite <- meqAp3.
           apply He in HI.
           specialize(listInG _ _ _ HI Hd); intro HG.
           destruct a as (q, d).
           case_eq d; intros.
           ++ subst. apply csInRAG in HG.
              apply csInRARevG.
              destruct HG as [HG | HG].
              * left. easy.
              * right. specialize(csInRARevG (apf_receive p l s' apf_end) q w'0); intro HQ.
                rewrite(st_eq(merge_apf_cont (apf_receive p l s' apf_end) w'0)) in HQ. simpl in HQ.
                rewrite apfend_an in HQ.
                apply HQ.  right. easy.
           ++ subst.
              assert((merge_apf_cont (ApnA3 a0 n) w'0) = 
                     (merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) w'0)).
              { rewrite mcAp2Bp2. easy. }
              rewrite H4 in HG.
              apply csInSBG in HG.
              destruct HG as [HG | HG].
              * rewrite BisInAF in HG. easy.
              * assert((merge_apf_cont (ApnA3 a0 n) (p & [(l, s', w'0)])) =
                       (merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive p l s' apf_end))) w'0)).
                { rewrite !Ap2BpSeq2.
                  rewrite bareOrg1. simpl.
                  rewrite (st_eq(merge_bpf_cont (bpf_receive p l s' bpf_end) w'0)). simpl.
                  rewrite bpfend_bn. easy.
                }
                rewrite H5.
                apply csInSBRevG.
                right. easy.
       - destruct H4 as (l1,(l2,(Ha,(Hb,(Hc,(Hd,He)))))).
         rewrite <- meqBp3 in H3, H6, Hb, Hd.
         rewrite <- H5 in H.
         apply csInB in H.
         destruct H as [H | H].
         + subst.
           rewrite <- meqBp3.
           apply csInSBRevG.
           right.
           rewrite(coseq_eq(act (p ! [(l, s', w'0)]))). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := (p, snd)) (ys := (act w'0) ). simpl. easy. easy.
         + specialize(coseqING _ _ _ H Ha); intro HI.
           rewrite <- meqBp3.
           apply He in HI.
           specialize(listInG _ _ _ HI Hd); intro HG.
           destruct a as (q, d).
           case_eq d; intros.
           ++ subst. apply coseqInRAddS. easy.
           ++ subst.
              apply csInSBG in HG.
              destruct HG as [HG | HG].
              * apply csInSBRevG. 
                left. easy.
              * apply csInSBRevG.
                right.
                rewrite(coseq_eq(act (p ! [(l, s', w'0)]))). unfold coseq_id. simpl.
                case_eq (eqb p q); intros.
                ** rewrite eqb_eq in H4. subst.
                   apply CoInSplit1 with (y := (q, snd)) (ys := (act w'0) ). simpl. easy. easy.
                ** rewrite eqb_neq in H4. subst.
                   apply CoInSplit2 with (y := (p, snd)) (ys := (act w'0) ). simpl. easy.
                   unfold not. intro Hn.
                   apply H4. inversion Hn. subst. easy.
                   easy.
       - subst. easy.
       apply refinementR3_mon.
Qed.

Lemma actionExR: forall a w w',
  coseqIn a (act w') ->
  paco2 refinementR3 bot2 w w' ->
  coseqIn a (act w).
Proof. intros.
       pinversion H0.
       - destruct H4 as (l1,(l2,(Ha,(Hb,(Hc,(Hd,He)))))).
         rewrite <- meqAp3 in H3, H6, Hb, Hd.
         rewrite <- H6 in H.
         assert((merge_apf_cont (ApnA3 a0 n) (p & [(l, s', w'0)])) =
                (merge_apf_cont (Apf_merge (ApnA3 a0 n) (apf_receive p l s' apf_end)) w'0)).
         { rewrite reOrd1.
           rewrite(st_eq(merge_apf_cont (apf_receive p l s' apf_end) w'0)). simpl.
           rewrite apfend_an. easy.
         }
         rewrite H4 in H.
         case_eq a; intros.
         + subst. rename s0 into q.
           destruct d.
           ++ case_eq (eqb p q); intros.
              * rewrite eqb_eq in H5. subst.
                apply CoInSplit1 with (y := (q, rcv)) (ys := (act w0) ). simpl. easy. easy.
              * rewrite eqb_neq in H5. 
                apply csInRAG in H. 
                destruct H as [H | H].
                ** rewrite InMerge in H. simpl in H.
                   assert(q <> p) by easy.
                   apply eqb_neq in H6.
                   rewrite H6 in H.
                   simpl in H.
                   rewrite Bool.orb_false_r in H. 
                   specialize(coseqInAP (ApnA3 a0 n) l2 q w'0 H Hb); intro HQ.
                   apply He in HQ.
                   specialize(listInG _ _ _ HQ Hc); intro HP.
                   apply CoInSplit2 with (y := (p, rcv)) (ys := (act w0) ). simpl. easy.
                   unfold not. intro Hn. apply H5.
                   inversion Hn. subst. easy.
                   easy.
                ** assert(coseqIn (q, rcv) (act (merge_apf_cont (ApnA3 a0 n) w'0))).
                   { apply csInRARevG. right. easy. }
                   specialize(coseqING _ _ _ H6 Hb); intro HP.
                   apply He in HP.
                   specialize(listInG _ _ _ HP Hc); intro HR.
                   apply CoInSplit2 with (y := (p, rcv)) (ys := (act w0) ). simpl. easy.
                   unfold not. intro Hn. apply H5.
                   inversion Hn. subst. easy.
                   easy.
           ++ assert((merge_apf_cont (Apf_merge (ApnA3 a0 n) (apf_receive p l s' apf_end)) w'0) =
                     (merge_bpf_cont (Ap2BpSeq (Apf_merge (ApnA3 a0 n) (apf_receive p l s' apf_end))) w'0)).
              { rewrite mcAp2Bp2. easy. }
              rewrite H5 in H.
              apply csInSBG in H.
              destruct H as [H | H].
              * rewrite BisInAF in H. easy.
              * assert((merge_apf_cont (ApnA3 a0 n) w'0) = (merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) w'0)).
                { rewrite mcAp2Bp2. easy. }
                rewrite H6 in Hb.
                assert(coseqIn (q, snd) (act (merge_bpf_cont (Ap2BpSeq (ApnA3 a0 n)) w'0))).
                { apply csInSBRevG. right. easy. }
                specialize(coseqING _ _ _ H7 Hb); intro HP.
                apply He in HP.
                specialize(listInG _ _ _ HP Hc); intro HR.
                apply CoInSplit2 with (y := (p, rcv)) (ys := (act w0) ). simpl. easy. easy.
                easy.
       - destruct H4 as (l1,(l2,(Ha,(Hb,(Hc,(Hd,He)))))).
         rewrite <- meqBp3 in H3, H6, Hb, Hd.
         rewrite <- H6 in H.
         case_eq a; intros.
         + subst. rename s0 into q.
           destruct d.
           ++ apply coseq_ninS in H; try easy.
              specialize(coseqING _ _ _ H Hb); intro HP.
              apply He in HP.
              specialize(listInG _ _ _ HP Hc); intro HR.
              rewrite(coseq_eq(act (p ! [(l, s, w0)]))). unfold coseq_id. simpl.
              apply CoInSplit2 with (y := (p, snd)) (ys := (act w0) ). simpl. easy. easy.
              easy.
           ++ case_eq(eqb p q); intros.
              * rewrite eqb_eq in H4. subst.
                rewrite(coseq_eq(act (q ! [(l, s, w0)]))). unfold coseq_id. simpl.
                apply CoInSplit1 with (y := (q, snd)) (ys := (act w0) ). simpl. easy. easy.
              * apply coseq_ninS in H.
                specialize(coseqING _ _ _ H Hb); intro HP.
                apply He in HP.
                specialize(listInG _ _ _ HP Hc); intro HR.
                rewrite(coseq_eq(act (p ! [(l, s, w0)]))). unfold coseq_id. simpl.
                apply CoInSplit2 with (y := (p, snd)) (ys := (act w0) ). simpl. easy.
                rewrite eqb_neq in H4.
                unfold not. intro Hn. apply H4. inversion Hn. easy.
                easy.
                rewrite eqb_neq in H4.
                unfold not. intro Hn. apply H4. inversion Hn. easy.
       - rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
         subst.
         rewrite(coseq_eq(act (end))) in H. unfold coseq_id in H. simpl in H.
         easy.
       apply refinementR3_mon.
Qed.

Lemma actionExLN: forall a w w',
  (coseqIn a (act w) -> False) ->
  paco2 refinementR3 bot2 w w' ->
  coseqIn a (act w') -> False.
Proof. intros.
       apply H.
       apply actionExR with (w' := w'); easy.
Qed.

Lemma actionExRN: forall a w w',
  (coseqIn a (act w') -> False) ->
  paco2 refinementR3 bot2 w w' ->
  coseqIn a (act w) -> False.
Proof. intros.
       apply H.
       apply actionExL with (w := w); easy.
Qed.

Lemma dropAInLCL1: forall a l1 p l s w, 
coseqInLC (act (merge_apf_cont a (p & [(l, s, w)]))) l1 ->
coseqInLC (act (merge_apf_cont a w)) l1.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. rewrite apfend_an in H.
         rewrite(coseq_eq(act (p & [(l, s, w)])) ) in H. unfold coseq_id in H. simpl in H.
         pinversion H. subst. easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) (p & [(l, s2, w)]))) in H. simpl in H.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a (p & [(l, s2, w)]))]))) in H. unfold coseq_id in H. simpl in H.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         pinversion H.
         subst.
         pfold.
         constructor. easy.
         left.
         apply IHa with (p := p) (l := l) (s := s2). easy.
         apply coseqInLC_mon.
Qed.

(* Lemma dropAInLCR: forall a l1 p l s w, 
In (p, rcv) l1 ->
coseqInLC (act (merge_apf_cont a w)) l1 ->
coseqInLC (act (merge_apf_cont a (p & [(l, s, w)]))) l1.
Admitted.
 *)
 
Lemma dropAInLCL2: forall a l1 p l s w, 
coseqInLC (act (p & [(l, s, (merge_apf_cont a w))])) l1 ->
coseqInLC (act (merge_apf_cont a w)) l1.
Proof. intro a.
       induction a; intros.
       - rewrite apfend_an. rewrite apfend_an in H.
         rewrite(coseq_eq(act (p & [(l, s, w)])) ) in H. unfold coseq_id in H. simpl in H.
         pinversion H. subst. easy.
         apply coseqInLC_mon.
       - rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)) in H. simpl in H.
         rewrite(coseq_eq (act (p & [(l, s2, s & [(s0, s1, merge_apf_cont a w)])]))) in H. unfold coseq_id in H. simpl in H.
         rewrite(st_eq(merge_apf_cont (apf_receive s s0 s1 a) w)). simpl.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         pinversion H.
         subst.
         pinversion H4.
         subst.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))) in H1. unfold coseq_id in H1. simpl in H1.
         easy.
         subst.
         rewrite(coseq_eq(act (s & [(s0, s1, merge_apf_cont a w)]))) in H0. unfold coseq_id in H0. simpl in H0.
         inversion H0. subst.
         pfold.
         constructor. easy.
         left.
         apply IHa with (p := p) (l := l) (s := s2).
         rewrite (coseq_eq(act (p & [(l, s2, merge_apf_cont a w)]))). unfold coseq_id. simpl.
         pfold. constructor. easy. left. easy.
         apply coseqInLC_mon.
         apply coseqInLC_mon.
Qed.

Lemma dropNin: forall l a, In a (dropE l a) -> False.
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - case_eq(sdir_eqb a a0); intros.
         + apply sdir_eqb_eq in H0. subst.
           rewrite dl in H. apply IHl in H. easy.
         + apply sdir_eqb_neq in H0. subst.
           rewrite dlN in H.
           simpl in H.
           destruct H as [H | H].
           ++ subst. easy.
           ++ apply IHl in H. easy. easy. 
Qed.

Lemma in_after_drop: forall l a x, In x (dropE l a) -> In x l.
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - simpl. case_eq(sdir_eqb a a0); intros.
         + apply sdir_eqb_eq in H0. subst.
           rewrite dl in H.
           apply IHl in H. right. easy.
         + apply sdir_eqb_neq in H0. subst.
           rewrite dlN in H.
           simpl in H.
           destruct H as [H | H].
           ++ left. easy.
           ++ apply IHl in H. right. easy.
           easy.
Qed.

Lemma in_before_drop: forall l a x, x <> a -> In x l -> In x (dropE l a).
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - case_eq(sdir_eqb a a0); intros.
         + apply sdir_eqb_eq in H1. subst.
           rewrite dl.
           apply IHl.
           easy.
           simpl in H0.
           destruct H0. subst. easy. easy.
         + apply sdir_eqb_neq in H1.
           rewrite dlN.
           simpl. simpl in H0.
           destruct H0 as [H0 | H0].
           ++ left. easy.
           ++ right. apply IHl; easy. easy.
Qed.

Lemma nin_before_drop: forall l x a, (In x l -> False) -> In x (dropE l a) -> False.
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - simpl. case_eq(sdir_eqb a a0); intros.
         + apply sdir_eqb_eq in H1. subst.
           rewrite dl in H0.
           apply IHl in H0. easy.
           intro Ha. apply H. simpl. right. easy.
         + apply sdir_eqb_neq in H1. subst.
           rewrite dlN in H0.
           simpl in H0.
           destruct H0 as [H0 | H0].
           ++ subst. apply H. simpl. left. easy.
           ++ apply IHl in H0. easy. intro Ha. apply H. simpl. right. easy.
           easy.
Qed.

Lemma ortf: forall P Q, (P \/ Q -> False) -> (P -> False) /\ (Q -> False).
Proof. intros.
       apply not_or_and in H.
       easy.
Qed.

Lemma nilIff: forall l, (forall x : string * dir, In x [] <-> In x l) -> l = [].
Proof. intro l.
       induction l; intros.
       - easy.
       - simpl in H.
         specialize(H a).
         destruct H as (Ha, Hb).
         apply ortf in Hb. easy.
Qed.

Lemma invdropH1: forall xs ys a x,
   x <> a ->
   (In a xs -> In a ys) ->
   (In a ys -> In a xs) ->
   In a (dropE xs x) ->
   In a (dropE ys x).
Proof. intros.
       specialize(classic(In a ys)); intro Hin.
       destruct Hin as [Hin | Hin].
       - apply H1 in Hin.
         specialize(H0 Hin).
         apply in_before_drop; easy.
       - assert(~ In a xs).
         { unfold not. intro Ha.
           apply Hin. apply H0. easy. }
         apply nin_before_drop with (a := x) in H3. easy.
         easy.
Qed.

Lemma dropSame: forall xs a, In a (dropE xs a) -> False.
Proof. intro xs.
       induction xs; intros.
       - simpl in H. easy.
       - case_eq(sdir_eqb a a0); intros.
         + apply sdir_eqb_eq in H0. subst.
           rewrite dl in H.
           apply IHxs with (a := a0). easy.
         + apply sdir_eqb_neq in H0.
           rewrite dlN in H; try easy.
           simpl in H.
           destruct H as [H | H].
           ++ subst. easy.
           ++ apply IHxs with (a := a0). easy.
Qed.

Lemma invdropEN: forall xs ys x y,
  x <> y ->
  (forall a, In a (x::xs) <-> In a (y::ys)) ->
  (forall a, In a (dropE (x::xs) x) <-> In a (dropE (y::ys) x)).
Proof. intros.
       rewrite dl. rewrite dlN; try easy.
       specialize(H0 a).
       simpl in H0.
       destruct H0 as (Ha, Hb).
       simpl.
       split.
       - intro Hc.
         specialize(classic (y = a)); intro Heq.
         destruct Heq as [Heq | Heq].
         + left. easy.
         + right.
           specialize(classic (x = a)); intro Heq2.
           destruct Heq2 as [Heq2 | Heq2].
           ++ subst. apply dropSame in Hc. easy.
           ++ assert(In a xs -> In a ys).
              { intro Hd.
                assert(x = a \/ In a xs).
                { right. easy. }
                apply Ha in H0.
                destruct H0. subst. easy. easy.
              }
              assert(In a ys -> In a xs).
              { intro Hd.
                assert(y = a \/ In a ys).
                { right. easy. }
                apply Hb in H1.
                destruct H1. subst. easy. easy.
              }
              clear Ha Hb.
              rename H0 into Ha.
              rename H1 into Hb.
              apply invdropH1 with (xs := xs); easy.
       - intro Hc.
         destruct Hc as [Hc | Hc].
         + subst.
           assert(x = a \/ In a xs).
           { apply Hb. left. easy. }
           destruct H0 as [H0 | H0].
           ++ subst. easy.
           ++ apply in_before_drop; easy.
         + specialize(classic (x = a)); intro Heq.
           destruct Heq as [Heq | Heq].
           ++ subst. apply dropSame in Hc. easy.
           ++ assert(In a xs -> y = a \/ In a ys).
              { intro Hd. apply Ha. right. easy. }
              clear Ha.
              rename H0 into Ha.
              assert(y = a \/ In a ys -> In a xs).
              { intro Hd. apply Hb in Hd. 
                destruct Hd as [Hd | Hd].
                + subst. easy.
                + easy.
              }
              clear Hb.
              rename H0 into Hb.
              specialize(classic (y = a)); intro Heq2.
              destruct Heq2 as [Heq2 | Heq2].
              * assert(In a xs).
                { apply Hb. left. easy. }
                apply in_before_drop; easy.
              * assert(In a xs -> In a ys).
                { intro Hd.
                  apply Ha in Hd.
                  destruct Hd as [Hd | Hd].
                  + subst. easy.
                  + easy.
                }
                clear Ha. rename H0 into Ha.
                assert(In a ys -> In a xs).
                { intro Hd. apply Hb. right. easy. }
                clear Hb. rename H0 into Hb.
                apply invdropH1 with (xs := ys); easy.
Qed.

Lemma invdropES: forall xs ys x,
  (forall a, In a (x::xs) <-> In a (x::ys)) ->
  (forall a, In a (dropE (x::xs) x) <-> In a (dropE (x::ys) x)).
Proof. intros.
       rewrite !dl.
       specialize(H a).
       destruct H as (Ha, Hb).
       simpl in Ha, Hb.
       specialize(classic (x = a)); intro Heq.
       destruct Heq as [Heq | Heq].
       + subst. split. intro Hc.
         apply dropSame in Hc. easy.
       + intro Hc.
         apply dropSame in Hc. easy.
         assert(In a xs -> In a ys).
         { intro Hc.
           assert(x = a \/ In a xs).
           { right. easy. }
           apply Ha in H.
           destruct H. subst. easy. easy.
         }
         clear Ha. rename H into Ha.
         assert(In a ys -> In a xs).
         { intro Hc.
           assert(x = a \/ In a ys).
           { right. easy. }
           apply Hb in H.
           destruct H. subst. easy. easy.
         }
         clear Hb. rename H into Hb.
         split. intro Hc.
         apply invdropH1 with (xs := xs); easy.
         intro Hc.
         apply invdropH1 with (xs := ys); easy.
Qed.

Lemma invdropE: forall xs ys x,
  (forall a, In a xs <-> In a ys) ->
  (forall a, In a (dropE xs x) <-> In a (dropE ys x)).
Proof. intros xs ys x.
       case_eq xs; case_eq ys; intros.
       - subst. simpl. easy.
       - subst. apply nilIff in H1. easy.
       - subst. symmetry in H1. apply nilIff in H1. easy.
       - subst. 
         specialize(classic (p0 = x)); intro Heq.
         destruct Heq as [Heq | Heq].
         + subst.
           specialize(classic (p = x)); intro Heq2.
           destruct Heq2 as [Heq2 | Heq2].
           ++ subst. 
              revert a.
              apply invdropES. easy.
           ++ revert a.
              apply invdropEN. easy. easy.
         + specialize(classic (p = x)); intro Heq2.
           destruct Heq2 as [Heq2 | Heq2].
           ++ subst. 
              symmetry. symmetry in H1.
              revert a.
              apply invdropEN. easy. easy.
           ++ rewrite !dlN; try easy.
              simpl.
              specialize(H1 a).
              destruct H1 as (Ha, Hb).
              simpl in Ha, Hb.
              split.
              * intro Hc.
                destruct Hc as [Hc | Hc].
                ** subst.
                   assert(p = a \/ In a l).
                   { apply Ha. left. easy. }
                   clear Ha. rename H into Ha.
                   destruct Ha as [Ha | Ha].
                   *** left. easy.
                   *** right. apply in_before_drop; easy.
                ** specialize(classic (p = a)); intro Heq3.
                   destruct Heq3 as [Heq3 | Heq3].
                   *** subst.  left. easy.
                   *** specialize(classic (p0 = a)); intro Heq4.
                       destruct Heq4 as [Heq4 | Heq4].
                       +++ subst. 
                           assert(In a l).
                           { assert(a = a \/ In a l0).
                             { left. easy. }
                             apply Ha in H.
                             destruct H. subst. easy. easy.
                           }
                           right. apply in_before_drop; easy.
                       +++ assert(In a l0 -> In a l).
                           { intro Hd.
                             assert(p0 = a \/ In a l0).
                             { right. easy. }
                             apply Ha in H.
                             destruct H. subst. easy. easy. 
                            }
                           assert(In a l -> In a l0).
                           { intro Hd.
                             assert(p = a \/ In a l).
                             { right. easy. }
                             apply Hb in H0.
                             destruct H0. subst. easy. easy.
                           }
                           specialize(classic (x = a)); intro Heq5.
                           destruct Heq5 as [Heq5 | Heq5].
                           -- subst. apply dropSame in Hc. easy.
                           -- right. apply invdropH1 with (xs := l0); easy.
              * intro Hc.
                destruct Hc as [Hc | Hc].
                ** subst.
                   assert(p0 = a \/ In a l0).
                   { apply Hb. left. easy. }
                   clear Hb. rename H into Hb.
                   destruct Hb as [Hb | Hb].
                   *** left. easy.
                   *** right. apply in_before_drop; easy.
                ** specialize(classic (p0 = a)); intro Heq3.
                   destruct Heq3 as [Heq3 | Heq3].
                   *** subst.  left. easy.
                   *** specialize(classic (p = a)); intro Heq4.
                       destruct Heq4 as [Heq4 | Heq4].
                       +++ subst. 
                           assert(In a l0).
                           { assert(a = a \/ In a l).
                             { left. easy. }
                             apply Hb in H.
                             destruct H. subst. easy. easy.
                           }
                           right. apply in_before_drop; easy.
                       +++ assert(In a l0 -> In a l).
                           { intro Hd.
                             assert(p0 = a \/ In a l0).
                             { right. easy. }
                             apply Ha in H.
                             destruct H. subst. easy. easy. 
                            }
                           assert(In a l -> In a l0).
                           { intro Hd.
                             assert(p = a \/ In a l).
                             { right. easy. }
                             apply Hb in H0.
                             destruct H0. subst. easy. easy.
                           }
                           specialize(classic (x = a)); intro Heq5.
                           destruct Heq5 as [Heq5 | Heq5].
                           -- subst. apply dropSame in Hc. easy.
                           -- right. apply invdropH1 with (xs := l); easy.
Qed.

Lemma notInCoseq: forall a s l,
  coseqInLC s l ->
  ~ coseqIn a s ->
  coseqInLC s (dropE l a).
Proof. pcofix CIH. intros.
       pinversion H0.
       subst. pfold. constructor.
       subst. pfold.
       constructor.
       case_eq(sdir_eqb a x); intros.
       - rewrite sdir_eqb_eq in H3. subst.
         contradict H1.
         apply CoInSplit1 with (y := x) (ys := xs). easy. easy.
       - rewrite sdir_eqb_neq in H3. subst.
         apply in_before_drop; easy.
         right. apply CIH. easy.
         unfold not. intro Ha.
         apply H1.
         case_eq(sdir_eqb a x); intros.
         + rewrite sdir_eqb_eq in H3. subst.
           apply CoInSplit1 with (y := x) (ys := xs). easy. easy.
         + rewrite sdir_eqb_neq in H3. subst.
           apply CoInSplit2 with (y := x) (ys := xs). easy. easy.
           easy.
       apply coseqInLC_mon.
Qed.

Lemma notInList: forall l a s,
~ coseqIn a s ->
coseqInR l s ->
coseqInR (dropE l a) s.
Proof. intro l.
       induction l; intros.
       - simpl. constructor.
       - inversion H0. subst.
         case_eq(sdir_eqb a a0); intros.
         + rewrite sdir_eqb_eq in H1.
           subst.
           rewrite dl.
           apply IHl; easy.
         + rewrite sdir_eqb_neq in H1.
           rewrite dlN.
           constructor. easy.
           apply IHl; easy.
           easy.
Qed.

Lemma dropEq: forall l a,
~ In a l ->
  l = dropE l a.
Proof. intro l.
       induction l; intros.
       - simpl. easy.
       - simpl in H.
         apply not_or_and in H.
         destruct H as (Ha, Hb).
         rewrite dlN.
         apply IHl in Hb.
         rewrite <- Hb. easy.
         easy.
Qed.

