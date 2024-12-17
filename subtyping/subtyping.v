Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Fixpoint listSisoPRef (l: list (siso*siso)): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => (exists d1, exists d2, (forall n, refinement (merge_dp_contn d1 (@und W) n) (merge_dp_contn d2 (@und W') n))) /\ listSisoPRef xs
  end.

Fixpoint decomposeL (l: list (siso*siso)) (s: st) (s': st): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => st2sisoC (@und W) s /\ st2sisoC (@und W') s' /\ decomposeL xs s s'
  end.

Definition subtype (T T': st): Prop := exists (l: list (siso*siso)), decomposeL l T T' /\ listSisoPRef l.

Fixpoint listSisoPRef2 (l: list (siso*siso)): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => (exists d1, exists d2, (forall n, (merge_dp_contn d1 (@und W) n) ~<  (merge_dp_contn d2 (@und W') n))) /\ listSisoPRef2 xs
  end.

Definition subtype2 (T T': st): Prop := exists (l: list (siso*siso)), decomposeL l T T' /\ listSisoPRef2 l.

Definition subltype (T T': local) (T1 T2: st) (P: lt2stC T T1) (Q: lt2stC T' T2) := subtype T1 T2.

Definition subltype2 (T T': local) (T1 T2: st) (P: lt2stC T T1) (Q: lt2stC T' T2) := subtype2 T1 T2.

Lemma pneqq: forall p q a l l' s s' w w' (H: p <> q),
  q & [(l, s, w)] = merge_ap_cont p (ap_merge q H p s a) (p & [(l', s', w')]) ->
  w = merge_ap_cont p a (p & [(l', s', w')]) .
Proof. intros p q a.
       induction a; intros.
       - rewrite(st_eq( merge_ap_cont p (ap_merge q H p s1 (ap_receive q0 n s s0)) (p & [(l', s', w')]))) in H0.
         simpl in H0. inversion H0. subst. easy.
       - rewrite(st_eq(merge_ap_cont p (ap_merge q H p s1 (ap_merge q0 n s s0 a)) (p & [(l', s', w')]))) in H0.
         simpl in H0. inversion H0. easy.
         rewrite(st_eq(merge_ap_cont p (ap_merge q H p s ap_end) (p & [(l', s', w')]))) in H0.
         simpl in H0. inversion H0. easy.
Qed.

Lemma pneqq2: forall p q a l l' s s' w w' (H: p <> q),
  q & [(l, s, w)] = merge_ap_cont p a (p & [(l', s', w')]) ->
  exists a', w = merge_ap_cont p a' (p & [(l', s', w')]) /\
  (a = (ap_merge q H l s a') \/ (a = (ap_receive q H l s) /\ a' = ap_end)).
Proof. intros p q a.
       induction a; intros.
       - rewrite(st_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l', s', w')]))) in H0.
         simpl in H0. inversion H0. subst.
         exists ap_end. split. rewrite apend_an. easy.
         right. split. 
         specialize(proof_irrelevance _ n H); intros. subst. easy. easy.
       - rewrite(st_eq(merge_ap_cont p (ap_merge q0 n s s0 a) (p & [(l', s', w')]))) in H0.
         simpl in H0. inversion H0. subst.
         exists a. split. easy. left.
         specialize(proof_irrelevance _ n H); intros. subst. easy.
       - rewrite apend_an in H0. inversion H0. subst. easy.
Qed.

Fixpoint isInAp {p} (a: Ap p) q: bool :=
  match a with
    | ap_merge q' H l s a' => eqb q' q || isInAp a' q
    | ap_receive q' H l s  => eqb q' q
    | _                   => false
  end.

Lemma isInAp_dec: forall {p} (a: Ap p) q, isInAp a q = true \/ isInAp a q = false.
Proof. intros p a.
       induction a; intros.
       - simpl.
         case_eq(eqb q q0); intros; [left; easy | right; easy].
         simpl.
         case_eq(eqb q q0); intros.
         + rewrite eqb_eq in H. subst.
           left. easy.
         + specialize(IHa q0).
           destruct IHa as [IHa | IHa].
           -- left. easy.
           -- right. easy.
        - simpl. right. easy.
Qed.

Lemma pRevq: forall p a q l s w,
  p <> q ->
  isInAp a q ->
  exists a' l' s' w',
  merge_ap_cont p a (p & [(l, s, w)]) = merge_ap_cont q a' (q & [(l', s', w')]).
Proof. intros p a.
       induction a; intros.
       - simpl in H0.
         apply eqb_eq in H0. subst.
         rewrite(st_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))).
         simpl.
         exists ap_end. exists s. exists s0. exists (p & [(l, s1, w)]).
         rewrite apend_an. easy.
       - simpl in H0.
         Search orb.
         apply Bool.orb_true_iff in H0.
         destruct H0 as [H0 | H0].
         + apply eqb_eq in H0. subst.
           rewrite(st_eq( merge_ap_cont p (ap_merge q0 n s s0 a) (p & [(l, s1, w)]))).
           simpl. 
           exists ap_end. exists s. exists s0.
           exists (merge_ap_cont p a (p & [(l, s1, w)])).
           rewrite apend_an. easy.
           
           rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))).
           simpl.
           specialize(IHa q0 l s1 w H H0).
           destruct IHa as (a',(l',(s',(w',IHa)))).
           rewrite IHa.
           case_eq(eqb q0 q); intros.
           -- apply eqb_eq in H1. subst.
              exists ap_end. exists s. exists s0.
              exists ( merge_ap_cont q a' (q & [(l', s', w')])).
              rewrite apend_an. easy.
           -- apply eqb_neq in H1.
              exists (ap_merge q H1 s s0 a').
              exists l'. exists s'. exists w'.
              rewrite(st_eq(merge_ap_cont q0 (ap_merge q H1 s s0 a') (q0 & [(l', s', w')]))).
              simpl. easy.
        - simpl in H0. easy.
Qed.

Lemma helperRecv:
  forall a b c r,
  a ~< b ->
  b ~< c ->
  (forall x y z : st, x ~< y -> y ~< z -> r x z) ->
  paco2 refinementR2 r a c.
Proof. intros.
       pfold.
       red in H, H0.
       pinversion H.
       - subst. 
         pinversion H0.
         + subst.
         case_eq (String.eqb p0 p); intros.
         ++ rewrite eqb_eq in H9. subst.
            pose proof H5 as H5A.
            rewrite <- meqAp in H5, H5A.
            specialize(ApApeqInvAnd p (ApnA2 p a0 n) l l0 s' s0 w' w0); intros HR.
            symmetry in H5.
            apply HR in H5.
            specialize (ApApeqInv p ap_end (ApnA2 p a0 n) l0 l s0 s' w0 w'); intros.
            rewrite apend_an in H9.
            apply H9 in H5A. inversion H5A. subst.
            constructor.
            admit.
            rewrite <- meqAp in H3.
            rewrite H5 in H3.
            rewrite apend_an in H3.
            right. apply H1 with (y := w'). easy. easy.
            admit.
         ++ rewrite eqb_neq in H9.
            rename p0 into q.
            rewrite <- meqAp in H5.
            assert(p <> q) by easy.
            apply pneqq2 with (H := H10) in H5.
            destruct H5 as (a',(Hw0,H5)).
            destruct H5 as [H5 | H5].
 
            rewrite <- meqAp.
            rewrite <- meqAp in H3, H7, H8, H4.
            specialize(isInAp_dec (ApnA2 q a n0) p); intros HLEM.
            destruct HLEM as [HL| HL].
            specialize(pRevq q (ApnA2 q a n0) p l0 s'0 w'0 H9 HL); intro HS.
            destruct HS as (a1,(l1,(s1,(w1,HS)))).
            rewrite HS.
Admitted.

Lemma endAp: forall p a l s w, end = merge_ap_cont p a (p & [(l, s, w)]) -> False.
Proof. intros p a.
       case_eq a; intros.
       - rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H0.
         simpl in H0. easy.
       - rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a0) (p & [(l, s1, w)]))) in H0.
         simpl in H0. easy.
       - rewrite apend_an in H0. easy.
Qed.

Lemma refTrans: Transitive (refinement2).
Proof. red. pcofix CIH.
       intros x y z Ha Hb.
       pinversion Ha. subst.
       pinversion Hb. subst.
(*     + punfold H0. punfold H4.
         pfold. *)
         case_eq (String.eqb p0 p); intros.
         ++ rewrite eqb_eq in H6. subst.
            punfold H0. punfold H4.
            pfold.
            pose proof H2 as H2A.
            rewrite <- meqAp in H2.
            specialize(ApApeqInvAnd p (ApnA2 p a n) l l0 s' s0 w' w0); intros HR.
            symmetry in H2.
            apply HR in H2.
            rewrite <- meqAp in H0.
            rewrite H2 in H0. rewrite apend_an in H0.
            
            rewrite <- meqAp in H2A.
            specialize(@ApApeqInv p ap_end (ApnA2 p a n) l0 l s0 s' w0 w'); intros HRA.
            rewrite apend_an in HRA.
            apply HRA in H2A.
            inversion H2A. subst.
            constructor.
            admit.
            * right. apply CIH with (y := w').
              unfold refinement. pfold. easy.
              pfold. easy.
            * rewrite <- meqAp in H1.
              rewrite H2 in H1. rewrite apend_an in H1.
              unfold act_eq. intros. split.
              intros. apply H5. apply H1. easy.
              intros. apply H1. apply H5. easy.
              apply refinementR2_mon.
              apply refinementR2_mon.
         ++ rewrite eqb_neq in H6.
            rename p0 into q.
            rewrite <- meqAp2 in H2.
            assert(p <> q) by easy.
            specialize (pneqq2 p q (ApnA p a n) l0 l s0 s' w0 w' H7 H2); intros.
            destruct H8 as (a',(Hw0,H8)).
            destruct H8.
            rewrite <- meqAp2 in H0, H1, H4.
            rewrite H8 in H0.
            rewrite(st_eq((merge_ap_cont p (ap_merge q H7 l0 s0 a') w'))) in H0.
            simpl in H0. rewrite <- meqAp2.
            rewrite <- meqAp2 in H5.
            assert(paco2 refinementR2 bot2 (p & [(l, s, w)]) (q & [(l0, s0, merge_ap_cont p a' (p & [(l, s', w')]))])).
            { pfold.
              assert((q & [(l0, s0, merge_ap_cont p a' (p & [(l, s', w')]))]) = merge_ap_cont p (ap_merge q H7 l0 s0 a') (p & [(l, s', w')])).
              { rewrite(st_eq(merge_ap_cont p (ap_merge q H7 l0 s0 a') (p & [(l, s', w')]))). simpl. easy. }
              rewrite H9.
              specialize(ref2_a  (upaco2 refinementR2 bot2) w w' p l s s' (ap_merge q H7 l0 s0 a') 1); intro HR.
              simpl in HR. apply HR.
              easy.
              left.
              rewrite(st_eq((merge_ap_cont p (ap_merge q H7 l0 s0 a') w'))).
              simpl. easy.
              rewrite H8 in H1. easy.
            }
            rewrite <- Hw0 in H9.
            assert(paco2 refinementR2 bot2 (q & [(l0, s0, w0)])
                  (merge_ap_cont q (ApnA q a0 n0) (q & [(l0, s'0, w'0)]))).
            { pfold. 
              specialize(ref2_a (upaco2 refinementR2 bot2) w0 w'0 q l0 s0 s'0 (ApnA q a0 n0) 1); intro HR.
              simpl in HR.
              apply HR.
              easy.
              left. easy.
              easy.
            }
            pose proof CIH as CIH2.
            specialize(CIH2 (p & [(l, s, w)]) (q & [(l0, s0, w0)])
                            (merge_ap_cont q (ApnA q a0 n0) (q & [(l0, s'0, w'0)]))
                            H9 H10).
            apply helperRecv with (b := (q & [(l0, s0, w0)])). easy. easy. easy.
            
            rewrite <- meqAp2 in H0, H1, H4.
            destruct H8 as (H8a,H8b).
            rewrite H8a in H0.
            rewrite(st_eq((merge_ap_cont p (ap_receive q H7 l0 s0) w'))) in H0.
            simpl in H0.
            rewrite <- meqAp2.
            rewrite <- meqAp2 in H5.
            rewrite Hw0 in H4.
            assert(paco2 refinementR2 bot2 (p & [(l, s, w)]) (q & [(l0, s0, (p & [(l, s', w')]))])).
            { pfold.
              assert((q & [(l0, s0, p & [(l, s', w')])])= merge_ap_cont p (ApnA p a n ) (p & [(l, s', w')])).
              { rewrite(st_eq(merge_ap_cont p (ApnA p a n) (p & [(l, s', w')]))). rewrite H8a. simpl. easy. }
              rewrite H8.
              specialize(ref2_a  (upaco2 refinementR2 bot2) w w' p l s s' (ApnA p a n) 1); intro HR.
              simpl in HR. apply HR.
              easy.
              left.
              rewrite(st_eq((merge_ap_cont p (ApnA p a n) w'))). rewrite H8a.
              simpl. easy. easy.
            }
            assert(paco2 refinementR2 bot2 (q & [(l0, s0, p & [(l, s', w')])]) (merge_ap_cont q (ApnA q a0 n0) (q & [(l0, s'0, w'0)]))).
            { pfold.
              specialize(ref2_a (upaco2 refinementR2 bot2) (p & [(l, s', w')]) w'0 q l0 s0 s'0 (ApnA q a0 n0) 1); intro HR.
              simpl in HR. apply HR.
              easy.
              left.
              rewrite H8b in H4.
              rewrite apend_an in H4. easy.
              rewrite Hw0 H8b in H5.
              rewrite apend_an in H5. easy.
            } 
            pose proof CIH as CIH2.
            specialize(CIH2 (p & [(l, s, w)]) (q & [(l0, s0, p & [(l, s', w')])])
                            (merge_ap_cont q (ApnA q a0 n0) (q & [(l0, s'0, w'0)]))
                            H8 H9).
            apply helperRecv with (b := (q & [(l0, s0, p & [(l, s', w')])])). easy. easy. easy.
        
        (*recv - send case*)
        subst.
        symmetry in H2.
        apply case11 in H2. easy.
        (*recv - end case*)
        subst.
        rewrite <- meqAp2 in H3.
        apply endAp in H3. easy.
        
        apply refinementR2_mon.
        
        subst.
       pinversion Hb. subst.
       (*send - recv case*)
       - admit. (*contradicts H2*)
       
       subst.
       - admit.
       
       subst.
       - admit.
        apply refinementR2_mon.
        
        subst. pinversion Hb.
        pfold. constructor.
        apply refinementR2_mon.
        apply refinementR2_mon.
Admitted.


