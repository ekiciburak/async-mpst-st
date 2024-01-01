From ST Require Import stream st so si siso norefined.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import ProofIrrelevance.

Inductive nRefinementNc: siso -> siso -> Prop :=
  | n_outNc  : forall w w' p l s P, 
              CoNInR (p,"!"%string) (act (@und w')) -> 
              nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) P) w'
  | n_inpNc  : forall w w' p l s P, 
              CoNInR (p,"?"%string) (act (@und w')) -> 
              nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) w'
  | n_out_rNc: forall w w' p l s P, 
               CoNInR (p,"!"%string) (act (@und w)) -> 
               nRefinementNc w (mk_siso (st_send p [(l,s,(@und w'))]) P)
  | n_inp_rNc: forall w w' p l s P,
              CoNInR (p,"?"%string) (act (@und w)) -> 
              nRefinementNc w (mk_siso (st_receive p [(l,s,(@und w'))]) P)
  | n_inp_lNc: forall w w' p l l' s s' P Q,
             l <> l' -> nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                     (mk_siso (st_receive p [(l',s',(@und w'))]) Q)
  | n_inp_sNc: forall w w' p l s s' P Q,
              nsubsort s' s -> nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P)
                                            (mk_siso (st_receive p [(l,s',(@und w'))]) Q)
  | n_inp_wNc: forall w w' p l s s' P Q,
              subsort s' s -> nRefinementNc w w' -> nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                                (mk_siso (st_receive p [(l,s',(@und w'))]) Q)
  | n_a_lNc  : forall w w' p l l' s s' a n P Q,
              l <> l' -> nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                      (mk_siso (merge_cp_contn p a (st_receive p [(l',s',(@und w'))]) n) Q)
  | n_a_sNc  : forall w w' p l s s' a n P Q,
              nsubsort s' s -> 
              nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                           (mk_siso (merge_cp_contn p a (st_receive p [(l,s',(@und w'))]) n) Q)
  | n_a_wNc  : forall w w' p l s s' a n P Q R,
              subsort s' s ->
              nRefinementNc w (mk_siso (merge_cp_contn p a (@und w') n) P) ->
              nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) Q) 
                           (mk_siso (merge_cp_contn p a (st_receive p [(l,s',(@und w'))]) n) R)
  | n_i_o_1Nc: forall w w' p q l l' s s' P Q, nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                            (mk_siso (st_send q [(l',s',(@und w'))]) Q)
  | n_i_o_2Nc: forall w w' p q l l' s s' (a: Cp p) n P Q, nRefinementNc (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                                  (mk_siso (merge_cp_contn p a (st_send q [(l',s',(@und w'))]) n) Q)
  | n_out_lNc: forall w w' p l l' s s' P Q,
              l <> l' -> nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                      (mk_siso (st_send p [(l',s',(@und w'))]) Q)
  | n_out_sNc: forall w w' p l s s' P Q,
              nsubsort s s' -> nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                            (mk_siso (st_send p [(l,s',(@und w'))]) Q)
  | n_out_wNc: forall w w' p l s s' P Q,
              subsort s s' -> nRefinementNc w w' -> nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                                                (mk_siso (st_send p [(l,s',(@und w'))]) Q)
  | n_b_lNc  : forall w w' p l l' s s' b n P Q,
              l <> l' -> nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                      (mk_siso (merge_bp_contn p b (st_send p [(l',s',(@und w'))]) n) Q)
  | n_b_sNc  : forall w w' p l s s' b n P Q,
              nsubsort s s' -> 
              nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) P) 
                           (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) Q)
  | n_b_wNc  : forall w w' p l s s' b n P Q R,
              subsort s s' ->
              nRefinementNc w (mk_siso (merge_bp_contn p b (@und w') n) P) ->
              nRefinementNc (mk_siso (st_send p [(l,s,(@und w))]) Q) 
                           (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) R).


Notation "x '//~<' y" := (nRefinementNc x y) (at level 50, left associativity).


Lemma merge_eq4c: forall p a1 a2 l s w,
merge_ap_cont p a1 (p & [(l, s, w)]) =
merge_cp_cont p a2 (p & [(l, s, w)]) ->
merge_ap_cont p a1 w =
merge_cp_cont p a2 w.
Proof. intros p a1.
       induction a1; intros.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) w )).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl.
       easy.
       
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c) w)).
       simpl.
       case_eq c; intros.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q n1 s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s4) (p & [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s4 c0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. easy.

       subst. rewrite cpend_an. easy.
       subst.
       
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]) )) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H. simpl in H. 
       inversion H. subst. easy.

       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) w)). simpl.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a1; intros.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q n1 s s0 a) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a1) w)).
       simpl.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c) w)).
       simpl.
       rewrite (IHa1 c l s1 w). easy. easy.
       
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H. simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       
       case_eq a2; intros.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s0 s1 c) (p & [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (p & [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (p & [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite apend_an. rewrite cpend_an. easy.
Qed.

Lemma case12_1c: forall n p q a l l' s s' w w',
p & [(l, s, w)] = merge_cp_contn p a (q ! [(l', s', w')]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s0 s1) (merge_cp_contn p (cp_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s0 s1 c) (merge_cp_contn p (cp_mergea q0 n0 s0 s1 c) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (merge_cp_contn p (cp_send s0 s1 s2) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (merge_cp_contn p (cp_merge s0 s1 s2 c) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy. 
       subst.
       rewrite cpend_ann in H.
       rewrite cpend_an in H. easy.
Qed.

Lemma case12_2c: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_cp_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n1 s s0 c0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s4) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s4 c0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       
       subst.
       rewrite cpend_an in H4. easy.
       
       subst.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]) )) in H.
       simpl in H. easy.

       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (cp_end) l l' s1 s' w w').
       apply IHa1.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea q1 n0 s2 s3 c) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 c l l' s1 s' w w').
       apply IHa1. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       
       subst. rewrite cpend_an in H.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n s0 s1 c) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
Qed.

Lemma nrefNLSC: forall w w',  (@und w) ~< (@und w') -> (nRefinementNc w w' -> False).
Proof. intros w w' H.
       unfold refinement in H.
       punfold H; [ | apply refinementR_mon].
       intro Ha.
       induction Ha; intros.
       {
         inversion H.
         subst.
         apply inOutLA in H0. easy. 
         rewrite <- H6.
         simpl.
         rewrite(coseq_eq(act (p ! [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w'0)). easy.
         apply inOutLA in H0. easy.
         rewrite <- H6.
         rewrite h0.
         pfold.
         apply eq0A.
         right.
         rewrite(coseq_eq(act (p ! [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         apply CoInSplit1A with (ys := (act w'0)). simpl. easy.
       }
       { inversion H.
         subst.
         apply inOutLA in H0. easy. rewrite <- H6.
         rewrite(coseq_eq(act (p & [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w'0)). easy.
         subst.
         apply inOutLA in H0. easy.
         simpl.
         pfold. rewrite <- H6.
         rewrite h1.
         apply eq0A.
         right.
         rewrite(coseq_eq(act (p & [(l, s0, w'0)]))). unfold coseq_id. simpl.
         apply CoInSplit1A with (ys := (act w'0)). simpl. easy.
       }
       { inversion H.
         subst.
         apply inOutLA in H0. easy. rewrite <- H1.
         rewrite(coseq_eq(act (p ! [(l, s0, w0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w0)). easy.

         unfold act_eq in H5.
         rewrite <- H1 in H0.
         apply inOutLA in H0. easy.
         rewrite(coseq_eq (act (p0 & [(l0, s', w0)]))). unfold coseq_id. simpl.
         pfold.
         apply CoInSplit2A with (y := (p0, "?"%string)) (ys := (act w0)). simpl. easy. easy.
         unfold upaco2.
         specialize(H5 (p, "!"%string)).
         unfold CoIn in H5. left.
         apply H5.
         pfold.

         case_eq n; intros.
         simpl in *. subst. inversion H2. 

         case_eq a; intros.
         subst.
         simpl in H2.
         rewrite(siso_eq(merge_ap_cont p0 (ap_receive q n1 s1 s2)
                        (merge_ap_contn p0 (ap_receive q n1 s1 s2) (p0 & [(l0, s0, w'0)]) n0))) in H2.
         simpl in H2.
         easy.

         subst.
         simpl in H2.
         rewrite(siso_eq(merge_ap_cont p0 (ap_merge q n1 s1 s2 a0) (merge_ap_contn p0 (ap_merge q n1 s1 s2 a0) 
          (p0 & [(l0, s0, w'0)]) n0) )) in H2.
         simpl in H2.
         inversion H2.
         subst.
         rewrite h1.
         apply eq0A.
         subst.
         rewrite apend_ann in H2. easy.

        (* subst.
         rewrite apend_ann in H1.
         inversion H1.  *)
         (*middle*)
         unfold act_eq in H5.
         rewrite <- H1 in H0.
         apply inOutLA in H0. easy.
         case_eq(eqb p p0); intro Heq.

         rewrite(coseq_eq(act (p0 ! [(l0, s0, w0)]))). unfold coseq_id. simpl.
         rewrite eqb_eq in Heq. subst.
         pfold.
         apply CoInSplit1A with (ys := (act w0)). easy.

         rewrite eqb_neq in Heq.
         rewrite(coseq_eq(act (p0 ! [(l0, s0, w0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit2A with (y := (p0, "!"%string)) (ys := (act w0)). simpl. easy.
         unfold not in *.
         intro Heq2.
         apply Heq. inversion Heq2. easy.
         unfold upaco2. left.
         specialize(H5 (p, "!"%string)).
         unfold CoIn in H5.
         apply H5.
         pfold.

         case_eq n; intros.
         simpl in *. subst. inversion H2. subst. easy.
         rewrite h0.
         apply eq0A.
         subst.

         case_eq b; intros.
         subst.
         simpl in H2.
         rewrite(siso_eq(merge_bp_cont p0 (bp_receivea s1 s2 s3) (merge_bp_contn p0 (bp_receivea s1 s2 s3) (p0 ! [(l0, s', w'0)]) n0))) in H2.
         simpl in H2.
         easy.

         subst.
         simpl in H2.
         rewrite(siso_eq(merge_bp_cont p0 (bp_send q n s1 s2) (merge_bp_contn p0 (bp_send q n s1 s2) (p0 ! [(l0, s', w'0)]) n0))) in H2.
         simpl in H2.
         inversion H2.
         subst.
         clear H2.
         left. simpl. left. easy.

         subst.
         simpl in H2.
         rewrite(siso_eq(merge_bp_cont p0 (bp_mergea s1 s2 s3 b0) (merge_bp_contn p0 (bp_mergea s1 s2 s3 b0) (p0 ! [(l0, s', w'0)]) n0))) in H2.
         simpl in H2.
         easy.

         subst.
         simpl in H2.
         rewrite(siso_eq(merge_bp_cont p0 (bp_merge q n s1 s2 b0) (merge_bp_contn p0 (bp_merge q n s1 s2 b0) (p0 ! [(l0, s', w'0)]) n0))) in H2.
         simpl in H2.
         inversion H2.
         left. simpl. subst. left. easy.

         subst.
         rewrite bpend_ann in H2.
         inversion H2. subst. easy.
       }
       { inversion H.
         subst.
         apply inOutLA in H0. easy. rewrite <- H1.
         rewrite(coseq_eq(act (p & [(l, s0, w0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w0)). easy.

         unfold act_eq in H5.
         rewrite <- H1 in H0.
         apply inOutLA in H0. easy.
         case_eq(eqb p p0); intro Heq.

         rewrite(coseq_eq(act (p0 & [(l0, s', w0)]))). unfold coseq_id. simpl.
         rewrite eqb_eq in Heq. subst.
         pfold.
         apply CoInSplit1A with (ys := (act w0)). easy.

         rewrite eqb_neq in Heq.
         rewrite(coseq_eq(act (p0 & [(l0, s', w0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit2A with (y := (p0, "?"%string)) (ys := (act w0)). simpl. easy.
         unfold not in *.
         intro Heq2.
         apply Heq. inversion Heq2. easy.
         unfold upaco2. left.
         specialize(H5 (p, "?"%string)).
         unfold CoIn in H5.
         apply H5.
         pfold.

         case_eq n; intros.
         simpl in *. subst. inversion H2. subst. easy.
         rewrite h1.
         apply eq0A.
         subst.

         case_eq a; intros.
         subst.
         simpl in H2.
         rewrite(siso_eq(merge_ap_cont p0 (ap_receive q n s1 s2)
                        (merge_ap_contn p0 (ap_receive q n s1 s2) (p0 & [(l0, s0, w'0)]) n0) )) in H2.
         simpl in H2.
         inversion H2.
         subst.
         left. simpl. left. easy.

         subst.
         simpl in H2.
         rewrite(siso_eq(merge_ap_cont p0 (ap_merge q n s1 s2 a0)
                        (merge_ap_contn p0 (ap_merge q n s1 s2 a0) (p0 & [(l0, s0, w'0)]) n0))) in H2.
         simpl in H2.
         simpl. inversion H2. subst. left. left. easy.

         subst.
         rewrite apend_ann in H2.
         inversion H2. subst. easy.

         apply inOutLA in H0. easy.
         rewrite <- H1.
         rewrite(coseq_eq((act (p0 ! [(l0, s0, w0)])))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit2A with (y := (p0, "!"%string)) (ys := (act w0)). simpl. easy. easy.
         unfold upaco2.
         left.
         unfold act_eq in H5.
         apply H5.

         case_eq b; intros.
         subst.
         simpl in H1.
         case_eq n; intros.
         subst. simpl in *. inversion H2.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_receivea s1 s2 s3) (p0 ! [(l0, s', w'0)]) n0.+1)) in H2.
         simpl in H2. inversion H2.
         subst.
         rewrite(coseq_eq( (act (merge_bp_contn p0 (bp_receivea p l s) w'0 n0.+1)))). unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act (merge_bp_contn p0 (bp_receivea p l s) w'0 n0))). simpl. easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. inversion H2.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_send q n0 s1 s2) (p0 ! [(l0, s', w'0)]) n1.+1)) in H2. simpl in H2. easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_mergea s1 s2 s3 b0) (p0 ! [(l0, s', w'0)]) n0.+1)) in H2.
         simpl in H2. inversion H2. subst.
         rewrite h0.
         pfold.
         apply eq0A.
         simpl. left. left. easy.
         case_eq n; intros.
         subst. simpl in *. inversion H2.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_merge q n0 s1 s2 b0) (p0 ! [(l0, s', w'0)]) n1.+1)) in H2.
         simpl in H2. easy.
         subst.
         rewrite bpend_ann in H2.
         easy.
       }
       {
         inversion H.
         subst. easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s0, w'0)]) n0.+1)) in H6.
         simpl in H6.
         case_eq a; intros.
         subst. inversion H6. subst. easy.
         subst. inversion H6. 
         subst. easy.
         subst. rewrite apend_ann in H6. inversion H6. subst. easy.
       }
       { inversion H.
         subst. apply ssnssL in H0. easy.
         easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. apply ssnssL in H0. easy.
         apply ssnssR in H4. easy. easy.

         subst.
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s0, w'0)]) n0.+1)) in H6. simpl in H6.
         destruct a.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         rewrite apend_ann in H6.
         inversion H6.
         subst.
         apply ssnssR in H4. easy. easy.
       }
       {
         apply IHHa.
         inversion H. subst.
         unfold upaco2 in H8.
         destruct H8.
         punfold H1.
         apply refinementR_mon.
         easy.
         subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.
         case_eq n; intros.
         subst. simpl in *.
         inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s0, w'0)]) n0.+1)) in H6.
         simpl in H6.
         destruct a.
         inversion H6. subst. simpl in H1. easy.
         inversion H6. subst. easy.
         rewrite apend_ann in H6.
         inversion H6. subst.
         rewrite apend_ann in H1. easy.
         apply refinementR_mon.
         easy.
       }
       {
         inversion H.
         subst.

         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         induction n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq( merge_cp_contn p a (p & [(l', s', und)]) n.+1)) in H6.
         case_eq a; intros.
         subst. inversion H6. subst. easy.
         subst. inversion H6. 
         subst. easy.
         subst. inversion H6.
         subst. inversion H6.
         subst. rewrite cpend_ann in H6. inversion H6. subst. easy.
         apply refinementR_mon.
         easy.


         subst.
         rewrite <- mergeeq in H6.
         rewrite <- mergeeq4 in H6.
         apply merge_eqc in H6.
         inversion H6. subst. easy.
       }
       { inversion H.
         subst.
         
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         induction n; intros.
         subst. simpl in *. inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         rewrite(siso_eq(merge_cp_contn p a (p & [(l, s',und)]) n.+1)) in H6. simpl in H6.
         destruct a.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         rewrite cpend_ann in H6. inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         apply refinementR_mon.
         easy.
         subst.
         rewrite <- mergeeq in H6.
         rewrite <- mergeeq4 in H6.
         apply merge_eqc in H6.
         inversion H6. subst.
         apply ssnssL in H0. easy. easy.
       }
       { apply IHHa.
         inversion H. subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1. simpl.
         
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_cp_contn p a (p & [(l, s', und)]) n0.+1)) in H6. simpl in H6.
         destruct a.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         rewrite cpend_ann in H6. inversion H6. subst.
         simpl.
         rewrite cpend_ann. rewrite cpend_an. easy.
         apply refinementR_mon.
         easy.
         subst.
         rewrite <- mergeeq2 in H6.
         rewrite <- mergeeq4 in H6.
         pose proof H6.
         apply merge_eqc in H6.
         rewrite <- mergeeq2 in H8.
         
         inversion H6. subst.
         apply merge_eq4c in H1.
         
         unfold upaco2 in H7.
         destruct H7.
         punfold H2. simpl.
         rewrite <- mergeeq4.
         rewrite <- mergeeq2 in H2.
         rewrite <- H1.
         easy.
         apply refinementR_mon.
         easy.
       }
       { inversion H.
         subst.
         specialize(case11 n p q a l l' s0 s' w'0 und H5); intros H11.
         easy.
       }
       { inversion H.
         subst. 

         apply case12_1c in H5.
         easy.
         subst.
         rewrite <- mergeeq2 in H5.
         rewrite <- mergeeq4 in H5.

         apply case12_2c in H5. easy. 
       }
       {
         inversion H.
         subst. easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq( merge_bp_contn p b (p ! [(l, s'0, w'0)]) n0.+1)) in H6.
         simpl in H6.
         case_eq b; intros.
         subst. easy.
         subst. inversion H6. subst. easy.
         subst. easy.
         subst. inversion H6. 
         subst. easy.
         subst. rewrite bpend_ann in H6. inversion H6. subst. easy.
       }
       { inversion H.
         subst. apply ssnssL in H0. easy.
         easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. apply ssnssL in H0. easy.
         apply ssnssR in H4. easy. easy.

         subst.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l, s'0, w'0)]) n0.+1)) in H6. simpl in H6.
         destruct b.
         easy.
         inversion H6. subst. easy.
         easy.
         inversion H6. subst. easy.
         rewrite bpend_ann in H6.
         inversion H6.
         subst.
         apply ssnssR in H4. easy. easy.
       }
       {
         apply IHHa.
         inversion H. subst.
         unfold upaco2 in H8.
         destruct H8.
         punfold H1.
         apply refinementR_mon.
         easy.
         subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.
         case_eq n; intros.
         subst. simpl in *.
         inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l, s'0, w'0)]) n0.+1)) in H6.
         simpl in H6.
         destruct b.
         easy.
         inversion H6. subst. simpl in H1. easy.
         easy.
         inversion H6. subst. easy.
         rewrite bpend_ann in H6.
         inversion H6. subst.
         rewrite bpend_ann in H1. easy.
         apply refinementR_mon.
         easy.
       }
       {
         inversion H.
         subst.

         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         induction n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l', s', und)]) n.+1)) in H6.
         simpl in H6.
         case_eq b; intros.
         subst. easy.
         subst. inversion H6. subst. easy.
         subst. easy.
         subst. inversion H6. 
         subst. easy.
         subst. rewrite bpend_ann in H6. inversion H6. subst. easy.
         apply refinementR_mon.
         easy.


         subst.
         rewrite <- mergeeq3 in H6.
         rewrite <- mergeeq3 in H6.
         apply merge_eq3 in H6.
         inversion H6. subst. easy.
       }
       { inversion H.
         subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         induction n; intros.
         subst. simpl in *. inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l, s', und)]) n.+1)) in H6. simpl in H6.
         destruct b.
         easy.
         inversion H6. subst. easy.
         easy.
         inversion H6. subst. easy.
         rewrite bpend_ann in H6. inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         apply refinementR_mon.
         easy.
         subst.
         rewrite <- mergeeq3 in H6.
         rewrite <- mergeeq3 in H6.
         apply merge_eq3 in H6.
         inversion H6. subst.
         apply ssnssL in H0. easy. easy.
       }
       { apply IHHa.
         inversion H. subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.
         simpl.
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l, s',und)]) n0.+1)) in H6. simpl in H6.
         destruct b.
         easy.
         inversion H6. subst. easy.
         easy.
         inversion H6. subst. easy.
         rewrite bpend_ann in H6. inversion H6. subst.
         simpl.
         rewrite bpend_ann. rewrite bpend_an. easy.
         apply refinementR_mon.
         easy.
         subst.
         rewrite <- mergeeq3 in H6.
         rewrite <- mergeeq3 in H6.
         pose proof H6.
         apply merge_eq3 in H6.
         rewrite <- mergeeq3 in H8.

         inversion H6. subst.
         apply merge_eq4 in H1.

         unfold upaco2 in H7.
         destruct H7.
         punfold H2. simpl.
         rewrite <- mergeeq3.
         rewrite <- mergeeq3 in H2.
         rewrite <- H1.
         easy.
         apply refinementR_mon.
         easy.
       }
Qed.

Lemma casen1c: forall p l s1 s2 w1 w2 P Q,
subsort s2 s1 ->
(nRefinementNc (mk_siso (st_receive p [(l, s1, (@und w1))]) P) 
              (mk_siso (st_receive p [(l, s2, (@und w2))]) Q) -> False) ->
(nRefinementNc w1 w2 -> False).
Proof. intros.
       apply H0.
       apply n_inp_wNc.
       easy.
       easy.
Qed.

Lemma casen2c: forall p l s1 s2 w1 w2 P Q,
subsort s1 s2 ->
(nRefinementNc (mk_siso (st_send p [(l, s1, (@und w1))]) P)
              (mk_siso (st_send p [(l, s2, (@und w2))]) Q) -> False) ->
(nRefinementNc w1 w2 -> False).
Proof. intros.
       apply H0.
       apply n_out_wNc.
       easy.
       easy.
Qed.

Lemma n_b_actNc: forall p l s s' w w' b P Q,
  subsort s s' ->
  (act_eq w (merge_bp_cont p b w') -> False) ->
  nRefinementNc (mk_siso (p ! [(l,s,w)]) P)
                (mk_siso (merge_bp_cont p b (p ! [(l,s',w')])) Q).
Admitted.

Lemma n_a_actNc: forall p l s s' w w' a P Q,
  subsort s' s ->
  (act_eq w (merge_ap_cont p a w') -> False) ->
  nRefinementNc (mk_siso (p & [(l,s,w)]) P)
                (mk_siso (merge_ap_cont p a (p & [(l,s',w')])) Q).
Admitted.

Lemma nrefNRSC: forall w w', (w //~< w' -> False) -> (@und w) ~< (@und w').
Proof. destruct w as (w, Pw).
       destruct w' as (w', Pw').
       intro H.
       generalize dependent w.
       generalize dependent w'.
       simpl. pcofix CIH.
       intros.
       specialize(sinv w Pw); intros Hpw.
       destruct Hpw as [Hpw | Hpw].
       destruct Hpw as (p, (l, (s, (w1, (Heq1, Hs1))))).
       { 
         specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         case_eq(eqb p q); intro Heq.
         rewrite eqb_eq in Heq.
         case_eq(eqb l l'); intro Heq2.
         rewrite eqb_eq in Heq2.
         specialize(sort_dec s s'); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         subst.
         pfold.
         apply _sref_out. easy.
         right.
         specialize (CIH w2 Hs2 w1 Hs1). apply CIH.
         simpl.
         specialize (casen2c q l' s s' ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} Pw Pw'); intros Hp.
         intros Hp2.
         apply Hp. easy. simpl. exact H0.
         exact Hp2.
         subst.
         specialize (n_out_sNc ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} q l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn. easy.
         subst.
         rewrite eqb_neq in Heq2.
         specialize (n_out_lNc ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} q l l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn. easy.
         rewrite eqb_neq in Heq.

         specialize(LEM (CoNInR (p, "!"%string) (act (q ! [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outNc {| und := w1; sprop := Hs1 |} {| und := q ! [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.

         unfold not in Hclass.
         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, "!"%string) (act (q ! [(l', s', w2)])) -> CoInR (p, "!"%string) (act (q ! [(l', s', w2)]))) as Hpr by admit.
         apply Hpr in Hclass.
         specialize(inSend (q ! [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (b,(l1,(s1,(w3,IHw3)))).
         rewrite IHw3.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s s1); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(LEM (act_eq w1 ((merge_bp_cont p b w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_b (upaco2 refinementR r) w1 w3 p l1 s s1 b 1 Heq3); intro Hrb.
         simpl in Hrb. 
         apply Hrb.

         assert(singleton w3) as Hs3.
         { revert Pw' H0.
           rewrite IHw3.
           intros Pw'' H0.
           specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw''); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         assert(singleton (merge_bp_cont p b w3)) as Pw''.
         { specialize(@extbp p b w3 Hs3); intros Hss. easy. }
         specialize(CIH (merge_bp_cont p b w3) Pw'' w1 Hs1).
         right.
         apply CIH.
         intro h.
         apply H0.
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.
         specialize(n_b_wNc (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         specialize(n_b_actNc p l1 s s1 w1 w3 b Pw Pw''); intros HN.
         apply HN. easy. easy.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw''); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_sNc (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw Pw'' Heq3); intros Hn.
         apply Hn.

         rewrite eqb_neq in Heq2.
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw''); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_lNc (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 b 1 Pw Pw''); intros Hn.
         apply Hn. easy.
         apply CoIn_mon.
         intros (u1,u2) (v1,v2).
         specialize (string_dec u1 v1); intro Hstr.
         destruct Hstr. subst.
         specialize (string_dec u2 v2); intro Hstr.
         destruct Hstr. subst.
         left. easy. 
         right. unfold not in *. intro Hss. apply n. inversion Hss. easy.
         right. unfold not in *. intro Hss. apply n. inversion Hss. easy.

         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.

(*****)

         specialize(LEM (CoNInR (p, "!"%string) (act (q & [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outNc {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.

         unfold not in Hclass.
         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, "!"%string) (act (q & [(l', s', w2)])) -> CoInR (p, "!"%string) (act (q & [(l', s', w2)]))) as Hpr by admit.
         apply Hpr in Hclass.
         specialize(inSend (q & [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (b,(l1,(s1,(w3,IHw3)))).
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s s1); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(LEM (act_eq w1 ((merge_bp_cont p b w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_b (upaco2 refinementR r) w1 w3 p l1 s s1 b 1 Heq3); intro Hrb.
         simpl in Hrb.
         apply Hrb.

         assert(singleton w3) as Hs3.
         { 
            specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss2.
            specialize (@extsR p l1 s1 w3 Hss2); intros Hss3. easy.
         }
         assert(singleton (merge_bp_cont p b w3)) as Pw''.
         { specialize(@extbp p b w3 Hs3); intros Hss. easy. }
         specialize(CIH (merge_bp_cont p b w3) Pw'' w1 Hs1).
         right.
         apply CIH.
         intro h.
         apply H0.

         specialize(n_b_wNc (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         destruct H0.
         specialize(n_b_actNc p l1 s s1 w1 w3 b Pw Pw'); intros HN.
         apply HN. easy. easy.

         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_sNc (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw Pw' Heq3); intros Hn.
         apply Hn.

         rewrite eqb_neq in Heq2.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_lNc (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 b 1 Pw Pw'); intros Hn.
         apply Hn. easy.
         apply CoIn_mon.
         intros (u1,u2) (v1,v2).
         specialize (string_dec u1 v1); intro Hstr.
         destruct Hstr. subst.
         specialize (string_dec u2 v2); intro Hstr.
         destruct Hstr. subst.
         left. easy. 
         right. unfold not in *. intro Hss. apply n. inversion Hss. easy.
         right. unfold not in *. intro Hss. apply n. inversion Hss. easy.

         subst.
         destruct H0.
         specialize(n_outNc {| und := w1; sprop := Hs1 |} {| und := end; sprop := Pw' |} p l s Pw); intro Hn.
         simpl in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor.
       }
       destruct Hpw as [Hpw | Hpw].
       destruct Hpw as (p, (l, (s, (w1, (Heq1, Hs1))))).
       { subst.
         specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         specialize(n_i_o_1Nc {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} p q l l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn.

         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         case_eq(eqb p q); intro Heq.
         rewrite eqb_eq in Heq.
         case_eq(eqb l l'); intro Heq2.
         rewrite eqb_eq in Heq2.
         specialize(sort_dec s' s); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         subst.
         pfold.
         apply _sref_in. easy.
         right. 
         apply (CIH w2 Hs2 w1 Hs1).
         intro Hs.
         specialize(casen1c q l' s s' {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} Pw Pw'); intro Hn.
         apply Hn. easy. exact H0. exact Hs.
         subst.
         destruct H0.
         specialize(n_inp_sNc {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} q l' s s' Pw Pw'); intro Hn.
         apply Hn. easy.
         subst.
         rewrite eqb_neq in Heq2.
         destruct H0.
         specialize(n_inp_lNc {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} q l l' s s' Pw Pw'); intro Hn.
         apply Hn. easy.
         rewrite eqb_neq in Heq.

         specialize(LEM (CoNInR (p, "?"%string) (act (q & [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_inpNc {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.

         unfold not in Hclass.
         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, "?"%string) (act (q & [(l', s', w2)])) -> CoInR (p, "?"%string) (act (q & [(l', s', w2)]))) as Hpr by admit.
         apply Hpr in Hclass.
         specialize(inReceive (q & [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (c,(l1,(s1,(w3,IHw3)))).
         rewrite IHw3.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.

         destruct H0.
         admit.
         apply CoIn_mon.
         admit.
         admit.
(*          specialize(n_inpNc {| und := w1; sprop := Hs1 |} {| und := end; sprop := Pw' |} p l s Pw); intro Hn.
         simpl in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor. *)
       }
       subst.
       { specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         destruct H0.
         specialize(n_out_rNc {| und := end; sprop := Pw |} {| und := w2; sprop := Hs2 |} q l' s' Pw'); intro Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.

         specialize(n_inp_rNc {| und := end; sprop := Pw |} {| und := w2; sprop := Hs2 |} q l' s' Pw'); intro Hn.
         destruct H0.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor.
         subst.
         pfold. constructor.
       }
Admitted.


