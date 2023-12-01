From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Inductive nRefinement: st -> st -> Prop :=
  | n_out  : forall w w' p l s, 
             CoNInR (p,"!"%string) (act w') -> nRefinement (st_send p [(l,s,w)]) w'
  | n_inp  : forall w w' p l s, 
             CoNInR (p,"?"%string) (act w') -> nRefinement (st_receive p [(l,s,w)]) w'
  | n_out_r: forall w w' p l s, 
             CoNInR (p,"!"%string) (act w) -> nRefinement w (st_send p [(l,s,w')])
  | n_inp_r: forall w w' p l s, 
             CoNInR (p,"?"%string) (act w) -> nRefinement w (st_receive p [(l,s,w')])
  | n_inp_l: forall w w' p l l' s s',
             l <> l' -> nRefinement (st_receive p [(l,s,w)]) (st_receive p [(l',s',w')])
  | n_inp_s: forall w w' p l s s',
             nsubsort s' s -> nRefinement (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])
  | n_inp_w: forall w w' p l s s',
             subsort s' s -> nRefinement w w' -> nRefinement (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])
  | n_a_l  : forall w w' p l l' s s' a n,
             l <> l' -> nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l',s',w')]) n)
  | n_a_s  : forall w w' p l s s' a n,
             nsubsort s' s -> 
             nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | n_a_w  : forall w w' p l s s' a n,
             subsort s' s ->
             nRefinement w (merge_ap_contn p a w' n) ->
             nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | n_i_o_1: forall w w' p q l l' s s', nRefinement (st_receive p [(l,s,w)]) (st_send q [(l',s',w')])
  | n_i_o_2: forall w w' p q l l' s s' (a: Ap p) n, nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_send q [(l',s',w')]) n)
  | n_out_l: forall w w' p l l' s s',
             l <> l' -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l',s',w')])
  | n_out_s: forall w w' p l s s',
             nsubsort s' s -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l,s',w')])
  | n_out_w: forall w w' p l s s',
             subsort s s' -> nRefinement w w' -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l,s',w')])
  | n_b_l  : forall w w' p l l' s s' b n,
             l <> l' -> nRefinement (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l',s',w')]) n)
  | n_b_s  : forall w w' p l s s' b n,
             nsubsort s s' -> 
             nRefinement (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | n_b_w  : forall w w' p l s s' b n,
             subsort s s' ->
             nRefinement w (merge_bp_contn p b w' n) ->
             nRefinement (st_receive p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n).

Notation "x '/~<' y" := (nRefinement x y) (at level 50, left associativity).


Lemma CoInIn: forall n w p l s b, CoInR (p, "!"%string) (act (merge_bp_contn p b (p ! [(l, s, w)]) n)).
Proof. intro n.
       induction n; intros.
       - simpl. rewrite(coseq_eq(act (p ! [(l, s, w)]))).
         unfold coseq_id. simpl.
         specialize(CoInSplit1 (p, "!"%string)
         (Delay(cocons (p, "!"%string) (act w)))
         (p, "!"%string) 
         (act w)
         ); intro Ha.
         apply Ha. simpl. easy. easy.
         induction b; intros.
         simpl.
         rewrite(coseq_eq((act (merge_bp_cont p (bp_receivea s0 s1 s2) (merge_bp_contn p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]) n))))).
         unfold coseq_id. simpl.
         specialize(CoInSplit2 (p, "!"%string)
         (Delay(cocons (s0, "?"%string) (act (merge_bp_contn p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]) n))))
         (s0, "?"%string)
         (act (merge_bp_contn p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]) n))
         ); intro Ha.
         apply Ha. simpl. easy. easy.
         apply IHn.
         rewrite(coseq_eq(act (merge_bp_cont p (bp_send q n0 s0 s1) (merge_bp_contn p (bp_send q n0 s0 s1) (p ! [(l, s, w)]) n)))).
         unfold coseq_id. simpl.
         specialize(CoInSplit2 (p, "!"%string)
         (Delay(cocons (q, "!"%string) (act (merge_bp_contn p (bp_send q n0 s0 s1) (p ! [(l, s, w)]) n))))
         (q, "!"%string)
         (act (merge_bp_contn p (bp_send q n0 s0 s1) (p ! [(l, s, w)]) n))
         ); intro Ha.
         apply Ha. simpl. easy. 
         unfold not in *.
         intro Hb. apply n0.
         inversion Hb. easy.
         apply IHn.
Admitted.

Lemma eq1a: forall n p q l l' s s' a w w',
  merge_ap_contn p a (p ! [(l,s,w)]) n = q ! [(l',s',w')] -> p = q.
Proof. intro n.
       induction n; intros.
       simpl in H. inversion H. easy.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_contn p (ap_receive q0 n0 s0 s1) (p ! [(l, s, w)]) n.+1)) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (p ! [(l, s, w)]) n.+1)) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_contn p ap_end (p ! [(l, s, w)]) n.+1)) in H.
       simpl in H. easy.
Qed.

Lemma mcomm: forall n p b w,
             merge_bp_contn p b (merge_bp_cont p b w) n =
             merge_bp_cont p b (merge_bp_contn p b w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma eq1b: forall n p b l s w,
CoInR (p, "!"%string) (act (merge_bp_contn p b (p ! [(l, s, w)]) n)).
Proof. intros n p b.
       induction n; intros.
       - simpl. admit.
       - simpl.
         induction b; intros.
         rewrite(coseq_eq((act (merge_bp_cont p (bp_receivea s0 s1 s2) (merge_bp_contn p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]) n))))).
         unfold coseq_id. simpl.
         admit.
         rewrite(coseq_eq(act (merge_bp_cont p (bp_send q n0 s0 s1) (merge_bp_contn p (bp_send q n0 s0 s1) (p ! [(l, s, w)]) n)))).
         unfold coseq_id. simpl.
         admit.
         rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s0 s1 s2 b) (merge_bp_contn p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]) n)))).
         unfold coseq_id. simpl.
         
         specialize(CoInSplit2 (p, "!"%string)
         (Delay(cocons (s0, "?"%string) (act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]) n)))))
         (s0, "?"%string) 
         (act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]) n)))
         ); intro Ha.
         apply Ha. simpl. easy. easy.

         rewrite(coseq_eq(act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]) n)))).
         unfold coseq_id. simpl.
         destruct b.
Admitted.

Lemma neq1a: forall n p q l l' s s' a w w',
  merge_ap_contn p a (p & [(l,s,w)]) n = q ! [(l',s',w')] -> False.
Proof. intro n.
       induction n; intros.
       simpl in H. inversion H.
       apply (IHn p q l l' s s' a w w').
       subst.
       induction a; intros.
       rewrite(siso_eq( merge_ap_contn p (ap_receive q0 n0 s0 s1) (p & [(l, s, w)]) n.+1)) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_ap_contn p (ap_merge q0 n0 s0 s1 a) (p & [(l, s, w)]) n.+1)) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_ap_contn p ap_end (p & [(l, s, w)]) n.+1)) in H.
       simpl in H. easy.
Qed.

Lemma nrefL: forall w w',  w ~< w' -> (w /~< w' -> False).
Proof. intros w w' H.
       unfold refinement in H.
       punfold H; [ | apply refinementR_mon].
       intro Ha.
       induction Ha; intros.
       { inversion H.
         subst.
         apply inOutL in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s', w'0)]))).
         specialize(CoInSplit1 (p, "!"%string)
         (Delay(cocons (p, "!"%string) (act w'0)))
         (p, "!"%string) 
         (act w'0)
         ); intro Hb.
         apply Hb. simpl. easy. easy.
         apply inOutL in H0. easy.
         rewrite <- H4.
         case_eq n; intros. simpl. admit.
         simpl.
         admit.
       }
       { inversion H.
         subst.
         apply inOutL in H0. easy.
         rewrite(coseq_eq(act (p & [(l, s', w'0)]))).
         specialize(CoInSplit1 (p, "?"%string)
         (Delay(cocons (p, "?"%string) (act w'0)))
         (p, "?"%string) 
         (act w'0)
         ); intro Hb.
         apply Hb. simpl. easy. easy.
         subst.
         apply inOutL in H0. easy.
         admit.
       }
       { inversion H.
         subst.
         apply inOutL in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s0, w0)]))).
         unfold coseq_id. simpl.
         specialize(CoInSplit1 (p, "!"%string)
         (Delay(cocons (p, "!"%string) (act w0)))
         (p, "!"%string) 
         (act w0)
         ); intro Hb.
         apply Hb. simpl. easy. easy.
         apply neq1a in H1. easy.
         
         
         apply inOutL in H0. easy.
         rewrite <- H4.
         
         unfold upaco2 in H3.
         destruct H3.
         punfold H3; [ | apply refinementR_mon].
         inversion H3.
         admit. 
         destruct b. try easy.
         admit.
         admit.
         admit.
         admit.
         admit.
         admit.
         admit.
         admit.
         admit.
       }
Admitted.
