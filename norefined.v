From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import ProofIrrelevance.

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
             nsubsort s s' -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l,s',w')])
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

Definition eqbp (a b: (participant*string)) :=
  andb (eqb a.1 b.1) (eqb a.2 b.2).

Lemma eq0: forall l (a: (participant*string)) xs, List.In a l \/ CoInR a xs ->
           CoInR a (appendL l xs).
Proof. intros l.
       induction l; intros.
       destruct H. easy.
       rewrite anl2. easy.
       destruct H.

       inversion H.
       subst.
       rewrite(coseq_eq(appendL (a0 :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       (Delay(cocons a0 (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       case_eq(eqbp a0 a); intros.
       unfold eqbp in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       (Delay(cocons a (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       rewrite eqb_eq in H2.
       inversion H1. inversion H2.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H1.
       rewrite Bool.andb_false_iff in H1.
       destruct H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       apply IHl. left. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       apply IHl. left. easy.

       case_eq(eqbp a0 a); intros.
       unfold eqbp in H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 a0
       (Delay(cocons a (appendL l xs)))
       a0
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       rewrite eqb_eq in H1.
       inversion H0. inversion H1.
       simpl in *. subst.
       easy. easy.

       unfold eqbp in H0.
       rewrite Bool.andb_false_iff in H0.
       destruct H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       apply IHl. right. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 a0
       (Delay(cocons a (appendL l xs)))
       a
       (appendL l xs)
       ); intro Ha.
       apply Ha. simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       apply IHl. right. easy.
Qed.

Lemma eq0A: forall l (a: (participant*string)) xs, List.In a l \/ CoInRA (upaco2 CoInRA bot2) a xs ->
             CoInRA (upaco2 CoInRA bot2) a (appendL l xs).
Proof. intros l.
       induction l; intros.
       destruct H. easy.
       rewrite anl2. easy.
       destruct H.

       inversion H.
       subst.
       rewrite(coseq_eq(appendL (a0 :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl. easy.

       case_eq(eqbp a0 a); intros.
       unfold eqbp in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       rewrite eqb_eq in H2.
       inversion H1. inversion H2.
       simpl in *. subst.
       easy.

       unfold eqbp in H1.
       rewrite Bool.andb_false_iff in H1.
       destruct H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       unfold upaco2. left. pfold.
       apply IHl. left. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       unfold upaco2. left. pfold.
       apply IHl. left. easy.

       case_eq(eqbp a0 a); intros.
       unfold eqbp in H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       rewrite eqb_eq in H1.
       inversion H0. inversion H1.
       simpl in *. subst.
       easy.

       unfold eqbp in H0.
       rewrite Bool.andb_false_iff in H0.
       destruct H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       unfold upaco2. left. pfold.
       apply IHl. right. easy.

       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (appendL l xs)). simpl. easy. 
       rewrite eqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       unfold upaco2. left. pfold.
       apply IHl. right. easy.
Qed.


Lemma eq1b: forall n p b l s w,
CoInR (p, "!"%string) (act (merge_bp_contn p b (p ! [(l, s, w)]) n)).
Proof. intros. rewrite h0.
       apply eq0.
       right.
       rewrite(coseq_eq(act (p ! [(l, s, w)]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 (p, "!"%string)
       (Delay(cocons (p, "!"%string) (act w)))
       (p, "!"%string)
       (act w)
       ); intro Ha.
       apply Ha. simpl. easy. easy.
Qed.


Lemma act_rec: forall n p b l s s0 s1 s2 w,
(act (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) (n.+1)))
=
Delay (cocons (s, "?"%string) (act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) n)))).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)])))).
       unfold coseq_id. simpl. easy.
       simpl.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) n))))).
       unfold coseq_id. simpl.
       simpl in IHn.
       easy.
Qed.

Lemma merge_eq2: forall p a1 a2 l s w,
merge_ap_cont p a1 (p & [(l, s, w)]) =
merge_ap_cont p a2 (p & [(l, s, w)]) ->
merge_ap_cont p a1 w =
merge_ap_cont p a2 w.
Proof. intros p a1.
       induction a1; intros.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq( merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a1; intros.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q n1 s s0 a) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl. destruct w; easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(proof_irrelevance _ n n0) ;intro Hp.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s2 s3 a1) w)).
       simpl.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q0 n0 s2 s3 a) w)).
       simpl.
       rewrite (IHa1 a l s1 w). easy. easy.
       case_eq a2; intros.
       subst. easy. subst. easy. subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s0 s1 a) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       easy.
Qed.

Lemma merge_eq: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [(l1, s1, w1)]) =
  merge_ap_cont p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.
       case_eq a; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q n1 s s0 a0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite apend_an in H. inversion H. subst. easy.
       subst. rewrite apend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (ap_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite apend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa a0 l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       destruct a2.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a2) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       easy.
Qed.


(* Lemma merge_eqG: forall p a1 a2 w1 w2,
  merge_ap_cont p a1 w1 =
  merge_ap_cont p a2 w2 -> w1 = w2. *)


Lemma case11: forall n p q a l l' s s' w w',
merge_ap_contn p a (p & [(l, s, w)]) n = q ! [(l', s', w')] -> False.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       subst.
       simpl in H.
(*        case_eq(eqb p q); intros.
       rewrite eqb_eq in H0.
       subst. *)
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1)
      (merge_ap_contn p (ap_receive q0 n0 s0 s1) (p & [(l, s, w)]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0)
      (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (p & [(l, s, w)]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite apend_ann in H.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l, s, w)]))) in H.
       simpl in H. easy.
Qed.

Lemma case12_1: forall n p q a l l' s s' w w',
p & [(l, s, w)] = merge_ap_contn p a (q ! [(l', s', w')]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s0 s1) (merge_ap_contn p (ap_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s0 s1 a0) (merge_ap_contn p (ap_merge q0 n0 s0 s1 a0) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite apend_ann in H.
       rewrite apend_an in H. easy.
Qed.

Lemma case12_2: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_ap_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n1 s s0 a0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite apend_an in H4. easy.
       subst. rewrite apend_an in H.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]) )) in H.
       simpl in H.
       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(siso_eq( merge_ap_cont p (ap_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (ap_end) l l' s1 s' w w').
       apply IHa1.
       rewrite apend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q1 n0 s2 s3 a) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 a l l' s1 s' w w').
       apply IHa1. easy.
       subst. rewrite apend_an in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s0 s1 a) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite apend_an in H. easy.
Qed.

Lemma nrefL: forall w w',  w ~< w' -> (w /~< w' -> False).
Proof. intros w w' H.
       unfold refinement in H.
       punfold H; [ | apply refinementR_mon].
       intro Ha.
       induction Ha; intros.
       {
         inversion H.
         subst.
         apply inOutLA in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w'0)). easy.
         apply inOutLA in H0. easy.
         rewrite <- H4.
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
         apply inOutLA in H0. easy.
         rewrite(coseq_eq(act (p & [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w'0)). easy.
         subst.
         apply inOutLA in H0. easy.
         simpl.
         pfold.
         rewrite h1.
         apply eq0A.
         right.
         rewrite(coseq_eq(act (p & [(l, s0, w'0)]))). unfold coseq_id. simpl.
         apply CoInSplit1A with (ys := (act w'0)). simpl. easy.
       }
       { inversion H.
         subst.
         apply inOutLA in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s0, w0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w0)). easy.

         unfold act_eq in H5.
         rewrite <- H4 in H0.
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
         simpl in *. subst. inversion H1. 

         case_eq a; intros.
         subst.
         simpl in H1.
         rewrite(siso_eq(merge_ap_cont p0 (ap_receive q n1 s1 s2)
                        (merge_ap_contn p0 (ap_receive q n1 s1 s2) (p0 & [(l0, s0, w'0)]) n0))) in H1.
         simpl in H1.
         easy.

         subst.
         simpl in H1.
         rewrite(siso_eq(merge_ap_cont p0 (ap_merge q n1 s1 s2 a0) (merge_ap_contn p0 (ap_merge q n1 s1 s2 a0) 
          (p0 & [(l0, s0, w'0)]) n0) )) in H1.
         simpl in H1.
         inversion H1.
         subst.
         rewrite h1.
         apply eq0A.
         subst.
         rewrite apend_ann in H1. easy.

        (* subst.
         rewrite apend_ann in H1.
         inversion H1.  *)
         (*middle*)
         unfold act_eq in H5.
         rewrite <- H4 in H0.
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
         simpl in *. subst. inversion H1. subst. easy.
         rewrite h0.
         apply eq0A.
         subst.

         case_eq b; intros.
         subst.
         simpl in H1.
         rewrite(siso_eq(merge_bp_cont p0 (bp_receivea s1 s2 s3) (merge_bp_contn p0 (bp_receivea s1 s2 s3) (p0 ! [(l0, s', w'0)]) n0))) in H1.
         simpl in H1.
         easy.

         subst.
         simpl in H1.
         rewrite(siso_eq(merge_bp_cont p0 (bp_send q n s1 s2) (merge_bp_contn p0 (bp_send q n s1 s2) (p0 ! [(l0, s', w'0)]) n0))) in H1.
         simpl in H1.
         inversion H1.
         subst.
         clear H1.
         left. simpl. left. easy.

         subst.
         simpl in H1.
         rewrite(siso_eq(merge_bp_cont p0 (bp_mergea s1 s2 s3 b0) (merge_bp_contn p0 (bp_mergea s1 s2 s3 b0) (p0 ! [(l0, s', w'0)]) n0))) in H1.
         simpl in H1.
         easy.

         subst.
         simpl in H1.
         rewrite(siso_eq(merge_bp_cont p0 (bp_merge q n s1 s2 b0) (merge_bp_contn p0 (bp_merge q n s1 s2 b0) (p0 ! [(l0, s', w'0)]) n0))) in H1.
         simpl in H1.
         inversion H1.
         left. simpl. subst. left. easy.

         subst.
         rewrite bpend_ann in H1.
         inversion H1. subst. easy.
       }
       { inversion H.
         subst.
         apply inOutLA in H0. easy.
         rewrite(coseq_eq(act (p & [(l, s0, w0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w0)). easy.

         unfold act_eq in H5.
         rewrite <- H4 in H0.
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
         simpl in *. subst. inversion H1. subst. easy.
         rewrite h1.
         apply eq0A.
         subst.

         case_eq a; intros.
         subst.
         simpl in H1.
         rewrite(siso_eq(merge_ap_cont p0 (ap_receive q n s1 s2)
       (merge_ap_contn p0 (ap_receive q n s1 s2) (p0 & [(l0, s0, w'0)]) n0) )) in H1.
         simpl in H1.
         inversion H1.
         subst.
         left. simpl. left. easy.

         subst.
         simpl in H1.
         rewrite(siso_eq(merge_ap_cont p0 (ap_merge q n s1 s2 a0)
       (merge_ap_contn p0 (ap_merge q n s1 s2 a0) (p0 & [(l0, s0, w'0)]) n0))) in H1.
         simpl in H1.
         simpl. inversion H1. subst. left. left. easy.

         subst.
         rewrite apend_ann in H1.
         inversion H1. subst. easy.

         apply inOutLA in H0. easy.
         rewrite <- H4.
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
         subst. simpl in *. inversion H1.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_receivea s1 s2 s3) (p0 ! [(l0, s', w'0)]) n0.+1)) in H1.
         simpl in H1. inversion H1.
         subst.
         rewrite(coseq_eq( (act (merge_bp_contn p0 (bp_receivea p l s) w'0 n0.+1)))). unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act (merge_bp_contn p0 (bp_receivea p l s) w'0 n0))). simpl. easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. inversion H1.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_send q n0 s1 s2) (p0 ! [(l0, s', w'0)]) n1.+1)) in H1. simpl in H1. easy.
         subst.
         case_eq n; intros.
         subst. simpl in *. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_mergea s1 s2 s3 b0) (p0 ! [(l0, s', w'0)]) n0.+1)) in H1.
         simpl in H1.  inversion H1. subst.
         rewrite h0.
         pfold.
         apply eq0A.
         simpl. left. left. easy.
         case_eq n; intros.
         subst. simpl in *. inversion H1.
         subst.
         rewrite(siso_eq(merge_bp_contn p0 (bp_merge q n0 s1 s2 b0) (p0 ! [(l0, s', w'0)]) n1.+1)) in H1.
         simpl in H1. easy.
         subst.
         rewrite bpend_ann in H1.
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
         rewrite(siso_eq( merge_ap_contn p a (p & [(l', s', w')]) n.+1)) in H6.
         case_eq a; intros.
         subst. inversion H6. subst. easy.
         subst. inversion H6. 
         subst. easy.
         subst. rewrite apend_ann in H6. inversion H6. subst. easy.
         apply refinementR_mon.
         easy.


         subst.
         rewrite <- mergeeq in H6.
         rewrite <- mergeeq in H6.
         apply merge_eq in H6.
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
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s', w')]) n.+1)) in H6. simpl in H6.
         destruct a.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         rewrite apend_ann in H6. inversion H6. subst.
         apply ssnssL in H0. easy. easy.
         apply refinementR_mon.
         easy.
         subst.
         rewrite <- mergeeq in H6.
         rewrite <- mergeeq in H6.
         apply merge_eq in H6.
         inversion H6. subst.
         apply ssnssL in H0. easy. easy.
       }
       { apply IHHa.
         inversion H. subst.
         unfold upaco2 in H7.
         destruct H7.
         punfold H1.
         
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s', w')]) n0.+1)) in H6. simpl in H6.
         destruct a.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         rewrite apend_ann in H6. inversion H6. subst.
         simpl.
         rewrite apend_ann.
         rewrite(siso_eq(merge_ap_cont p ap_end w')). simpl.
         destruct w'; easy.
         apply refinementR_mon.
         easy.
         subst.
         rewrite <- mergeeq2 in H6.
         rewrite <- mergeeq2 in H6.
         pose proof H6.
         apply merge_eq in H6.
         rewrite <- mergeeq2 in H8.
         
         inversion H6. subst.
         apply merge_eq2 in H1.
         
         unfold upaco2 in H7.
         destruct H7.
         punfold H2.
         rewrite <- mergeeq2.
         rewrite <- mergeeq2 in H2.
         rewrite <- H1.
         easy.
         apply refinementR_mon.
         easy.
       }
       { inversion H.
         subst.
         specialize(case11 n p q a l l' s0 s' w'0 w' H5); intros H11.
         easy.
       }
       { inversion H.
         subst. 
         apply case12_1 in H5.
         easy.
         subst.
         rewrite <- mergeeq2 in H5.
         rewrite <- mergeeq2 in H5.
         apply case12_2 in H5. easy.
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
Admitted.
