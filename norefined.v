From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import ProofIrrelevance.

Lemma exts: forall {p l s} w, singleton w -> singleton (st_send p [(l,s,w)]).
Proof. intros.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Qed.

Lemma extsR: forall {p l s} w, singleton (st_send p [(l,s,w)]) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.

Lemma extr: forall {p l s} w, singleton w -> singleton (st_receive p [(l,s,w)]).
Proof. intros.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Qed.

Lemma extrR: forall {p l s} w, singleton (st_receive p [(l,s,w)]) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.

Lemma extap: forall {p a} w, singleton w -> singleton ((merge_ap_cont p a w)).
Proof. induction a; intros.
       rewrite(siso_eq((merge_ap_cont p (ap_receive q n s s0) w))).
       simpl. apply extr. easy.
       rewrite(siso_eq((merge_ap_cont p (ap_merge q n s s0 a) w))).
       simpl. pfold. constructor. unfold singleton in IHa, H.
       left.
       apply IHa. easy.
       rewrite apend_an.
       easy.
Qed.

Lemma extapR: forall {p a} w, singleton ((merge_ap_cont p a w)) -> singleton w.
Proof. intros p a.
       induction a; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) w)) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) w)) in H.
       simpl in H.
       apply IHa. apply extrR in H. easy.
       rewrite apend_an in H. easy.
Qed.

Lemma extapnR: forall {n p a} w, singleton ((merge_ap_contn p a w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       apply extapR in H.
       apply (IHn p a). easy.
Qed.

Lemma extapn: forall {n p a} w, singleton w -> singleton ((merge_ap_contn p a w n)).
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply extap.
       apply IHn. easy.
Qed.

Lemma extbp: forall {p b} w, singleton w -> singleton ((merge_bp_cont p b w)).
Proof. induction b; intros.
       rewrite(siso_eq((merge_bp_cont p (bp_receivea s s0 s1) w))).
       simpl. apply extr. easy.
       rewrite(siso_eq((merge_bp_cont p (bp_send q n s s0) w))).
       simpl. pfold. constructor. unfold singleton in H.
       left. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) w)).
       simpl. pfold. constructor. left. 
       unfold singleton in IHb, H.
       apply IHb. easy.
       rewrite(siso_eq((merge_bp_cont p (bp_merge q n s s0 b) w))).
       simpl. pfold. constructor.
       unfold singleton in IHb, H. left.
       apply IHb. easy.
       rewrite bpend_an.
       easy.
Qed.

Lemma extbpR: forall {p b} w, singleton ((merge_bp_cont p b w)) -> singleton w.
Proof. intros p b.
       induction b; intros.
       rewrite(siso_eq((merge_bp_cont p (bp_receivea s s0 s1) w))) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) w)) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) w)) in H.
       simpl in H. apply extrR in H. apply IHb. easy.
       rewrite(siso_eq((merge_bp_cont p (bp_merge q n s s0 b) w))) in H.
       simpl in H.  apply extsR in H. apply IHb. easy.
       rewrite bpend_an in H. easy. 
Qed.

Lemma extbpn: forall {n p b} w, singleton w -> singleton ((merge_bp_contn p b w n)).
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply extbp.
       apply IHn. easy.
Qed.

Lemma extbpnR: forall {n p b} w, singleton ((merge_bp_contn p b w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       apply extbpR in H.
       apply (IHn p b). easy.
Qed.

Lemma extbpns: forall {n p l s b} w, singleton w -> singleton ((merge_bp_contn p b (st_send p [(l,s,w)]) n)).
Proof. intros.
       apply extbpn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extbpnr: forall {n p l s b} w, singleton w -> singleton ((merge_bp_contn p b (st_receive p [(l,s,w)]) n)).
Proof. intros.
       apply extbpn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapns: forall {n p l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_send p [(l,s,w)]) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapnr: forall {n p l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_receive p [(l,s,w)]) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.

Lemma extapnspq: forall {n p q l s a} w, singleton w -> singleton ((merge_ap_contn p a (st_send q [(l,s,w)]) n)).
Proof. intros.
       apply extapn.
       pfold. constructor.
       unfold singleton in H. left. easy.
Qed.


Inductive nRefinementN: siso -> siso -> Prop :=
  | n_outN  : forall w w' p l s P, 
              CoNInR (p,"!"%string) (act (@und w')) -> 
              nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) w'
  | n_inpN  : forall w w' p l s P, 
              CoNInR (p,"?"%string) (act (@und w')) -> 
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) w'
  | n_out_rN: forall w w' p l s P, 
              CoNInR (p,"!"%string) (act (@und w)) -> 
              nRefinementN w (mk_siso (st_send p [(l,s,(@und w'))]) P)
  | n_inp_rN: forall w w' p l s P,
              CoNInR (p,"?"%string) (act (@und w)) -> 
              nRefinementN w (mk_siso (st_receive p [(l,s,(@und w'))]) P)
  | n_inp_lN: forall w w' p l l' s s' P Q,
             l <> l' -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                     (mk_siso (st_receive p [(l',s',(@und w'))]) Q)
  | n_inp_sN: forall w w' p l s s' P Q,
              nsubsort s' s -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P)
                                            (mk_siso (st_receive p [(l,s',(@und w'))]) Q)
  | n_inp_wN: forall w w' p l s s' P Q,
              subsort s' s -> nRefinementN w w' -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                                (mk_siso (st_receive p [(l,s',(@und w'))]) Q)
  | n_a_lN  : forall w w' p l l' s s' a n P Q,
              l <> l' -> nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                      (mk_siso (merge_ap_contn p a (st_receive p [(l',s',(@und w'))]) n) Q)
  | n_a_sN  : forall w w' p l s s' a n P Q,
              nsubsort s' s -> 
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                           (mk_siso (merge_ap_contn p a (st_receive p [(l,s',(@und w'))]) n) Q)
  | n_a_wN  : forall w w' p l s s' a n P Q R,
              subsort s' s ->
              nRefinementN w (mk_siso (merge_ap_contn p a (@und w') n) P) ->
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) Q) 
                           (mk_siso (merge_ap_contn p a (st_receive p [(l,s',(@und w'))]) n) R)
  | n_i_o_1N: forall w w' p q l l' s s' P Q, nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                          (mk_siso (st_send q [(l',s',(@und w'))]) Q)
  | n_i_o_2N: forall w w' p q l l' s s' (a: Ap p) n P Q, nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                                  (mk_siso (merge_ap_contn p a (st_send q [(l',s',(@und w'))]) n) Q)
  | n_out_lN: forall w w' p l l' s s' P Q,
              l <> l' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                      (mk_siso (st_send p [(l',s',(@und w'))]) Q)
  | n_out_sN: forall w w' p l s s' P Q,
              nsubsort s s' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                            (mk_siso (st_send p [(l,s',(@und w'))]) Q)
  | n_out_wN: forall w w' p l s s' P Q,
              subsort s s' -> nRefinementN w w' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                                                (mk_siso (st_send p [(l,s',(@und w'))]) Q)
  | n_b_lN  : forall w w' p l l' s s' b n P Q,
              l <> l' -> nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                                      (mk_siso (merge_bp_contn p b (st_send p [(l',s',(@und w'))]) n) Q)
  | n_b_sN  : forall w w' p l s s' b n P Q,
              nsubsort s s' -> 
              nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) 
                           (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) Q)
  | n_b_wN  : forall w w' p l s s' b n P Q R,
              subsort s s' ->
              nRefinementN w (mk_siso (merge_bp_contn p b (@und w') n) P) ->
              nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) Q) 
                           (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) R).

(* Inductive nRefinement: siso -> siso -> Prop :=
  | n_out  : forall w w' p l s, 
             CoNInR (p,"!"%string) (act (@und w')) -> 
             nRefinement (mk_siso (st_send p [(l,s,(@und w))]) (sisoext (@und w) (@sprop w))) w'. *)

Inductive nRefinement: st -> st -> Prop :=
  | n_out  : forall w w' p l s, 
             CoNInR (p,"!"%string) (act w') -> 
             nRefinement (st_send p [(l,s,w)]) w'
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
             nRefinement (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n).
(*   | n_new1 :  forall w w' p q l s, p <> q -> CoIn (p,"!"%string) (act w') -> nRefinement (st_send p [(l,s,w)]) (st_send q [(l,s,w')]). *)
(*   | n_i_o_2R: forall w w' p q l l' s s' (a: Ap p) n, nRefinement (merge_ap_contn p a (st_send q [(l',s',w')]) n) (st_receive p [(l,s,w)]). *)
(*   | n_i_o_1R: forall w w' p q l l' s s', nRefinement (st_send p [(l,s,w)]) (st_receive q [(l',s',w')]). *)

Notation "x '/~<' y" := (nRefinement x y) (at level 50, left associativity).


(* Inductive nRefinementA: siso -> siso -> Prop :=
  | n_outA  : forall w w' p l s, 
              CoNInR (p,"!"%string) (actC w') -> nRefinementA (siso_send p (l,s,w)) w'
  | n_inpA  : forall w w' p l s, 
              CoNInR (p,"?"%string) (actC w') -> nRefinementA (siso_receive p (l,s,w)) w'
  | n_out_rA: forall w w' p l s, 
              CoNInR (p,"!"%string) (actC w) -> nRefinementA w (siso_send p (l,s,w'))
  | n_inp_rA: forall w w' p l s, 
              CoNInR (p,"?"%string) (actC w) -> nRefinementA w (siso_receive p (l,s,w'))
  | n_inp_lA: forall w w' p l l' s s',
              l <> l' -> nRefinementA (siso_receive p (l,s,w)) (siso_receive p (l',s',w'))
  | n_inp_sA: forall w w' p l s s',
              nsubsort s' s -> nRefinementA (siso_receive p (l,s,w)) (siso_receive p (l,s',w'))
  | n_inp_wA: forall w w' p l s s',
              subsort s' s -> nRefinementA w w' -> nRefinementA (siso_receive p (l,s,w)) (siso_receive p (l,s',w'))
  | n_a_lA  : forall w w' p l l' s s' a n,
              l <> l' -> nRefinementA (siso_receive p (l,s,w)) (merge_ap_contnB p a (siso_receive p (l',s',w')) n)
  | n_a_sA  : forall w w' p l s s' a n,
              nsubsort s' s -> 
              nRefinementA (siso_receive p (l,s,w)) (merge_ap_contnB p a (siso_receive p (l,s',w')) n)
  | n_a_wA  : forall w w' p l s s' a n,
              subsort s' s ->
              nRefinementA w (merge_ap_contnB p a w' n) ->
              nRefinementA (siso_receive p (l,s,w)) (merge_ap_contnB p a (siso_receive p (l,s',w')) n)
  | n_i_o_1A: forall w w' p q l l' s s', nRefinementA (siso_receive p (l,s,w)) (siso_send q (l',s',w'))
  | n_i_o_2A: forall w w' p q l l' s s' (a: Ap p) n, nRefinementA (siso_receive p (l,s,w)) (merge_ap_contnB p a (siso_send q (l',s',w')) n)
  | n_out_lA: forall w w' p l l' s s',
              l <> l' -> nRefinementA (siso_send p (l,s,w)) (siso_send p (l',s',w'))
  | n_out_sA: forall w w' p l s s',
              nsubsort s s' -> nRefinementA (siso_send p (l,s,w)) (siso_send p (l,s',w'))
  | n_out_wA: forall w w' p l s s',
              subsort s s' -> nRefinementA w w' -> nRefinementA (siso_send p (l,s,w)) (siso_send p (l,s',w'))
  | n_b_lA  : forall w w' p l l' s s' b n,
              l <> l' -> nRefinementA (siso_send p (l,s,w)) (merge_bp_contnB p b (siso_send p (l',s',w')) n)
  | n_b_sA  : forall w w' p l s s' b n,
              nsubsort s s' -> 
              nRefinementA (siso_send p (l,s,w)) (merge_bp_contnB p b (siso_send p (l,s',w')) n)
  | n_b_wA  : forall w w' p l s s' b n,
              subsort s s' ->
              nRefinementA w (merge_bp_contnB p b w' n) ->
              nRefinementA (siso_send p (l,s,w)) (merge_bp_contnB p b (siso_send p (l,s',w')) n). *)

(* Notation "x '/~<A' y" := (nRefinementA x y) (at level 50, left associativity). *)


(* Lemma convref: forall w w', nRefinement w w' -> nRefinementA w w'. *)


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

Lemma merge_eq4: forall p b1 b2 l s w,
merge_bp_cont p b1 (p ! [(l, s, w)]) =
merge_bp_cont p b2 (p ! [(l, s, w)]) ->
merge_bp_cont p b1 w =
merge_bp_cont p b2 w.
Proof. intros p b1.
       induction b1; intros.
       case_eq b2; intros. subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l, s2, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [(l, s2, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 bp_end) w)).
       simpl.
       rewrite bpend_an. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H.
       rewrite(siso_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       inversion H.
       subst.
       specialize(proof_irrelevance _ n n0); intro Hp.
       subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n s2 s3) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)).
       simpl.
       case_eq b; intros.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s4) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n1 s s0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s4 b0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b1) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l, s2, w)]))) in H.
       simpl in H.
       inversion H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) w)).
       simpl. subst.
       specialize(IHb1 (bp_end) l s2 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s3 s4) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s2 w).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b1) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) w)).
       simpl.
       rewrite IHb1. easy. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s3 s4 b) (p ! [(l, s2, w)]))) in H.
       simpl in H. easy.
       subst. rewrite bpend_an in H. easy.

       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) w)).
       simpl.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b1) (p ! [(l, s1, w)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s2 s3 s4) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s2 s3) (p ! [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq( merge_bp_cont p (bp_send q0 n0 s2 s3) w)).
       simpl.
       specialize(IHb1 (bp_end) l s1 w).
       rewrite IHb1. rewrite bpend_an. easy.
       rewrite bpend_an. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s2 s3 s4 b) (p ! [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) (p ! [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       specialize(IHb1 b l s1 w).
       rewrite IHb1. 
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s2 s3 b) w)). simpl.
       easy.
       easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s0 s1 s2) (p ! [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s0 s1) (p ! [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s0 s1 s2 b) (p ! [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s0 s1 b) (p ! [(l, s, w)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite bpend_an. easy.
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
       specialize(proof_irrelevance _ n n0); intro Hp.
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

Lemma merge_eqc: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont p a1 (p & [(l1, s1, w1)]) =
  merge_cp_cont p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s5) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       
       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.
       inversion H. subst. easy.
       
       rewrite apend_an in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s3) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       easy.
Qed.

Lemma merge_eqc2: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_cp_cont p a1 (p & [(l1, s1, w1)]) =
  merge_cp_cont p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.

       case_eq c; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. inversion H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s5) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s5 c0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       
       subst. rewrite cpend_an in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa c l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_send s3 s4 s5) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite cpend_an in H.
       specialize(IHa (cp_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite cpend_an. 
       destruct a.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s3 s4 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_send s3 s4 s5) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s3 s4 s5 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       inversion H. subst. easy.

       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst. easy.

       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.

       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c0) (p & [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4.
       subst.
       rewrite cpend_an in H4. easy.
       subst.
       rewrite cpend_an in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l1, s2, w1)]))) in H.
       simpl in H. easy.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 a) (p & [(l1, s2, w1)]))) in H.
       simpl in H.

       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s4 s5) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s4 s5 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s4 s5 s6) (p & [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H. subst. rewrite H4.

       specialize (IHa (cp_end) l1 l2 s2 s3 w1 w2).
       apply IHa.
       rewrite cpend_an. easy.
       
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s4 s5 s6 c) (p & [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa c l1 l2 s2 s3 w1 w2).
       apply IHa. easy.

       subst.
       rewrite cpend_an in H. easy.
       rewrite cpend_an in H.
       
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s3) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s3 c) (p & [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst. rewrite cpend_an in H. easy.
Qed.

Lemma merge_eq3: forall p b1 b2 l1 l2 s1 s2 w1 w2,
  merge_bp_cont p b1 (p ! [(l1, s1, w1)]) =
  merge_bp_cont p b2 (p ! [(l2, s2, w2)]) -> (p ! [(l1, s1, w1)]) = (p ! [(l2, s2, w2)]).
Proof. intros p b.
       induction b; intros.
       simpl.
       case_eq b2; intros.
       simpl.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(siso_eq( merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. 
       subst.
       rewrite(siso_eq( merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b0) (p ! [(l2, s3, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite bpend_an in H4. easy.
       
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq( merge_bp_cont p (bp_merge q n s4 s5 b) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (p ! [(l1, s2, w1)]))) in H.
       rewrite bpend_an in H. simpl in H. easy.

       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst.
       case_eq b; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s5) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq( merge_bp_cont p (bp_send q n1 s s0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. inversion H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s5 b0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n1 s s0 b0) (p ! [(l2, s2, w2)]))) in H4.
       simpl in H4.  inversion H4. easy.
       subst. rewrite bpend_an in H4. easy.
       
       subst. rewrite bpend_an in H.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l1, s1, w1)]) )) in H.
       simpl in H. inversion H. subst. easy.
       
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (p ! [(l1, s2, w1)]))) in H.
       simpl in H. inversion H.
       
       case_eq b2; intros.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s4 s5 s6) (p ! [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H.
       rewrite H5.
       specialize(IHb (bp_end) l1 l2 s2 s3 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s4 s5) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s4 s5 s6 b0) (p ! [(l2, s3, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHb b0 l1 l2 s2 s3 w1 w2).
       apply IHb. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s4 s5 b0) (p ! [(l2, s3, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite bpend_an in H. easy.
       
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s3 s4 s5) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q0 n0 s3 s4) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. rewrite H4.
       specialize(IHb (bp_end) l1 l2 s1 s2 w1 w2).
       apply IHb. rewrite bpend_an. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s3 s4 s5 b0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q0 n0 s3 s4 b0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H.
       specialize(IHb b0 l1 l2 s1 s2 w1 w2).
       apply IHb. easy.
       subst. rewrite bpend_an in H. inversion H. subst. easy.
       
       rewrite bpend_an in H.
       case_eq b2; intros.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s3) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. 
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s3 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (p ! [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite bpend_an in H. easy.
Qed.

Lemma case11: forall n p q a l l' s s' w w',
merge_ap_contn p a (p & [(l, s, w)]) n = q ! [(l', s', w')] -> False.
Proof. intros n.
       induction n; intros.
       simpl in H. easy.
       subst.
       simpl in H.

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

Lemma nrefLS: forall w w',  w ~< w' -> (w /~< w' -> False).
Proof. intros w w' H.
       unfold refinement in H.
       punfold H; [ | apply refinementR_mon].
       intro Ha.
       induction Ha; intros.
       {
         inversion H.
         subst.
(*          destruct H0 as (H0, (hl1,hl2)). *)
         apply inOutLA in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w'0)). easy.
(*          destruct H0 as (H0, (hl1,hl2)). *)
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
(*          destruct H0 as (H0, (hl1,hl2)). *)
         apply inOutLA in H0. easy.
         rewrite(coseq_eq(act (p & [(l, s', w'0)]))).
         unfold coseq_id. simpl.
         pfold.
         apply CoInSplit1A with (ys := (act w'0)). easy.
         subst.
(*          destruct H0 as (H0, (hl1,hl2)). *)
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
       {
         inversion H.
         subst.

         unfold upaco2 in H7.
         destruct H7.
         punfold H1.

         induction n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l', s', w')]) n.+1)) in H6.
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
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l, s', w')]) n.+1)) in H6. simpl in H6.
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
         
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_bp_contn p b (p ! [(l, s', w')]) n0.+1)) in H6. simpl in H6.
         destruct b.
         easy.
         inversion H6. subst. easy.
         easy.
         inversion H6. subst. easy.
         rewrite bpend_ann in H6. inversion H6. subst.
         simpl.
         rewrite bpend_ann.
         rewrite(siso_eq(merge_bp_cont p bp_end w')). simpl.
         destruct w'; easy.
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
         punfold H2.
         rewrite <- mergeeq3.
         rewrite <- mergeeq3 in H2.
         rewrite <- H1.
         easy.
         apply refinementR_mon.
         easy.
       }
Qed.

Lemma nrefL: forall w w', w /~< w' -> (w ~< w' -> False).
Proof. intros.
       apply (nrefLS w w'); easy.
Qed.

Lemma nrefNLS: forall w w',  (@und w) ~< (@und w') -> (nRefinementN w w' -> False).
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
         rewrite(siso_eq( merge_ap_contn p a (p & [(l', s', und)]) n.+1)) in H6.
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
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s',und)]) n.+1)) in H6. simpl in H6.
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
         punfold H1. simpl.
         
         case_eq n; intros.
         subst. simpl in *. inversion H6. subst. easy.
         subst.
         rewrite(siso_eq(merge_ap_contn p a (p & [(l, s', und)]) n0.+1)) in H6. simpl in H6.
         destruct a.
         inversion H6. subst. easy.
         inversion H6. subst. easy.
         rewrite apend_ann in H6. inversion H6. subst.
         simpl.
         rewrite apend_ann. rewrite apend_an. easy.
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
         punfold H2. simpl.
         rewrite <- mergeeq2.
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

Axiom LEM: forall (p: Prop), p \/ ~p.

Lemma nrefLSV: forall w w',  (w ~< w' /\ w /~< w') -> False.
Proof. intros.
       specialize (nrefLS w w'); intro Hs.
       apply Hs. easy. easy.
Qed.

(* Lemma nrefLSNeg: forall w w',  (w ~< w' -> False) -> (w /~< w' -> False) -> False.
Proof. intros w w' Ha Hb. *)

Lemma invsingl: forall p l, singleton (p & l) -> exists (l': label) (s: st.sort) (w: st), l = [((l',s),w)].
Proof. intros.
       induction l; intros.
       unfold singleton in H. punfold H. inversion H. 
       apply sI_mon.
       unfold singleton in H. punfold H. inversion H.
       subst. simpl in *.
       exists l0. exists s. exists w. easy. 
       apply sI_mon.
Qed.

Lemma invsingl2: forall p l, singleton (p ! l) -> exists (l': label) (s: st.sort) (w: st), l = [((l',s),w)].
Proof. intros.
       induction l; intros.
       unfold singleton in H. punfold H. inversion H. 
       apply sI_mon.
       unfold singleton in H. punfold H. inversion H.
       subst. simpl in *.
       exists l0. exists s. exists w. easy. 
       apply sI_mon.
Qed.

Lemma sinv4: forall n w p, singleton w -> (exists a, (w = merge_ap_contn p a w n)).
Proof. intros.
       case_eq w; intros.
       subst.
       case_eq n; intros.
       subst.
       (*  exists "p"%string. *) exists(ap_end).
       simpl. easy.
       subst. simpl.
       exists(ap_end).
       simpl.
       rewrite apend_an.
       rewrite apend_ann.
       easy.
       
       rewrite H0 in H.
       specialize(invsingl s l H); intro HH.
       destruct HH as (l1,(s1,(w1,HH))).
       subst.
       exists (ap_end).
       rewrite apend_ann. easy.
       
       rewrite H0 in H.
       specialize(invsingl2 s l H); intro HH.
       destruct HH as (l1,(s1,(w1,HH))).
       subst.
       exists (ap_end).
       rewrite apend_ann. easy.
Qed.

Lemma sinv3: forall w p, singleton w ->
                       (exists n a, (w = merge_ap_contn p a w n)) \/
                       (exists n b, (w = merge_bp_contn p b w n)).
Proof. intros.
       case_eq w; intros.
       subst. left.
       exists O. (*  exists "p"%string. *) exists(ap_end).
       simpl. easy.
       subst.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst. right.
       exists 1. (* exists s. *) exists (bp_end).
       simpl. rewrite bpend_an. easy.
(*        rewrite(siso_eq(merge_bp_cont p (bp_receivea s l0 s0) w)). simpl.
       split. easy.
       unfold upaco1 in H1. destruct H1.
       unfold singleton. easy. easy. *)
       apply sI_mon.
       
       subst.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       right.
       exists 1. (* exists s. *) exists (bp_end).
       simpl. rewrite bpend_an. easy.
       apply sI_mon.
Qed.


Lemma sinv2: forall w p, singleton w ->
                       (exists n a w', (w = merge_ap_contn p a w' n) /\ singleton w') \/
                       (exists n b w', (w = merge_bp_contn p b w' n) /\ singleton w').
Proof. intros.
       case_eq w; intros.
       subst. left.
       exists O. (*  exists "p"%string. *) exists(ap_end). exists st_end.
       simpl. easy.
       subst. right.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists 1. (* exists s. *) exists (bp_receivea s l0 s0). exists w.
       simpl.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s l0 s0) w)). simpl.
       split. easy.
       unfold upaco1 in H1. destruct H1.
       unfold singleton. easy. easy.
       apply sI_mon.
       
       subst.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       right.
       exists O. (* exists s. *) exists (bp_end). exists (s ! [(l0, s0, w)]).
       simpl. split. easy.
       unfold singleton.
       unfold upaco1 in H1.
       pfold. constructor.
       left. destruct H1.
       easy. easy.
       apply sI_mon.
Qed.

Lemma sinv5: forall w, singleton w ->
                      (exists p l s w', w = st_send p [(l,s,w')] /\ singleton w') \/
                      (exists p l s w', w = st_receive p [(l,s,w')] /\ singleton w') \/
                      (w = st_end) \/
                      (exists p w', forall n a, (w = merge_ap_contn p a w' n) /\ singleton w') \/
                      (exists p w', forall n b, (w = merge_bp_contn p b w' n) /\ singleton w').
Proof. intros.
       case_eq w; intros.
       subst. right. right.  left.  easy.
       subst. right. left.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists s. exists l0. exists s0. exists w.
       split. easy. unfold singleton.
       inversion H1. easy. easy.
       apply sI_mon.
       subst. left.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists s. exists l0. exists s0. exists w.
       split. easy. unfold singleton.
       inversion H1. easy. easy.
       apply sI_mon.
Qed.


Lemma sinv: forall w, singleton w ->
                      (exists p l s w', w = st_send p [(l,s,w')] /\ singleton w') \/
                      (exists p l s w', w = st_receive p [(l,s,w')] /\ singleton w') \/
                      (w = st_end)(*  \/
                      (exists p w', forall n a, (w = merge_ap_contn p a w' n) /\ singleton w') \/
                      (exists p w', forall n b, (w = merge_bp_contn p b w' n) /\ singleton w') *).
Proof. intros.
       case_eq w; intros.
       subst. right. right. (*  left.  *) easy.
       subst. right. left.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists s. exists l0. exists s0. exists w.
       split. easy. unfold singleton.
       inversion H1. easy. easy.
       apply sI_mon.
       subst. left.
       induction l; intros.
       punfold H. inversion H. apply sI_mon.
       punfold H. inversion H. subst.
       exists s. exists l0. exists s0. exists w.
       split. easy. unfold singleton.
       inversion H1. easy. easy.
       apply sI_mon.
Qed.


Lemma casen1: forall p l s1 s2 w1 w2 P Q,
subsort s2 s1 ->
(nRefinementN (mk_siso (st_receive p [(l, s1, (@und w1))]) P) 
              (mk_siso (st_receive p [(l, s2, (@und w2))]) Q) -> False) ->
(nRefinementN w1 w2 -> False).
Proof. intros.
       apply H0.
       apply n_inp_wN.
       easy.
       easy.
Qed.

Lemma casen2: forall p l s1 s2 w1 w2 P Q,
subsort s1 s2 ->
(nRefinementN (mk_siso (st_send p [(l, s1, (@und w1))]) P)
              (mk_siso (st_send p [(l, s2, (@und w2))]) Q) -> False) ->
(nRefinementN w1 w2 -> False).
Proof. intros.
       apply H0.
       apply n_out_wN.
       easy.
       easy.
Qed.

Lemma hhact: forall p w ys, singleton w -> acts w = coconss (p, "?"%string) ys ->
  exists l s w', w = (p & [(l,s,w')]).
Proof. intros.
       specialize(sinv w H); intro Hw.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst. 
       rewrite(stream_eq(acts (q ! [(l, s, w')]))) in H0.
       unfold stream_id in H0. simpl in H0.
       inversion H0.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst. 
       rewrite(stream_eq(acts (q & [(l, s, w')]))) in H0.
       unfold stream_id in H0. simpl in H0.
       inversion H0.
       subst.
       exists l. exists s. exists w'. easy.
       subst.
       rewrite(stream_eq(acts (end))) in H0.
       unfold stream_id in H0. simpl in H0.
       easy.
Qed.

Lemma inReceive: forall w p (Hs: singleton w) (Hin: CoInR (p, "?"%string) (act w)),
  exists c l s w2, w = merge_cp_cont p c (p & [(l,s,w2)]).
Proof. intros.
       remember (p, "?"%string) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.
       subst.
       exists cp_end. exists l1. exists s1. exists w1. 
       rewrite cpend_an. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H. 

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((p, "?"%string) = (p, "?"%string)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H1 w1 H2 H3).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. }
       exists (cp_mergea s H4 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea s H4 l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in Hs.
       assert((p, "?"%string) = (p, "?"%string)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       rewrite Heqw1 in H. simpl in H.
       inversion H.
       symmetry in H6.
       specialize(IHHin H1 w1 H2 H6).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       subst.
       exists (cp_merge s l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.
Qed.

Lemma inReceive_wos: forall w p (Hs: singleton w) (Hin: CoInR (p, "?"%string) (act w)),
  (forall q, CoInR (q, "!"%string) (act w) -> False) ->
  exists a l s w2, w = merge_ap_cont p a (p & [(l,s,w2)]).
Proof. intros w p Hs Hin Hout.
       remember (p, "?"%string) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.
       subst.
       exists ap_end. exists l1. exists s1. exists w1. 
       rewrite apend_an. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H. 

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((p, "?"%string) = (p, "?"%string)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       assert((forall q : participant, CoInR (q, "!"%string) (act w1) -> False)).
       { intros. apply (Hout q). 
         rewrite(coseq_eq((act (s & [(l1, s1, w1)])))).
         unfold coseq_id. simpl. 
         specialize (CoInSplit2 (q, "!"%string) (Delay(cocons (s, "?"%string) (act w1))) (s, "?"%string)  ((act w1))); intros.
         apply H5.
         simpl. easy. easy. easy.
       } 
       specialize(IHHin H1 H4 w1 H2 H3).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. }
       exists (ap_merge s H5 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_ap_cont p (ap_merge s H5 l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(Hout s).
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       subst.
       assert(CoInR (s, "!"%string) (act (s ! [(l1, s1, w1)]))).
       { apply CoInSplit1 with (y := (s, "!"%string)) (ys := (act w1)).
         simpl. easy. easy. }
       specialize (Hout H1). easy.
Qed.

(*
Lemma inReceive_ws: forall w p q (Hs: singleton w) (Hin: CoInR (p, "?"%string) (act w)),
  (CoInR (q, "!"%string) (act w)) ->
  exists a l s w2, w = merge_ap_cont p a (q ! [(l,s,w2)]).
Proof. intros w p q Hs Hin Hout.
       remember (q, "!"%string) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hout; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.
       subst.


       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H.
       subst.

       exists ap_end. exists l1. exists s1. exists w1. 
       rewrite apend_an. easy.
       
       subst.

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((q, "!"%string) = (q, "!"%string)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       
       assert((forall q : participant, CoInR (q, "!"%string) (act w1) -> False)).
       { intros. apply (Hout q). 
         rewrite(coseq_eq((act (s & [(l1, s1, w1)])))).
         unfold coseq_id. simpl. 
         specialize (CoInSplit2 (q, "!"%string) (Delay(cocons (s, "?"%string) (act w1))) (s, "?"%string)  ((act w1))); intros.
         apply H5.
         simpl. easy. easy. easy.
       } 
       specialize(IHHin H1 H4 w1 H2 H3).
       destruct IHHin as (c,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert(p <> s).
       { unfold not in *.
         intro Hp.
         apply H0.
         subst. easy. }
       exists (ap_merge s H5 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_ap_cont p (ap_merge s H5 l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(Hout s).
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       subst.
       assert(CoInR (s, "!"%string) (act (s ! [(l1, s1, w1)]))).
       { apply CoInSplit1 with (y := (s, "!"%string)) (ys := (act w1)).
         simpl. easy. easy. }
       specialize (Hout H1). easy.
Qed. *)

Lemma inSend: forall w p (Hs: singleton w) (Hin: CoInR (p, "!"%string) (act w)),
  exists b l s w2, w = merge_bp_cont p b (p ! [(l,s,w2)]).
Proof. intros.
       remember (p, "!"%string) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hin; intros.
       rewrite Heqv in H0. rewrite <- H0 in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       easy.
       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       inversion H. subst. 
       exists (bp_end). (* exists 1. *) exists l1. exists s1. exists w1. simpl.
       rewrite bpend_an. easy.
       rewrite Heqv in H0. rewrite Hequ in H.
       subst. simpl in *.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((p, "!"%string) = (p, "!"%string)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H1 w1 H2 H3).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_mergea s l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s l1 s1 b) (p ! [(l2, s2, w3)]))).
       simpl. easy.
       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert (p <> s). unfold not in *. intros. apply H0. subst. easy.
       assert((p, "!"%string) = (p, "!"%string)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy. }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H2 w1 H3 H4).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_merge s H1 l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_bp_cont p (bp_merge s H1 l1 s1 b) (p ! [(l2, s2, w3)]))). simpl. easy.
Qed.


Lemma splitFalse: forall a b, ((a <-> b) -> False) -> (((a -> b) -> False) \/ ((b -> a) -> False)).
Proof. intros. 
       specialize(LEM (a -> b)); intro Ha.
       specialize(LEM (b -> a)); intro Hb.
       destruct Ha as [Ha | Ha].
       destruct Hb as [Hb | Hb].
       assert(a <-> b). split; easy.
       apply H in H0. easy. right. easy. left. easy.
Qed.

Lemma n_b_actN: forall p l s s' w w' b P Q,
  subsort s s' ->
  (act_eq w (merge_bp_cont p b w') -> False) ->
  nRefinementN (mk_siso (p ! [(l,s,w)]) P)
               (mk_siso (merge_bp_cont p b (p ! [(l,s',w')])) Q).
Admitted.

Lemma n_a_actN: forall p l s s' w w' a P Q,
  subsort s' s ->
  (act_eq w (merge_ap_cont p a w') -> False) ->
  nRefinementN (mk_siso (p & [(l,s,w)]) P)
               (mk_siso (merge_ap_cont p a (p & [(l,s',w')])) Q).
Admitted.

Axiom DNE: forall P, ~ (~ P) -> P.

Lemma nrefNRS: forall w w', (nRefinementN w w' -> False) -> (@und w) ~< (@und w').
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
         specialize (casen2 q l' s s' ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} Pw Pw'); intros Hp.
         intros Hp2.
         apply Hp. easy. simpl. exact H0.
         exact Hp2.
         subst.
         specialize (n_out_sN ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} q l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn. easy.
         subst.
         rewrite eqb_neq in Heq2.
         specialize (n_out_lN ({| und := w1; sprop := Hs1 |}) {| und := w2; sprop := Hs2 |} q l l' s s' Pw Pw'); intro Hn.
         destruct H0.
         apply Hn. easy.
         rewrite eqb_neq in Heq.

         specialize(LEM (CoNInR (p, "!"%string) (act (q ! [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outN {| und := w1; sprop := Hs1 |} {| und := q ! [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
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
         specialize(n_b_wN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'' H0.
         destruct H0.
         specialize(n_b_actN p l1 s s1 w1 w3 b Pw Pw''); intros HN.
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
         specialize (n_b_sN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw Pw'' Heq3); intros Hn.
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
         specialize (n_b_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 b 1 Pw Pw''); intros Hn.
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
         specialize (n_outN {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
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

         specialize(n_b_wN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         destruct H0.
         specialize(n_b_actN p l1 s s1 w1 w3 b Pw Pw'); intros HN.
         apply HN. easy. easy.

         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_sN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 b 1 Pw Pw' Heq3); intros Hn.
         apply Hn.

         rewrite eqb_neq in Heq2.
         destruct H0.
         assert(singleton w3) as Hs3.
         { specialize (@extbpR p b (p ! [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extsR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_b_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 b 1 Pw Pw'); intros Hn.
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
         specialize(n_outN {| und := w1; sprop := Hs1 |} {| und := end; sprop := Pw' |} p l s Pw); intro Hn.
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
         specialize(n_i_o_1N {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} p q l l' s s' Pw Pw'); intro Hn.
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
         specialize(casen1 q l' s s' {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} Pw Pw'); intro Hn.
         apply Hn. easy. exact H0. exact Hs.
         subst.
         destruct H0.
         specialize(n_inp_sN {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} q l' s s' Pw Pw'); intro Hn.
         apply Hn. easy.
         subst.
         rewrite eqb_neq in Heq2.
         destruct H0.
         specialize(n_inp_lN {| und := w1; sprop := Hs1 |} {| und := w2; sprop := Hs2 |} q l l' s s' Pw Pw'); intro Hn.
         apply Hn. easy.
         rewrite eqb_neq in Heq.

         specialize(LEM (CoNInR (p, "?"%string) (act (q & [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_inpN {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.

         unfold not in Hclass.
         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, "?"%string) (act (q & [(l', s', w2)])) -> CoInR (p, "?"%string) (act (q & [(l', s', w2)]))) as Hpr by admit.
         apply Hpr in Hclass.
         
         specialize(LEM(forall q0 : participant, CoInR (q0, "!"%string) (act (q & [(l', s', w2)])) -> False)); intros Hee.
         destruct Hee as [Hee | Hee].
         specialize(inReceive_wos (q & [(l', s', w2)]) p Pw' Hclass Hee); intros.
         destruct H as (a,(l1,(s1,(w3,IHw3)))).
         rewrite IHw3.
         
         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s1 s); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(LEM (act_eq w1 ((merge_ap_cont p a w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_a (upaco2 refinementR r) w1 w3 p l1 s1 s a 1 Heq3); intro Hrb.
         simpl in Hrb.
         apply Hrb.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.
         assert(singleton (merge_ap_cont p a w3)) as Pw''.
         { specialize(@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize(@extrR p l1 s1 w3 Hss); intros Hss2.
           apply extap. easy.
         }
         specialize(CIH (merge_ap_cont p a w3) Pw'' w1 Hs1).
         right.
         apply CIH.
         intro h.
         apply H0.

         assert(singleton w3) as Hs3.
         { specialize(@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize(@extrR p l1 s1 w3 Hss); intros Hss2.
           easy.
         }

         specialize(n_a_wN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 a 1 Pw'' Pw); intros HN. simpl in HN.
         apply HN. easy. easy. easy.

         destruct H0.
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'.

         specialize(n_a_actN p l1 s s1 w1 w3 a Pw Pw'); intros HN.
         apply HN. easy. easy.

         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.
         assert(singleton w3) as Hs3.
         { specialize(@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize(@extrR p l1 s1 w3 Hss); intros Hss2.
           easy.
         }

         specialize (n_a_sN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l1 s s1 a 1 Pw Pw' Heq3); intros Hn.
         destruct H0.
         apply Hn.

         rewrite eqb_neq in Heq2.
         destruct H0.
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw'.
         assert(singleton w3) as Hs3.
         { specialize (@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extrR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_a_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 a 1 Pw Pw'); intros Hn.
         apply Hn. easy.
         unfold not in Hee.

         admit.
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
         specialize(n_inpN {| und := w1; sprop := Hs1 |} {| und := end; sprop := Pw' |} p l s Pw); intro Hn.
         simpl in Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor. 
       }
       subst.
       { specialize(sinv w' Pw'); intros Hpw'.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.
         destruct H0.
         specialize(n_out_rN {| und := end; sprop := Pw |} {| und := w2; sprop := Hs2 |} q l' s' Pw'); intro Hn.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor.
         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.

         specialize(n_inp_rN {| und := end; sprop := Pw |} {| und := w2; sprop := Hs2 |} q l' s' Pw'); intro Hn.
         destruct H0.
         apply Hn. 
         rewrite(coseq_eq(act st_end)). unfold coseq_id. simpl.
         constructor.
         subst.
         pfold. constructor.
       }
Admitted.


