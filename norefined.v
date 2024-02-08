From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.

Lemma exts: forall {p l s} w, singleton w -> singleton (st_send p [(l,s,w)]).
Proof. intros p l s w H.
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


Lemma extcpR: forall {p c} w, singleton (merge_cp_cont p c w) -> singleton w.
Proof. intros p c.
       induction c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) w)) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq((merge_cp_cont p (cp_mergea q n s s0 c) w))) in H.
       simpl in H.
       apply IHc. apply extrR in H. easy.
       rewrite(siso_eq((merge_cp_cont p (cp_send s s0 s1) w))) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(siso_eq((merge_cp_cont p (cp_merge s s0 s1 c) w))) in H.
       simpl in H. 
       apply IHc. apply extsR in H. easy.
       rewrite cpend_an in H. easy.
Qed.

Lemma extdcnR: forall {n p c} w, singleton ((merge_cp_contn p c w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply (@extcpR p c w).
       apply (IHn p c (merge_cp_cont p c w)).
       simpl in H.
       rewrite mcomm3. exact H.
Qed.


Lemma extdpR: forall {p d} w, singleton ((merge_dp_cont p d w)) -> singleton w.
Proof. intros p d.
       induction d; intros.
       subst.
       rewrite(siso_eq((merge_dp_cont p (dp_receive q n s s0) w))) in H.
       simpl in H. apply extrR in H. easy.
       rewrite(siso_eq((merge_dp_cont p (dp_mergea q n s s0 d) w))) in H.
       simpl in H.
       apply IHd. apply extrR in H. easy.
       rewrite(siso_eq((merge_dp_cont p (dp_send q n s s0) w))) in H.
       simpl in H. apply extsR in H. easy.
       rewrite(siso_eq((merge_dp_cont p (dp_merge q n s s0 d) w))) in H.
       simpl in H. 
       apply IHd. apply extsR in H. easy.
       rewrite dpend_an in H. easy.
Qed.


Lemma extdpnR: forall {n p d} w, singleton ((merge_dp_contn p d w n)) -> singleton w.
Proof. intros n.
       induction n; intros.
       simpl. easy.
       simpl.
       apply (@extdpR p d w).
       apply (IHn p d (merge_dp_cont p d w)).
       simpl in H.
       rewrite mcomm4. exact H.
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


Fixpoint isInCp (p: participant) (c: Cp p): bool :=
  match c with
    | cp_send q l s       => true
    | cp_merge q l s c    => true
    | cp_mergea q H l s c => isInCp p c
    | _                   => false
  end.

Lemma cpap: forall p c w,
  isInCp p c = false ->
  exists a, merge_cp_cont p c w = merge_ap_cont p a w.
Proof. intros p c.
       induction c; intros.
       - simpl in *. 
         exists (ap_receive q n s s0).
         rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) w)).
         rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) w)).
         simpl. easy.
       - simpl in *.
         specialize(IHc w H).
         destruct IHc as (a,IHc).
         exists(ap_merge q n s s0 a).
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) w)).
         rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) w)).
         simpl.
         rewrite IHc. easy.
       - simpl in *. easy.
       - simpl in *. easy.
       - simpl in *. exists ap_end. 
         rewrite(siso_eq( merge_ap_cont p ap_end w)).
         rewrite(siso_eq(merge_cp_cont p cp_end w )).
         simpl. easy.
Qed.


Inductive nRefinementN: siso -> siso -> Prop :=
  | n_outN  : forall w w' p l s P, 
              CoNInR (p,snd) (act (@und w')) -> 
              nRefinementN (mk_siso (st_send p [(l,s,(@und w))]) P) w'
  | n_inpN  : forall w w' p l s P, 
              CoNInR (p,rcv) (act (@und w')) -> 
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) w'
(*   | n_inpN  : forall w w' p a l s P, 
              CoNInR (p,rcv) (act (@und w')) -> 
              nRefinementN (mk_siso (merge_ap_cont p a (st_receive p [(l,s,(@und w))])) P) w' *)
(*   | n_inpN  : forall w w' p l s P, 
              CoNInR (p,rcv) (act (@und w')) -> 
              nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) w' *)
  | n_out_rN: forall w w' p l s P, 
              CoNInR (p,snd) (act (@und w)) -> 
              nRefinementN w (mk_siso (st_send p [(l,s,(@und w'))]) P)
  | n_inp_rN: forall w w' p l s P,
              CoNInR (p,rcv) (act (@und w)) -> 
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
  | n_i_o_2N: forall w w' p l l' s s' c P Q, isInCp p c = true ->
                                             nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                          (mk_siso (merge_cp_cont p c (st_receive p [(l',s',(@und w'))])) Q)
(*   | n_i_o_2N: forall w w' p q l l' s s' c n P Q, nRefinementN (mk_siso (st_receive p [(l,s,(@und w))]) P) 
                                                              (mk_siso (merge_cp_contn p c (st_send q [(l',s',(@und w'))]) n) Q) *)
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

Inductive nRefinement: st -> st -> Prop :=
  | n_out  : forall w w' p l s, 
             CoNInR (p,snd) (act w') -> 
             nRefinement (st_send p [(l,s,w)]) w'
  | n_inp  : forall w w' p l s, 
             CoNInR (p,rcv) (act w') -> nRefinement (st_receive p [(l,s,w)]) w'
  | n_out_r: forall w w' p l s, 
             CoNInR (p,snd) (act w) -> nRefinement w (st_send p [(l,s,w')])
  | n_inp_r: forall w w' p l s, 
             CoNInR (p,rcv) (act w) -> nRefinement w (st_receive p [(l,s,w')])
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
(*   | n_new1 :  forall w w' p q l s, p <> q -> CoIn (p,snd) (act w') -> nRefinement (st_send p [(l,s,w)]) (st_send q [(l,s,w')]). *)
(*   | n_i_o_2R: forall w w' p q l l' s s' (a: Ap p) n, nRefinement (merge_ap_contn p a (st_send q [(l',s',w')]) n) (st_receive p [(l,s,w)]). *)
(*   | n_i_o_1R: forall w w' p q l l' s s', nRefinement (st_send p [(l,s,w)]) (st_receive q [(l',s',w')]). *)

Notation "x '/~<' y" := (nRefinement x y) (at level 50, left associativity).


(* Inductive nRefinementA: siso -> siso -> Prop :=
  | n_outA  : forall w w' p l s, 
              CoNInR (p,snd) (actC w') -> nRefinementA (siso_send p (l,s,w)) w'
  | n_inpA  : forall w w' p l s, 
              CoNInR (p,rcv) (actC w') -> nRefinementA (siso_receive p (l,s,w)) w'
  | n_out_rA: forall w w' p l s, 
              CoNInR (p,snd) (actC w) -> nRefinementA w (siso_send p (l,s,w'))
  | n_inp_rA: forall w w' p l s, 
              CoNInR (p,rcv) (actC w) -> nRefinementA w (siso_receive p (l,s,w'))
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

Definition eqbp2 (a b: (participant*actT)) :=
  andb (eqb a.1 b.1) (actTeqb a.2 b.2).


Lemma eq0: forall l (a: (participant*actT)) xs, List.In a l \/ CoInR a xs ->
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

       case_eq(eqbp2 a0 a); intros.
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
       simpl in H2.
       apply act_eqb_eq in H2.
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
       apply act_neqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       apply IHl. left. easy.

       case_eq(eqbp2 a0 a); intros.
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
       apply act_eqb_eq in H1.
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
       apply act_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       apply IHl. right. easy.
Qed.

Lemma eq0A: forall l (a: (participant*actT)) xs, List.In a l \/ CoInRA (upaco2 CoInRA bot2) a xs ->
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

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp2 in H1.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H1.
       destruct H1.
       rewrite eqb_eq in H1.
       apply act_eqb_eq in H2.
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
       apply act_neqb_neq in H1.
       unfold not in *.
       intro H2.
       apply H1.
       destruct a, a0. simpl in *.
       inversion H2. easy.
       unfold upaco2. left. pfold.
       apply IHl. left. easy.

       case_eq(eqbp2 a0 a); intros.
       unfold eqbp2 in H0.
       rewrite(coseq_eq(appendL (a :: l) xs)).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (appendL l xs)). simpl.
       destruct a, a0.
       rewrite Bool.andb_true_iff in H0.
       destruct H0.
       rewrite eqb_eq in H0.
       apply act_eqb_eq in H1.
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
       apply act_neqb_neq in H0.
       unfold not in *.
       intro H1.
       apply H0.
       destruct a, a0. simpl in *.
       inversion H1. easy.
       unfold upaco2. left. pfold.
       apply IHl. right. easy.
Qed.


Lemma eq1b: forall n p b l s w,
CoInR (p, snd) (act (merge_bp_contn p b (p ! [(l, s, w)]) n)).
Proof. intros. rewrite h0.
       apply eq0.
       right.
       rewrite(coseq_eq(act (p ! [(l, s, w)]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 (p, snd)
       (Delay(cocons (p, snd) (act w)))
       (p, snd)
       (act w)
       ); intro Ha.
       apply Ha. simpl. easy. easy.
Qed.


Lemma act_rec: forall n p b l s s0 s1 s2 w,
(act (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) (n.+1)))
=
Delay (cocons (s, rcv) (act (merge_bp_cont p b (merge_bp_contn p (bp_mergea s s0 s1 b) (p ! [(l, s2, w)]) n)))).
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

Lemma merge_eqac: forall p a c l s w,
 merge_ap_cont p a (p & [(l, s, w)]) =
 merge_cp_cont p c (p & [(l, s, w)]) ->
 merge_ap_cont p a w =
 merge_cp_cont p c w.
Proof. intros p a.
       induction a; intros.
       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s2 s3) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       case_eq c0; intros.
       subst.
       rewrite(siso_eq( merge_cp_cont p (cp_receive q n1 s s0) (p & [(l, s1, w)]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n1 s s0 c) (p & [(l, s1, w)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s4) (p & [(l, s1, w)]))) in H4.
       simpl in H4.
       easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s4 c) (p & [(l, s1, w)]))) in H4.
       simpl in H4. easy.
       subst. rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.
       
       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) (p & [(l, s1, w)]))) in H.
       simpl in H. inversion H.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s2 s3 a) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q0 n0 s2 s3) w)).
       simpl.
       subst.
       specialize(IHa (cp_end) l s1 w).
       rewrite IHa. rewrite cpend_an. easy.
       rewrite cpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s2 s3 a) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q0 n0 s2 s3 c0) w)).
       simpl.
       specialize(IHa c0 l s1 w).
       rewrite IHa. easy. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_send s2 s3 s4) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst. 
       rewrite(siso_eq( merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s2 s3 s4 c0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l, s1, w)]))) in H.
       rewrite cpend_an in H.
       simpl in H.
       inversion H. subst. easy.
       rewrite apend_an in H.
       rewrite apend_an.
       
       case_eq c; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s0 s1) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s0 s1 c0) (p & [(l, s, w)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_send s0 s1 s2) (p & [(l, s, w)]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s0 s1 s2 c0) (p & [(l, s, w)]))) in H. 
       simpl in H. easy.
       rewrite cpend_an. easy.
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
         subst.
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
         apply CoInSplit2A with (y := (p0, rcv)) (ys := (act w0)). simpl. easy. easy.
         unfold upaco2.
         specialize(H5 (p, snd)).
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
         apply CoInSplit2A with (y := (p0, snd)) (ys := (act w0)). simpl. easy.
         unfold not in *.
         intro Heq2.
         apply Heq. inversion Heq2. easy.
         unfold upaco2. left.
         specialize(H5 (p, snd)).
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
         apply CoInSplit2A with (y := (p0, rcv)) (ys := (act w0)). simpl. easy.
         unfold not in *.
         intro Heq2.
         apply Heq. inversion Heq2. easy.
         unfold upaco2. left.
         specialize(H5 (p, rcv)).
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
         apply CoInSplit2A with (y := (p0, snd)) (ys := (act w0)). simpl. easy. easy.
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


Lemma case12_1c2: forall p c l l' s s' w w',
isInCp p c = true ->
p & [(l, s, w)] = merge_cp_cont p c (p & [(l', s', w')]) ->  False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l', s', w')]))) in H0.
         simpl in H0.
         inversion H0. subst. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l', s', w')]))) in H0.
         simpl in H0. easy.
       - rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l', s', w')]))) in H0.
         simpl in H0. easy.
       - simpl in *. easy.
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

Lemma case12_1d: forall n p q a l l' s s' w w',
p & [(l, s, w)] = merge_dp_contn p a (q ! [(l', s', w')]) n ->  False.
Proof. intro n.
       induction n; intros.
       simpl in H. easy.
       simpl in H.
       case_eq a; intros.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q0 n0 s0 s1) (merge_dp_contn p (dp_receive q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q0 n0 s0 s1 d) (merge_dp_contn p (dp_mergea q0 n0 s0 s1 d) (q ! [(l', s', w')]) n))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_send q0 n0 s0 s1) (merge_dp_contn p (dp_send q0 n0 s0 s1) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q0 n0 s0 s1 d) (merge_dp_contn p (dp_merge q0 n0 s0 s1 d) (q ! [(l', s', w')]) n))) in H.
       simpl in H. easy. 
       subst.
       rewrite dpend_ann in H.
       rewrite dpend_an in H. easy.
Qed.


Lemma case12_2c2: forall p c a l1 s1 l2 s2 w1 w2,
isInCp p c = true ->
merge_ap_cont p a (p & [(l1, s1, w1)]) = merge_cp_cont p c (p & [(l2, s2, w2)]) -> False.
Proof. intros p c.
       induction c; intros.
       - simpl in *. easy.
       - simpl in *.
         rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l2, s2, w2)]))) in H0.
         simpl in H0.
         case_eq a; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l1, s1, w1)]))) in H0.
           simpl in H0.
           inversion H0.
           subst.
           apply (IHc (ap_end) l1 s1 l2 s2 w1 w2).
           easy. rewrite apend_an. easy.
        + subst.
          rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l1, s1, w1)]))) in H0.
          simpl in H0.
          inversion H0.
          subst.
          apply (IHc a0 l1 s1 l2 s2 w1 w2).
          easy. easy.
        + subst.
          rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l1, s1, w1)]))) in H0.
          simpl in H0.
          inversion H0. subst. easy.
       - case_eq a; intros.
         + subst. 
           rewrite(siso_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst. 
           rewrite(siso_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
       - case_eq a; intros.
         + subst.
           rewrite(siso_eq(merge_ap_cont p (ap_receive q n s4 s5) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite(siso_eq(merge_ap_cont p (ap_merge q n s4 s5 a0) (p & [(l1, s2, w1)]))) in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
         + subst.
           rewrite apend_an in H0.
           rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l2, s3, w2)]))) in H0.
           simpl in H0. easy.
       - simpl in *. easy.
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

Lemma case12_2d: forall p q a1 a2 l l' s s' w w',
merge_ap_cont p a1 (p & [(l, s, w)]) = merge_dp_cont p a2 (q ! [(l', s', w')]) -> False.
Proof. intros p q a1.
       induction a1; intros.
       case_eq a2; intros.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H.
       inversion H. subst.
       case_eq d; intros.
       subst.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4.
       inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_mergea q0 n1 s s0 d0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_send q0 n1 s s0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_merge q0 n1 s s0 d0) (q ! [(l', s', w')]))) in H4.
       simpl in H4. easy.
       
       subst.
       rewrite dpend_an in H4. easy.
       
       subst.
       rewrite(siso_eq( merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_send q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite dpend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n s s0) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.

       case_eq a2; intros.
(*        specialize (IHa1 a2 l l' s1 s' w w'). *)
       subst. 
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 (dp_end) l l' s1 s' w w').
       apply IHa1.
       rewrite dpend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst.
       specialize (IHa1 d l l' s1 s' w w').
       apply IHa1. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_send q1 n0 s2 s3) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q1 n0 s2 s3 d) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       
       subst. rewrite dpend_an in H.
       rewrite(siso_eq( merge_ap_cont p (ap_merge q0 n s s0 a1) (p & [(l, s1, w)]))) in H.
       simpl in H. easy.
       rewrite apend_an in H.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_dp_cont p (dp_receive q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_mergea q0 n s0 s1 d) (q ! [(l', s', w')]))) in H.
       simpl in H. inversion H. subst. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_send q0 n s0 s1) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite(siso_eq(merge_dp_cont p (dp_merge q0 n s0 s1 d) (q ! [(l', s', w')]))) in H.
       simpl in H. easy.
       subst. rewrite dpend_an in H. easy.
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
(*
         case_eq a; intros. subst.
         rewrite(siso_eq(merge_ap_cont p (ap_receive q n s1 s2) (p & [(l, s, und)]))) in H1.
         simpl in H1.
         inversion H1. subst.
         unfold upaco2 in H4.
         destruct H4.
         punfold H4.
         inversion H4. subst.
         rewrite <- H2 in H0. admit.
         subst. 
         rewrite <- H2 in H0. admit.
         apply refinementR_mon.
         easy.
         subst.
         rewrite(siso_eq(merge_ap_cont p (ap_merge q n s1 s2 a0) (p & [(l, s, und)]))) in H1.
         simpl in H1.
         inversion H1.
         subst.
         
(*          subst. *)
         rewrite <- H2 in H0.
         unfold upaco2 in H4.
         destruct H4.
         punfold H4.
         inversion H4. subst.
         inversion H10.
         punfold H6.
         inversion H6.
          subst.
         
         unfold upaco2 in H7.
         destruct H7.
         punfold H7.
         inversion H7. subst.
         rewrite <- H2 in H0. *)
         
         
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
         apply CoInSplit2A with (y := (p0, rcv)) (ys := (act w0)). simpl. easy. easy.
         unfold upaco2.
         specialize(H5 (p, snd)).
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
         apply CoInSplit2A with (y := (p0, snd)) (ys := (act w0)). simpl. easy.
         unfold not in *.
         intro Heq2.
         apply Heq. inversion Heq2. easy.
         unfold upaco2. left.
         specialize(H5 (p, snd)).
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
         apply CoInSplit2A with (y := (p0, rcv)) (ys := (act w0)). simpl. easy.
         unfold not in *.
         intro Heq2.
         apply Heq. inversion Heq2. easy.
         unfold upaco2. left.
         specialize(H5 (p, rcv)).
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
         apply CoInSplit2A with (y := (p0, snd)) (ys := (act w0)). simpl. easy. easy.
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
         apply case12_1c2 in H6.
         easy. easy.
         subst.
         rewrite <- mergeeq2 in H6.
         apply case12_2c2 in H6. easy.
         easy.
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

(* Axiom LEM: forall (p: Prop), p \/ ~p. *)

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

Lemma hhact: forall p w ys, singleton w -> acts w = coconss (p, rcv) ys ->
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

Lemma ninReceive: forall w p (Hs: singleton w) (Hnin: CoNInR (p, rcv) (act w)),
  exists c w2, w = merge_cp_cont p c w2 /\ CoNInR (p, rcv) (act w2).
Proof. intros.
       remember (p, rcv) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hnin; intros.
       specialize(sinv w Hs); intro Hw.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst.
       rewrite(coseq_eq(act (q ! [(l, s, w')]))) in Hequ.
       unfold coseq_id in Hequ.
       easy.
       destruct Hw as [Hw | Hw].
       destruct Hw as (q,(l,(s,(w',(Hw1,Hw2))))).
       subst.
       rewrite(coseq_eq(act (q & [(l, s, w')]))) in Hequ.
       unfold coseq_id in Hequ.
       easy.
       exists cp_end. exists st_end.
       rewrite(siso_eq(merge_cp_cont p cp_end (end))). simpl.
       split. easy.
       rewrite(coseq_eq((act (end)))).
       unfold coseq_id. simpl.
       constructor.

       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       simpl in H.
       inversion H.
       subst.
       assert((p, rcv) = (p, rcv)) as Ha1 by easy.
       assert(singleton w1) as Ha2.
       { apply extrR in Hs. easy. }
       assert(act w1 = act w1) as Ha3 by easy.
       specialize(IHHnin Ha1 w1 Ha2 Ha3).
       destruct IHHnin as (c1,(w2,(IHN1, IHN2))).
       assert(p <> s) as Ha4.
       { unfold not. intro Hb. apply H0. subst. easy. }
       subst.
       exists (cp_mergea s Ha4 l1 s1 c1). exists w2.
       rewrite(siso_eq( merge_cp_cont p (cp_mergea s Ha4 l1 s1 c1) w2)).
       simpl. split. easy. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       simpl in H. inversion H. subst.
       assert((p, rcv) = (p, rcv)) as Ha1 by easy.
       assert(singleton w1) as Ha2.
       { apply extsR in Hs. easy. }
       assert(act w1 = act w1) as Ha3 by easy.
       specialize(IHHnin Ha1 w1 Ha2 Ha3).
       destruct IHHnin as (c1,(w2,(IHN1, IHN2))).
       exists (cp_merge s l1 s1 c1). exists w2.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s l1 s1 c1) w2)).
       simpl. subst. split; easy.
Qed.

Lemma inReceive: forall w p (Hs: singleton w) (Hin: CoInR (p, rcv) (act w)),
  exists c l s w2, w = merge_cp_cont p c (p & [(l,s,w2)]).
Proof. intros.
       remember (p, rcv) as v.
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
       assert((p, rcv) = (p, rcv)) by easy.
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
       assert((p, rcv) = (p, rcv)) by easy.
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

Lemma inSend: forall w p (Hs: singleton w) (Hin: CoInR (p, snd) (act w)),
  exists b l s w2, w = merge_bp_cont p b (p ! [(l,s,w2)]).
Proof. intros.
       remember (p, snd) as v.
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
       assert((p, snd) = (p, snd)) by easy.
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
       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy. }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHin H2 w1 H3 H4).
       destruct IHHin as (b,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (bp_merge s H1 l1 s1 b). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_bp_cont p (bp_merge s H1 l1 s1 b) (p ! [(l2, s2, w3)]))). simpl. easy.
Qed.

Inductive Ep: Type :=
  | ep_send   : participant -> label -> st.sort -> Ep
  | ep_merge  : participant -> label -> st.sort -> Ep -> Ep
  | ep_end    : Ep.

CoFixpoint merge_ep_cont (e: Ep) (w: st): st :=
  match e with 
    | ep_send q l s    => st_send q [(l,s,w)]
    | ep_merge q l s c => st_send q [(l,s,(merge_ep_cont c w))]
    | ep_end           => w
  end.

Fixpoint merge_ep_contn (e: Ep) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ep_cont e (merge_ep_contn e w k)
  end.

CoFixpoint merge_ape_cont (p: participant) (a: Ap p) (e: Ep) (w: st): st :=
  match a with
    | ap_receive q H l s  => st_receive q [(l,s,merge_ep_cont e w)]
    | ap_merge q H l s w' => st_receive q [(l,s,(merge_ape_cont p w' e w))]
    | ap_end              => w
  end.

Fixpoint merge_ape_contn (p: participant) (a: Ap p) (e: Ep) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ape_cont p a e (merge_ape_contn p a e w k)
  end.
  

Lemma inReceive_wos: forall w p (Hs: singleton w) (Hin: CoInR (p, rcv) (act w)),
  (forall q, CoInR (q, snd) (act w) -> False) ->
  exists a l s w2, w = merge_ap_cont p a (p & [(l,s,w2)]).
Proof. intros w p Hs Hin Hout.
       remember (p, rcv) as v.
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
       assert((p, rcv) = (p, rcv)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       assert((forall q : participant, CoInR (q, snd) (act w1) -> False)).
       { intros. apply (Hout q). 
         rewrite(coseq_eq((act (s & [(l1, s1, w1)])))).
         unfold coseq_id. simpl. 
         specialize (CoInSplit2 (q, snd) (Delay(cocons (s, rcv) (act w1))) (s, rcv)  ((act w1))); intros.
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
         subst. easy. 
       }
       exists (ap_merge s H5 l1 s1 c). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_ap_cont p (ap_merge s H5 l1 s1 c) (p & [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(Hout s).
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       subst.
       assert(CoInR (s, snd) (act (s ! [(l1, s1, w1)]))).
       { apply CoInSplit1 with (y := (s, snd)) (ys := (act w1)).
         simpl. easy. easy.
       }
       specialize (Hout H1). easy.
Qed.

Lemma inReceive_wsE: forall w p (Hs: singleton w) (* (Hin: CoInR (p, rcv) (act w)) *),
  (forall q, p <> q) ->
  (exists q, CoInR (q, snd) (act w)) ->
  exists d q l s w2, w = merge_dp_cont p d (q ! [(l,s,w2)]).
Proof. intros w p Hs Hdiff (q, Hout).
       remember (q, snd) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hout; intros.

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
       exists dp_end. exists q. exists l1. exists s1. exists w1.
       rewrite dpend_an. easy.

       subst.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.

       assert((q, snd) = (q, snd)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHout H1 w1 H2 H3).
       destruct IHHout as (d,(q1,(l2,(s2,(w3,IHw3))))).
       rewrite IHw3.
       assert (p <> s).
       { easy. }
       exists (dp_mergea s H4 l1 s1 d). exists q1. exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea s H4 l1 s1 d) (q1 ! [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert((q, snd) = (q, snd)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy. }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHout H1 w1 H2 H3).
       destruct IHHout as (d,(q1,(l2,(s2,(w3,IHw3))))).
       rewrite IHw3.
       assert (p <> s). (* unfold not in *. intros. apply H0. subst. easy. *)
       { easy. }
       exists (dp_merge s H4 l1 s1 d). exists q1. exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_dp_cont p (dp_merge s H4 l1 s1 d) (q1 ! [(l2, s2, w3)]))). simpl. easy.
Qed.

Lemma inReceive_ws: forall w p (Hs: singleton w) (* (Hin: CoInR (p, rcv) (act w)) *),
  (forall q, p <> q) ->
  (forall q, CoInR (q, snd) (act w)) ->
  exists d l s w2, w = merge_dp_cont p d (p ! [(l,s,w2)]).
Proof. intros w p Hs Hdiff Hout.
       specialize(Hout p).
       remember (p, snd) as v.
       remember (act w) as u.
       generalize dependent w.
       induction Hout; intros.

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
       exists dp_end. exists l1. exists s1. exists w1.
       rewrite dpend_an. easy.

       subst.
       case_eq w; intros. subst. easy.
       subst.
       specialize(invsingl s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.

       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extrR in Hs. easy.  }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHout H1 w1 H2 H3).
       destruct IHHout as (d,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       assert (p <> s).
       { easy.
       }
       exists (dp_mergea s H4 l1 s1 d). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea s H4 l1 s1 d) (p ! [(l2, s2, w3)]))).
       simpl. easy.

       subst.
       specialize(invsingl2 s l Hs); intros Hl.
       destruct Hl as (l1,(s1,(w1, Heqw1))).
       rewrite Heqw1 in H.
       subst. inversion H. subst.
       assert (p <> s). unfold not in *. intros. apply H0. subst. easy.
       assert((p, snd) = (p, snd)) by easy.
       assert(singleton w1).
       { apply extsR in Hs. easy. }
       assert((act w1) = (act w1)) by easy.
       specialize(IHHout H2 w1 H3 H4).
       destruct IHHout as (d,(l2,(s2,(w3,IHw3)))).
       rewrite IHw3.
       exists (dp_merge s H1 l1 s1 d). exists l2. exists s2. exists w3.
       rewrite(siso_eq(merge_dp_cont p (dp_merge s H1 l1 s1 d) (p ! [(l2, s2, w3)]))). simpl. easy.
Qed.

Lemma splitFalse: forall a b, ((a <-> b) -> False) -> (((a -> b) -> False) \/ ((b -> a) -> False)).
Proof. intros.
       specialize(classic (a -> b)); intro Ha.
       specialize(classic (b -> a)); intro Hb.
       destruct Ha as [Ha | Ha].
       destruct Hb as [Hb | Hb].
       assert(a <-> b). split; easy.
       apply H in H0. easy. right. easy. left. easy.
Qed.

(* Lemma indp: forall (p: participant) a w (Hs: singleton w) (i: Ap p -> st -> Prop),
 (forall q l s w (Hs: singleton w) (Hneq: p <> q), i a w -> i (ap_merge q Hneq l s a) w) ->
 (forall q l s w (Hs: singleton w) (Hneq: p <> q), i (ap_receive q Hneq l s) w) ->
 (forall q l s w (Hs: singleton w) (Hneq: p <> q), i (ap_send q Hneq l s) w) ->
 i a w.
Admitted.
  
 *)
  
Lemma n_b_actN: forall p l s s' w w' b P Q,
  subsort s s' ->
  (act_neq w (merge_bp_cont p b w')) ->
  nRefinementN (mk_siso (p ! [(l,s,w)]) P)
               (mk_siso (merge_bp_cont p b (p ! [(l,s',w')])) Q).
Admitted.

Lemma act_eq_neq: forall w w', (act_eq w w' -> False) -> act_neq w w'.
Admitted.

Inductive Fp: Type :=
  | fp_receive: participant -> label -> st.sort -> Fp
  | fp_send   : participant -> label -> st.sort -> Fp
  | fp_merge  : participant -> label -> st.sort -> Fp -> Fp
  | fp_mergea : participant -> label -> st.sort -> Fp -> Fp
  | fp_end    : Fp.

CoFixpoint merge_fp_cont (f: Fp) (w: st): st :=
  match f with 
    | fp_send q l s     => st_send q [(l,s,w)]
    | fp_receive q l s  => st_receive q [(l,s,w)]
    | fp_merge q l s c  => st_send q [(l,s,(merge_fp_cont c w))]
    | fp_mergea q l s c => st_receive q [(l,s,(merge_fp_cont c w))]
    | fp_end            => w
  end.

Fixpoint merge_fp_contn (f: Fp) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_fp_cont f (merge_fp_contn f w k)
  end.


Inductive FinPre: st -> list (participant*actT) -> nat -> Prop :=
  | fpe: forall n, FinPre st_end [] n
  | fpr: forall p lbl s w l n, FinPre w l n -> FinPre (st_receive p [(lbl,s,w)]) ((p,rcv) :: l) (S n) 
  | fps: forall p lbl s w l n, FinPre w l n -> FinPre (st_send p [(lbl,s,w)]) ((p,snd) :: l) (S n).


Lemma n_a_actNH2: forall p b q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoNInR (p,snd) (act (merge_ap_cont q a w2))),
  nRefinementN (mk_siso (merge_bp_cont p b (p ! [(l,s,w1)])) P)
               (mk_siso (merge_ap_cont q a w2) Q).
Admitted.

Lemma n_a_actNH3: forall p c q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoNInR (p,rcv) (act (merge_ap_cont q a w2))),
  nRefinementN (mk_siso (merge_ap_cont q a w2) Q)
               (mk_siso (merge_cp_cont p c (p & [(l,s,w1)])) P).
Admitted.

Lemma n_a_actNH4: forall p b q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoNInR (p,snd) (act (merge_ap_cont q a w2))),
  nRefinementN (mk_siso (merge_ap_cont q a w2) Q)
               (mk_siso (merge_bp_cont p b (p ! [(l,s,w1)])) P).
Admitted.

Lemma n_a_actNH1: forall p c q a l s w1 w2 P Q (Hw1: singleton w1) (Hw2: singleton w2) (Hw2a: CoNInR (p,rcv) (act (merge_ap_cont q a w2))),
  nRefinementN (mk_siso (merge_cp_cont p c (p & [(l,s,w1)])) P)
               (mk_siso (merge_ap_cont q a w2) Q).
Proof. intros p c.
       induction c; intros.
       destruct a.
       
       generalize dependent P.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l, s1, w1)]))).
       generalize dependent Q.
       rewrite(siso_eq(merge_ap_cont q0 (ap_receive q1 n0 s2 s3) w2)).
       simpl. intros Q P.
       case_eq(eqb q1 q); intros Heq1.
       rewrite eqb_eq in Heq1.
       subst.
       (* by n_inp_wN and n_inpN*)
       admit.
       rewrite eqb_neq in Heq1.
       specialize(classic (CoNInR (q, rcv) (act (q1 & [(s2, s3, w2)])))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       specialize (n_inpN {| und := (p & [(l, s1, w1)]); sprop := Hs1 |} {| und := q1 & [(s2, s3, w2)]; sprop := Q |} q s s0 P); intros HH.
       unfold und in HH.
       simpl in HH. apply HH. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (q, rcv) (act (q1 & [(s2, s3, w2)])) -> CoInR (q, rcv) (act (q1 & [(s2, s3, w2)]))) as Hin by admit.
       apply Hin in Hclass.
       specialize(inReceive ( q1 & [(s2, s3, w2)]) q Q Hclass); intros HHin.
       destruct HHin as (c4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.
       case_eq(isInCp q c4); intros.
       assert(singleton w4) as Hs4.
       { apply extcpR, extrR in Q.
         easy.
       }
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       specialize(n_i_o_2N (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs4) q s l4 s0 s4 c4 P Q); intros HN2.
       apply HN2. easy.
       
       specialize(cpap q c4 (q & [(l4, s4, w4)]) H); intros Hpc.
       destruct Hpc as (a, Hpc).
       generalize dependent Q.
       rewrite Hpc.
       intros Q.
       
       case_eq(eqb l4 s); intros Heq2.
       rewrite eqb_eq in Heq2.
       subst.
       specialize(sort_dec s4 s0); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
       rewrite(siso_eq((merge_ap_cont q0 (ap_receive q1 n0 s2 s3) w2))) in Hw2a.
       simpl in Hw2a.
       rewrite Heqw4 in Hw2a.
       rewrite Hpc in Hw2a.
       assert(CoNInR (p, rcv) (act (merge_ap_cont q a w4))) as Hnin by admit.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_ap_cont q a w4)) as Hs3 by admit.
       specialize(n_a_wN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 Hs3 P Q Heq3); intros HNAWN.
       apply HNAWN.
       simpl.
       specialize(n_inpN (mk_siso w1 Hw1) (mk_siso (merge_ap_cont q a w4) Hs3) p l s1); intro HNP.
       apply HNP. simpl. easy.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_sN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 P Q Heq3); intro HNS.
       apply HNS.
       rewrite eqb_neq in Heq2.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_lN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s l4 s0 s4 a 1 P Q ); intro HNL.
       apply HNL.
       easy.
       admit.

       generalize dependent P.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (p & [(l, s1, w1)]))).
       generalize dependent Q.
       rewrite(siso_eq(merge_ap_cont q0 (ap_merge q1 n0 s2 s3 a) w2)).
       simpl. intros Q P.
       rewrite(siso_eq((merge_ap_cont q0 (ap_merge q1 n0 s2 s3 a) w2))) in Hw2a.
       simpl in Hw2a.
       case_eq(eqb q1 q); intros Heq1.
       rewrite eqb_eq in Heq1.
       subst.
       (* by n_inp_wN and n_inpN*)
       admit.
       rewrite eqb_neq in Heq1.
       specialize(classic (CoNInR (q, rcv) (act (q1 & [(s2, s3, merge_ap_cont q0 a w2)])))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       specialize (n_inpN {| und := (p & [(l, s1, w1)]); sprop := Hs1 |} {| und := q1 & [(s2, s3, merge_ap_cont q0 a w2)]; sprop := Q |} q s s0 P); intros HH.
       unfold und in HH.
       simpl in HH. apply HH. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (q, rcv) (act (q1 & [(s2, s3, merge_ap_cont q0 a w2)])) -> CoInR (q, rcv) (act (q1 & [(s2, s3, merge_ap_cont q0 a w2)]))) as Hin by admit.
       apply Hin in Hclass.
       specialize(inReceive (q1 & [(s2, s3, merge_ap_cont q0 a w2)]) q Q Hclass); intros HHin.
       destruct HHin as (c4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.
       case_eq(isInCp q c4); intros.
       assert(singleton w4) as Hs4.
       { apply extcpR, extrR in Q.
         easy.
       }
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       specialize(n_i_o_2N (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs4) q s l4 s0 s4 c4 P Q); intros HN2.
       apply HN2. easy.
       
       specialize(cpap q c4 (q & [(l4, s4, w4)]) H); intros Hpc.
       rename a into a1.
       destruct Hpc as (a, Hpc).
       generalize dependent Q.
       rewrite Hpc.
       intros Q.

       case_eq(eqb l4 s); intros Heq2.
       rewrite eqb_eq in Heq2.
       subst.
       specialize(sort_dec s4 s0); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
       rewrite Heqw4 in Hw2a.
       rewrite Hpc in Hw2a.
       assert(CoNInR (p, rcv) (act (merge_ap_cont q a w4))) as Hnin by admit.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_ap_cont q a w4)) as Hs3 by admit.
       specialize(n_a_wN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 Hs3 P Q Heq3); intros HNAWN.
       apply HNAWN.
       simpl.
       specialize(n_inpN (mk_siso w1 Hw1) (mk_siso (merge_ap_cont q a w4) Hs3) p l s1); intro HNP.
       apply HNP. simpl. easy.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_sN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 P Q Heq3); intro HNS.
       apply HNS.
       rewrite eqb_neq in Heq2.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_lN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s l4 s0 s4 a 1 P Q ); intro HNL.
       apply HNL.
       easy.
       admit.
       
       generalize dependent Q.
       rewrite apend_an.
       intro Q.
       generalize dependent P.
       rewrite(siso_eq((merge_cp_cont p (cp_receive q n s s0) (p & [(l, s1, w1)])))).
       simpl.
       intro P.
       rewrite apend_an in Hw2a.
       simpl in Hw2a.
       specialize(classic (CoNInR (q, rcv) (act w2))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       specialize (n_inpN {| und := (p & [(l, s1, w1)]); sprop := Hs1 |} {| und := w2; sprop := Q |} q s s0 P); intros HH.
       unfold und in HH.
       simpl in HH. apply HH. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (q, rcv) (act w2) -> CoInR (q, rcv) (act w2)) as Hin by admit.
       apply Hin in Hclass.
       specialize(inReceive w2 q Q Hclass); intros HHin.
       destruct HHin as (c4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.
       case_eq(isInCp q c4); intros.
       assert(singleton w4) as Hs4.
       { apply extcpR, extrR in Q.
         easy.
       }
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       specialize(n_i_o_2N (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs4) q s l4 s0 s4 c4 P Q); intros HN2.
       apply HN2. easy.
       specialize(cpap q c4 (q & [(l4, s4, w4)]) H); intros Hpc.
       destruct Hpc as (a, Hpc).
       generalize dependent Q.
       rewrite Hpc.
       intros Q.

       case_eq(eqb l4 s); intros Heq2.
       rewrite eqb_eq in Heq2.
       subst.
       specialize(sort_dec s4 s0); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
(*        rewrite Heqw4 in Hw2a. *)
       rewrite Hpc in Hw2a.
       assert(CoNInR (p, rcv) (act (merge_ap_cont q a w4))) as Hnin by admit.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_ap_cont q a w4)) as Hs3 by admit.
       specialize(n_a_wN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 Hs3 P Q Heq3); intros HNAWN.
       apply HNAWN.
       simpl.
       specialize(n_inpN (mk_siso w1 Hw1) (mk_siso (merge_ap_cont q a w4) Hs3) p l s1); intro HNP.
       apply HNP. simpl. easy.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_sN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 P Q Heq3); intro HNS.
       apply HNS.
       rewrite eqb_neq in Heq2.
       assert(singleton(p & [(l, s1, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_lN (mk_siso (p & [(l, s1, w1)]) Hs1) (mk_siso w4 Hs2) q s l4 s0 s4 a 1 P Q ); intro HNL.
       apply HNL.
       easy.
       admit.
       
       (*inductive step*)
       destruct a.
       
       generalize dependent P.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l, s1, w1)]))).
       generalize dependent Q.
       rewrite(siso_eq(merge_ap_cont q0 (ap_receive q1 n0 s2 s3) w2)).
       simpl.
       intros Q P.
       rewrite(siso_eq(merge_ap_cont q0 (ap_receive q1 n0 s2 s3) w2)) in Hw2a.
       simpl in Hw2a.
       case_eq(eqb q1 q); intros Heq1.
       rewrite eqb_eq in Heq1.
       subst.
       (* by n_inp_wN + ... + IHc and n_inp_sN*)
       admit.
       rewrite eqb_neq in Heq1.
       specialize(classic (CoNInR (q, rcv) (act (q1 & [(s2, s3, w2)])))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       specialize (n_inpN {| und := merge_cp_cont p c (p & [(l, s1, w1)]); sprop := Hs1 |} {| und := q1 & [(s2, s3, w2)]; sprop := Q |} q s s0 P); intros HH.
       unfold und in HH.
       simpl in HH. apply HH. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (q, rcv) (act (q1 & [(s2, s3, w2)])) -> CoInR (q, rcv) (act (q1 & [(s2, s3, w2)]))) as Hin by admit.
       apply Hin in Hclass.
       specialize(inReceive ( q1 & [(s2, s3, w2)]) q Q Hclass); intros HHin.
       destruct HHin as (c4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.
       case_eq(isInCp q c4); intros.
       assert(singleton w4) as Hs4.
       { apply extcpR, extrR in Q.
         easy.
       }
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       specialize(n_i_o_2N (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs4) q s l4 s0 s4 c4 P Q); intros HN2.
       apply HN2. easy.
       specialize(cpap q c4 (q & [(l4, s4, w4)]) H); intros Hpc.
       destruct Hpc as (a, Hpc).
       generalize dependent Q.
       rewrite Hpc.
       intros Q.

       case_eq(eqb l4 s); intros Heq2.
       rewrite eqb_eq in Heq2.
       subst.
       specialize(sort_dec s4 s0); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
       rewrite Heqw4 in Hw2a.
       rewrite Hpc in Hw2a.
       assert(CoNInR (p, rcv) (act (merge_ap_cont q a w4))) as Hnin by admit.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_ap_cont q a w4)) as Hs3 by admit.
       specialize(n_a_wN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 Hs3 P Q Heq3); intros HNAWN.
       apply HNAWN.
       simpl.
       specialize(IHc q a l s1 w1 w4 Hs1 Hs3 Hw1 Hs2 Hnin).
       apply IHc.

       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_sN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 P Q Heq3); intro HNS.
       apply HNS.
       rewrite eqb_neq in Heq2.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_lN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s l4 s0 s4 a 1 P Q ); intro HNL.
       apply HNL.
       easy.
       admit.
       
       generalize dependent P.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l, s1, w1)]))).
       generalize dependent Q.
       rewrite(siso_eq(merge_ap_cont q0 (ap_merge q1 n0 s2 s3 a) w2)).
       simpl. intros Q P.
       rewrite(siso_eq(merge_ap_cont q0 (ap_merge q1 n0 s2 s3 a) w2)) in Hw2a.
       simpl in Hw2a.
       case_eq(eqb q1 q); intros Heq1.
       rewrite eqb_eq in Heq1.
       subst.
       (* by n_inp_wN + ... + IHc and n_inp_sN*)
       admit.
       rewrite eqb_neq in Heq1.
       specialize(classic (CoNInR (q, rcv) (act (q1 & [(s2, s3, merge_ap_cont q0 a w2)])))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       specialize (n_inpN {| und := (merge_cp_cont p c (p & [(l, s1, w1)])); sprop := Hs1 |} 
                          {| und := (q1 & [(s2, s3, merge_ap_cont q0 a w2)]); sprop := Q |} q s s0 P); intros HH.
       unfold und in HH.
       simpl in HH. apply HH. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (q, rcv) (act (q1 & [(s2, s3, merge_ap_cont q0 a w2)])) -> CoInR (q, rcv) (act (q1 & [(s2, s3, merge_ap_cont q0 a w2)]))) as Hin by admit.
       apply Hin in Hclass.
       specialize(inReceive (q1 & [(s2, s3, merge_ap_cont q0 a w2)]) q Q Hclass); intros HHin.
       destruct HHin as (c4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.
       case_eq(isInCp q c4); intros.
       assert(singleton w4) as Hs4.
       { apply extcpR, extrR in Q.
         easy.
       }
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       specialize(n_i_o_2N (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs4) q s l4 s0 s4 c4 P Q); intros HN2.
       apply HN2. easy.
       specialize(cpap q c4 (q & [(l4, s4, w4)]) H); intros Hpc.
       rename a into a1.
       destruct Hpc as (a, Hpc).
       generalize dependent Q.
       rewrite Hpc.
       intros Q.

       case_eq(eqb l4 s); intros Heq2.
       rewrite eqb_eq in Heq2.
       subst.
       specialize(sort_dec s4 s0); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
       rewrite Heqw4 in Hw2a.
       rewrite Hpc in Hw2a.
       assert(CoNInR (p, rcv) (act (merge_ap_cont q a w4))) as Hnin by admit.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_ap_cont q a w4)) as Hs3 by admit.
       specialize(n_a_wN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 Hs3 P Q Heq3); intros HNAWN.
       apply HNAWN.
       simpl.
       specialize(IHc q a l s1 w1 w4 Hs1 Hs3 Hw1 Hs2 Hnin).
       apply IHc.

       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_sN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 P Q Heq3); intro HNS.
       apply HNS.
       rewrite eqb_neq in Heq2.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_lN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s l4 s0 s4 a 1 P Q ); intro HNL.
       apply HNL.
       easy.
       admit.

       generalize dependent P.
       rewrite(siso_eq( (merge_cp_cont p (cp_mergea q n s s0 c) (p & [(l, s1, w1)])))).
       simpl.
       generalize dependent Q.
       rewrite apend_an.
       intros Q P.
       rewrite apend_an in Hw2a.
       simpl in Hw2a.
       specialize(classic (CoNInR (q, rcv) (act w2))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       specialize (n_inpN {| und := (merge_cp_cont p c (p & [(l, s1, w1)])); sprop := Hs1 |} {| und := w2; sprop := Q |} q s s0 P); intros HH.
       unfold und in HH.
       simpl in HH. apply HH. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (q, rcv) (act w2) -> CoInR (q, rcv) (act w2)) as Hin by admit.
       apply Hin in Hclass.
       specialize(inReceive w2 q Q Hclass); intros HHin.
       destruct HHin as (c4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.
       case_eq(isInCp q c4); intros.
       assert(singleton w4) as Hs4.
       { apply extcpR, extrR in Q.
         easy.
       }
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       specialize(n_i_o_2N (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs4) q s l4 s0 s4 c4 P Q); intros HN2.
       apply HN2. easy.
       specialize(cpap q c4 (q & [(l4, s4, w4)]) H); intros Hpc.
       destruct Hpc as (a, Hpc).
       generalize dependent Q.
       rewrite Hpc.
       intros Q.

       case_eq(eqb l4 s); intros Heq2.
       rewrite eqb_eq in Heq2.
       subst.
       specialize(sort_dec s4 s0); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
(*        rewrite Heqw4 in Hw2a. *)
       rewrite Hpc in Hw2a.
       assert(CoNInR (p, rcv) (act (merge_ap_cont q a w4))) as Hnin by admit.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_ap_cont q a w4)) as Hs3 by admit.
       specialize(n_a_wN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 Hs3 P Q Heq3); intros HNAWN.
       apply HNAWN.
       simpl.
       specialize(IHc q a l s1 w1 w4 Hs1 Hs3 Hw1 Hs2 Hnin).
       apply IHc.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_sN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s s0 s4 a 1 P Q Heq3); intro HNS.
       apply HNS.
       rewrite eqb_neq in Heq2.
       assert(singleton(merge_cp_cont p c (p & [(l, s1, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_a_lN (mk_siso (merge_cp_cont p c (p & [(l, s1, w1)])) Hs1) (mk_siso w4 Hs2) q s l4 s0 s4 a 1 P Q ); intro HNL.
       apply HNL.
       easy.
       admit.

       (*sends*)
       generalize dependent P.
       rewrite(siso_eq( merge_cp_cont p (cp_send s s0 s1) (p & [(l, s2, w1)]))).
       simpl. intro P.
       specialize(classic (CoNInR (s, snd) (act (merge_ap_cont q a w2)))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(p & [(l, s2, w1)])) as Hs1 by admit.
       specialize (n_outN {| und := (p & [(l, s2, w1)]); sprop := Hs1 |} {| und := merge_ap_cont q a w2; sprop := Q |} s s0 s1 P); intros HH.
       apply HH.
       simpl. easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (s, snd) (act (merge_ap_cont q a w2)) -> CoInR (s, snd) (act (merge_ap_cont q a w2))) as Hin by admit.
       apply Hin in Hclass.
       specialize(inSend (merge_ap_cont q a w2) s Q Hclass); intros HHin.
       destruct HHin as (b4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.

       case_eq (eqb l4 s0); intro Heq1.
       rewrite eqb_eq in Heq1.
       subst.
       specialize(sort_dec s1 s4); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
       rewrite Heqw4 in Hw2a.
       assert(singleton(p & [(l, s2, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_bp_cont s b4 w4)) as Hs3 by admit.
       specialize(n_b_wN (mk_siso (p & [(l, s2, w1)]) Hs1) (mk_siso w4 Hs2) s s0 s1 s4 b4 1 Hs3 P Q Heq3); intros HNBWN.
       apply HNBWN.
       simpl.
       assert(CoNInR (p, rcv) (act (merge_bp_cont s b4 w4))) as Hnin by admit.
       specialize(n_inpN (mk_siso w1 Hw1) (mk_siso (merge_bp_cont s b4 w4) Hs3) p l s2 Hs1 Hnin); intro HN.
       apply HN.
       assert(singleton(p & [(l, s2, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_b_sN (mk_siso (p & [(l, s2, w1)]) Hs1) (mk_siso w4 Hs2) s s0 s1 s4 b4 1 P Q Heq3); intro HNS.
       apply HNS.
       
       rewrite eqb_neq in Heq1.
       assert(singleton(p & [(l, s2, w1)])) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_b_lN (mk_siso (p & [(l, s2, w1)]) Hs1) (mk_siso w4 Hs2) s s0 l4 s1 s4 b4 1 P Q); intro HNL.
       apply HNL. easy.
       admit.
       
  
       generalize dependent P.
       rewrite(siso_eq((merge_cp_cont p (cp_merge s s0 s1 c) (p & [(l, s2, w1)])))).
       simpl. intro P.
       specialize(classic (CoNInR (s, snd) (act (merge_ap_cont q a w2)))); intro Hclass.
       destruct Hclass as [Hclass | Hclass].
       assert(singleton(merge_cp_cont p c (p & [(l, s2, w1)]))) as Hs1 by admit.
       specialize (n_outN {| und := (merge_cp_cont p c (p & [(l, s2, w1)])); sprop := Hs1 |} {| und := merge_ap_cont q a w2; sprop := Q |} s s0 s1 P); intros HH.
       apply HH.
       easy.
       apply inOutLA_O in Hclass.
       assert(CoIn (s, snd) (act (merge_ap_cont q a w2)) -> CoInR (s, snd) (act (merge_ap_cont q a w2))) as Hin by admit.
       apply Hin in Hclass.

       specialize(inSend (merge_ap_cont q a w2) s Q Hclass); intros HHin.
       destruct HHin as (b4,(l4,(s4,(w4,Heqw4)))).
       generalize dependent Q.
       rewrite Heqw4. intros Q.

       case_eq (eqb l4 s0); intro Heq1.
       rewrite eqb_eq in Heq1.
       subst.
       specialize(sort_dec s1 s4); intro Heq3.
       destruct Heq3 as [Heq3 | Heq3].
       rewrite Heqw4 in Hw2a.
       assert(singleton(merge_cp_cont p c (p & [(l, s2, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       assert(singleton (merge_bp_cont s b4 w4)) as Hs3 by admit.
       specialize(n_b_wN (mk_siso (merge_cp_cont p c (p & [(l, s2, w1)])) Hs1) (mk_siso w4 Hs2) s s0 s1 s4 b4 1 Hs3 P Q Heq3); intros HNBWN.
       apply HNBWN.
       simpl.
       assert(CoNInR (p, rcv) (act (merge_bp_cont s b4 w4))) as Hnin by admit.
       specialize(IHc q (ap_end) l s2 w1 (merge_bp_cont s b4 w4) Hs1 ).
       rewrite apend_an in IHc.
       apply IHc. easy. easy. easy.

       assert(singleton(merge_cp_cont p c (p & [(l, s2, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_b_sN (mk_siso (merge_cp_cont p c (p & [(l, s2, w1)])) Hs1) (mk_siso w4 Hs2) s s0 s1 s4 b4 1 P Q Heq3); intros HNBWN.
       apply HNBWN.
       
       rewrite eqb_neq in Heq1.
       assert(singleton(merge_cp_cont p c (p & [(l, s2, w1)]))) as Hs1 by admit.
       assert(singleton w4) as Hs2 by admit.
       specialize(n_b_lN (mk_siso (merge_cp_cont p c (p & [(l, s2, w1)])) Hs1) (mk_siso w4 Hs2) s s0 l4 s1 s4 b4 1 P Q); intros HNBWN.
       apply HNBWN. easy.
       admit.
       
       generalize dependent P.
       rewrite cpend_an.
       intro P.

       specialize(n_inpN (mk_siso w1 Hw1) (mk_siso (merge_ap_cont q a w2) Q)); intros HN.
       apply HN. easy.
Admitted.

Lemma n_a_actN: forall p a l s s' w w' P Q,
  subsort s' s ->
  (act_neq w (merge_ap_cont p a w')) ->
  nRefinementN (mk_siso (p & [(l,s,w)]) P)
               (mk_siso (merge_ap_cont p a (p & [(l,s',w')])) Q).
Proof. intros.
       unfold act_neq in H0.
       destruct H0 as (a1, H0).
       destruct H0 as [H0 | H0].
       destruct a1 as (q,ac).
       destruct H0 as (Ha,Hb).
       case_eq ac; intros.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inReceive w q Hw Ha); intros.
         destruct H0 as (c1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hw.
         subst.
         intros Hw Hn.
         apply n_a_actNH1.
         assert(singleton w1) as Hw1.
         { clear Hn. apply extrR, extcpR, extrR in P. easy. }
         easy. easy. easy.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inSend w q Hw Ha); intros.
         destruct H0 as (b1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hw.
         subst.
         intros Hw Hn.
         apply n_a_actNH2.
         assert(singleton w1) as Hw1.
         {  clear Hn. apply extrR, extbpR, extsR in P. easy. }
         easy. easy. easy.
       destruct a1 as (q,ac).
       destruct H0 as (Ha,Hb).
       case_eq ac; intros.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inReceive (merge_ap_cont p a w') q Hpw' Ha); intros.
         destruct H0 as (c1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hpw'.
         rewrite IHw1.
         intros IHw' Hn.
         specialize (n_a_actNH3 q c1 p (ap_end) l1 s1 w1 w IHw'); intros IHn3.
         simpl in IHn3.
         rewrite apend_an in IHn3.
         apply IHn3.
         assert(singleton w1) as Hw1.
         {  clear IHn3 Hn. apply extcpR, extrR in IHw'. easy. }
         easy. easy. easy.
       + subst.
         assert(singleton w) as Hw.
         { apply extrR in P. easy. }
         assert(singleton w') as Hw'.
         { apply extapR, extrR in Q. easy. }
         assert(singleton (merge_ap_cont p a w')) as Hpw'.
         { apply extap. easy. }
         specialize(n_a_wN (mk_siso w Hw) (mk_siso w' Hw') p l s s' a 1 Hpw' P Q H); intro Hn.
         apply Hn.
         simpl in *.
         specialize(inSend (merge_ap_cont p a w') q Hpw' Ha); intros.
         destruct H0 as (b1,(l1,(s1,(w1,IHw1)))).
         generalize dependent Hpw'.
         rewrite IHw1.
         intros IHw' Hn.
         specialize (n_a_actNH4 q b1 p (ap_end) l1 s1 w1 w IHw'); intros IHn3.
         simpl in IHn3.
         rewrite apend_an in IHn3.
         apply IHn3.
         assert(singleton w1) as Hw1.
         {  clear IHn3 Hn. apply extbpR, extsR in IHw'. easy. }
         easy. easy. easy.
Qed.

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

         specialize(classic (CoNInR (p, snd) (act (q ! [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outN {| und := w1; sprop := Hs1 |} {| und := q ! [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.
         unfold not in Hclass.

         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, snd) (act (q ! [(l', s', w2)])) -> CoInR (p, snd) (act (q ! [(l', s', w2)]))) as Hpr by admit.
         apply Hpr in Hclass.
         specialize(inSend (q ! [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (b,(l1,(s1,(w3,IHw3)))).
         rewrite IHw3.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s s1); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(classic (act_eq w1 ((merge_bp_cont p b w3)))); intro Hact.
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
         apply act_eq_neq in Hact.
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
         specialize (act_dec u2 v2); intro Hstr.
         destruct Hstr. 
         apply act_eqb_eq in H.
         subst.
         left. easy. 
         right. unfold not in *. intro Hss.
         apply act_neqb_neq in H.
         apply H. inversion Hss. easy.
         right. unfold not in *. intro Hss. apply n. inversion Hss. easy.

         destruct Hpw' as [Hpw' | Hpw'].
         destruct Hpw' as (q, (l', (s', (w2, (Heq2, Hs2))))).
         subst.

(*****)
         specialize(classic (CoNInR (p, snd) (act (q & [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_outN {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.

         unfold not in Hclass.
         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, snd) (act (q & [(l', s', w2)])) -> CoInR (p, snd) (act (q & [(l', s', w2)]))) as Hpr by admit.
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
         specialize(classic (act_eq w1 ((merge_bp_cont p b w3)))); intro Hact.
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
         apply act_eq_neq in Hact.
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
         specialize (act_dec u2 v2); intro Hstr.
         destruct Hstr. subst.
         left. apply act_eqb_eq in H. subst. easy. 
         right. unfold not in *. intro Hss.
         apply act_neqb_neq in H. apply H. inversion Hss. easy.
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

         specialize(classic (CoNInR (p, rcv) (act (q & [(l', s', w2)])))); intro Hclass.
         destruct Hclass as [Hclass | Hclass].
         destruct H0.
         specialize (n_inpN {| und := w1; sprop := Hs1 |} {| und := q & [(l', s', w2)]; sprop := Pw' |} p l s ); intros HH.
         simpl in HH. apply HH. easy.

         unfold not in Hclass.
         apply inOutLA_O in Hclass.
         unfold CoIn in Hclass.
         punfold Hclass.
         assert(CoInRA (upaco2 CoInRA bot2) (p, rcv) (act (q & [(l', s', w2)])) -> CoInR (p, rcv) (act (q & [(l', s', w2)]))) as Hpr by admit.
         apply Hpr in Hclass.

         specialize(inReceive (q & [(l', s', w2)]) p Pw' Hclass); intros.
         destruct H as (c,(l1,(s1,(w3,IHw3)))).
         generalize dependent Pw'.
         rewrite IHw3.
         intros Pw' H0.

         case_eq(isInCp p c); intros.
         destruct H0.
         assert(singleton w3) as Hs3.
         { apply extcpR, extrR in Pw'.
           easy.
         }
         specialize(n_i_o_2N (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 c Pw Pw'); intros HN2.
         apply HN2. easy.
         
         specialize(cpap p c (p & [(l1, s1, w3)]) H); intros Hpc.
         destruct Hpc as (a, Hpc).
         generalize dependent Pw'.
         rewrite Hpc.
         intros Pw' H0.

         case_eq(eqb l l1); intro Heq2.
         rewrite eqb_eq in Heq2. subst.
         specialize(sort_dec s1 s); intro Heq3.
         destruct Heq3 as [Heq3 | Heq3].
         pfold.
         specialize(classic (act_eq w1 ((merge_ap_cont p a w3)))); intro Hact.
         destruct Hact as [Hact | Hact].
         specialize(_sref_a (upaco2 refinementR r) w1 w3 p l1 s1 s a 1 Heq3); intro Hrb.
         simpl in Hrb.
         apply Hrb.

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
         apply act_eq_neq in Hact.
         specialize(n_a_actN p a l1 s s1 w1 w3 Pw Pw'); intros HN.
         apply HN. easy. easy.

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
         assert(singleton w3) as Hs3.
         { specialize (@extapR p a (p & [(l1, s1, w3)]) Pw'); intros Hss.
           specialize (@extrR p l1 s1 w3 Hss); intros Hss2.
           easy. 
         }
         specialize (n_a_lN (mk_siso w1 Hs1) (mk_siso w3 Hs3) p l l1 s s1 a 1 Pw Pw'); intros Hn.
         apply Hn. easy.
(***********)

         apply CoIn_mon.
         intros (u1,u2) (v1,v2).
         specialize (string_dec u1 v1); intro Hstr.
         destruct Hstr. subst.
         specialize (act_dec u2 v2); intro Hstr.
         destruct Hstr. subst.
         left. apply act_eqb_eq in H. subst. easy. 
         right. unfold not in *. intro Hss.
         apply act_neqb_neq in H.
         apply H. inversion Hss. easy.
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


