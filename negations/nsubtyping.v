Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts 
               ST.subtyping.subtyping ST.negations.nrefinement.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Fixpoint listSisoNRef (l: list (siso*siso)): Prop :=
  match l with
    | nil            => False
    | cons (W,W') xs => (forall d1, forall d2, (exists n, (nRefinement (mk_siso (merge_dp_contn d1 (@und W) n) (extdpn (@und W) (@sprop W)))
                                                                       (mk_siso (merge_dp_contn d2 (@und W') n) (extdpn (@und W') (@sprop W'))))))
                        \/ listSisoNRef xs
  end.

Definition nsubtype (T T': st): Prop := forall (l: list (siso*siso)), decomposeL l T T' -> listSisoNRef l.

Definition nsubltype (T T': local) (T1 T2: st) (P: lt2stC T T1) (Q: lt2stC T' T2 ) := nsubtype T1 T2.

Lemma trivL2:  forall l, (listSisoPRef2 l -> False) -> listSisoNRef l.
Proof. intro l.
       induction l; intros.
       - simpl in *. easy.
       - simpl in *. destruct a as (W, W').
         destruct W as (w, Hw).
         destruct W' as (w', Hw').
         apply not_and_or in H.
         destruct H as [H| H].
         left.
         intros d1 d2.
         apply not_ex_all_not with (n := d1) in H.
         apply not_ex_all_not with (n := d2) in H.
         apply not_all_ex_not in H.
         destruct H as (n, H).
         exists n.
         apply nRefL.
         intros.
         apply H.
         simpl in *.
         rewrite <- !meqDp in H, H0. easy.
         right.
         apply IHl. easy.
Qed.

Lemma trivL1: forall l, listSisoPRef2 l -> listSisoNRef l -> False.
Proof. intro l.
       induction l; intros.
       - simpl in *. easy.
       - simpl in *. destruct a as (W, W').
         destruct W as (w, Hw).
         destruct W' as (w', Hw').
         destruct H as ((d1,(d2,Ha)), Hb).
         destruct H0 as [H0 | H0].
         specialize(H0 d1 d2).
         destruct H0 as (n, H0).
         specialize(Ha n).
         simpl in H0.
         specialize (nRefR ({| und := merge_dp_contn d1 w n; sprop := extdpn w Hw |}) ( {| und := merge_dp_contn d2 w' n; sprop := extdpn w' Hw' |})); intros.
         apply H. easy.
         easy.
         apply IHl. easy. easy.
Qed.

(*talk*)
Definition subtype3 (T T': st): Prop :=
  forall U, st2soC T U /\ 
  forall V', st2siC T' V' /\
  exists (W: siso), st2sisoC U  (@und W) /\
  exists (W':siso), st2sisoC V' (@und W') /\ (@und W) ~< (@und W').

Definition nsubtype3 (T T': st): Prop :=
  exists U,  (st2soC T U) ->
  exists V', (st2siC T' V') ->
  forall W,  (st2sisoC U (@und W)) ->
  forall W', (st2sisoC V' (@und W')) -> nRefinement W W'.

Lemma subNeq3L: forall T T', (subtype3 T T' -> False) -> nsubtype3 T T'.
Proof. intros.
       unfold subtype3, nsubtype3 in *.
       apply not_all_ex_not in H.
       destruct H as (U, H).
       exists U.
       intro Ha.
       apply not_and_or in H.
       destruct H as [H | H].
       easy.
       apply not_all_ex_not in H.
       destruct H as (V', H).
       exists V'. 
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hb.
       easy.
       intros Hb W.
       apply not_ex_all_not with (n := W) in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hc.
       easy.
       intros Hc W'.
       apply not_ex_all_not with (n := W') in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hd. easy.
       intro Hd.
       apply nRefL. easy.
Qed.

Lemma subNeq3R: forall T T', nsubtype3 T T' -> (subtype3 T T' -> False).
Proof. intros.
       unfold subtype3, nsubtype3 in *.
       rename H into Ha.
       rename H0 into H.
       rename Ha into H0.
       destruct H0 as (U, H0).
       specialize(H U).
       destruct H as (p, Ha).
       specialize(H0 p).
       destruct H0 as (V', H0).
       specialize(Ha V').
       destruct Ha as (q, Ha).
       specialize(H0 q).
       destruct Ha as (W, Ha).
       destruct Ha as (r, Ha).
       specialize(H0 W r).
       destruct Ha as (W', Ha).
       destruct Ha as (s, Ha).
       specialize(H0 W' s).
       apply (nRefR W W'); easy.
Qed.

