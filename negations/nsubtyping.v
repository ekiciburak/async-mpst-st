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

Locate extdpn.

Fixpoint listSisoNRef (l: list (siso*siso)): Prop :=
  match l with
    | nil            => False
    | cons (W,W') xs => (forall d1, forall d2, (exists n, (nRefinement (mk_siso (merge_dpf_contn d1 (@und W) n) (extdpfn (@und W) (@sprop W)))
                                                                       (mk_siso (merge_dpf_contn d2 (@und W') n) (extdpfn (@und W') (@sprop W'))))))
                        \/ listSisoNRef xs
  end.

Definition nsubtype (T T': st): Prop := forall (l: list (siso*siso)), decomposeL l T T' -> listSisoNRef l.

(* Definition nsubltype (T T': local) (T1 T2: st) (P: lt2stC T T1) (Q: lt2stC T' T2 ) := nsubtype T1 T2. *)

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
         rewrite <- !meqDpf in H, H0. easy.
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
         specialize (nRefR ({| und := merge_dpf_contn d1 w n; sprop := extdpfn w Hw |}) ( {| und := merge_dpf_contn d2 w' n; sprop := extdpfn w' Hw' |})); intros.
         apply H. easy.
         easy.
         apply IHl. easy. easy.
Qed.

Definition subtype3 (T T': st): Prop :=
  forall U, st2soC U T /\ 
  forall V', st2siC V' T'/\
  exists (W: siso), st2sisoC (@und W) U /\
  exists (W':siso), st2sisoC (@und W') V' /\ (@und W) ~< (@und W').

Definition nsubtype3 (T T': st): Prop :=
  exists U,  (st2soC U T) ->
  exists V', (st2siC V' T') ->
  forall W,  (st2sisoC (@und W) U) ->
  forall W', (st2sisoC (@und W') V') -> nRefinement W W'.

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

Definition subltype3 (T T': local): Prop := subtype3 (lt2st T) (lt2st T').

Definition nsubltype3 (T T': local): Prop := nsubtype3 (lt2st T) (lt2st T').

Lemma sublNeq3L: forall T T', (subltype3 T T' -> False) -> nsubltype3 T T'.
Proof. intros.
       unfold subltype3, nsubltype3 in *.
       apply subNeq3L. easy.
Qed.

Lemma sublNeq3R: forall T T', nsubltype3 T T' -> (subltype3 T T' -> False).
Proof. intros.
       unfold subltype3, nsubltype3 in *.
       apply subNeq3R with (T := lt2st T) (T' := lt2st T'); easy.
Qed.

(*npc*)
Inductive subtypeI: st -> st -> Prop :=
  | stc: forall T T', (forall U, st2soC U T -> forall V', st2siC V' T' -> (exists W W', st2sisoC (@und W) U -> st2sisoC (@und W') V' -> (@und W) ~< (@und W'))) ->
                      subtypeI T T'.

Definition nsubtypeI (T T': st): Prop :=
  exists U,  (st2soC U T) /\
  exists V', (st2siC V' T') /\
  (forall W W', st2sisoC (@und W) U /\ st2sisoC (@und W') V' /\ nRefinement W W').

Lemma subNeqIR: forall T T', subtypeI T T' -> (nsubtypeI T T' -> False).
Proof. intros.
       unfold nsubtypeI in *.
       destruct H0 as (U,(Ha,(V',(Hb,Hc)))).
       inversion H.
       subst.
       specialize(H0 U Ha V' Hb).
       destruct H0 as (W,(W',Hd)).
       specialize(Hc W W').
       destruct Hc as (Hc,(He,Hf)).
       specialize(Hd Hc He).
       apply (nRefR W W'); easy.
Qed.

Lemma nexfl: forall (X: Type) (P: X -> Prop),
  ~ (exists (x: X), P x) -> (forall (x: X), ~P x).
Proof. intros X P H x.
       unfold not in *.
       intro px.
       apply H.
       exists x.
       exact px.
Qed.

Lemma dne: forall (P: Prop), ((P -> False) -> False) -> P.
Proof. intros.
       specialize (classic P).
       intro HP.
       destruct HP as [ HP | HP ].
       - exact HP.
       - unfold not in *.
         specialize (H HP).
         contradiction.
Qed.

Lemma subNeqIL: forall T T', (subtypeI T T' -> False) -> nsubtypeI T T'.
Proof. intros.
       specialize(classic (nsubtypeI T T')); intro Heq.
       destruct Heq as [Heq | Heq].
       - easy.
       - destruct H.
         unfold nsubtypeI in *.
         unshelve econstructor.
         intros.
         eapply nexfl with (x := U) in Heq.
         apply not_and_or in Heq.
         destruct Heq as [Heq | Heq].
         easy.
         eapply nexfl with (x := V') in Heq.
         apply not_and_or in Heq.
         destruct Heq as [Heq | Heq].
         easy.
         apply not_all_ex_not  in Heq.
         destruct Heq as (W, Heq).
         apply not_all_ex_not  in Heq.
         destruct Heq as (W', Heq).
         exists W. exists W'.
         intros.
         apply not_and_or in Heq.
         destruct Heq as [Ha | Heq].
         easy.
         apply not_and_or in Heq.
         destruct Heq as [Ha | Heq].
         easy.
         apply nRefLH.
         easy.
Qed.

Inductive subtypeI2: st -> st -> Prop :=
  | stc2: forall T T', (forall U, st2soC U T -> forall V', st2siC V' T' -> (exists W W', st2sisoC (@und W) U /\ st2sisoC (@und W') V' /\ (@und W) ~< (@und W'))) ->
                      subtypeI2 T T'.

Definition nsubtypeI2 (T T': st): Prop :=
  exists U,  (st2soC U T) /\
  exists V', (st2siC V' T') /\
  (forall W W', st2sisoC (@und W) U -> st2sisoC (@und W') V' -> nRefinement W W').

Lemma subNeqIR2: forall T T', subtypeI2 T T' -> (nsubtypeI2 T T' -> False).
Proof. intros.
       unfold nsubtypeI2 in *.
       destruct H0 as (U,(Ha,(V',(Hb,Hc)))).
       inversion H.
       subst.
       specialize(H0 U Ha V' Hb).
       destruct H0 as (W,(W',(Hd,(He,Hf)))).
       specialize(Hc W W').
       specialize(Hc Hd He).
       apply (nRefR W W'); easy.
Qed.

Lemma subNeqIL2: forall T T', (subtypeI2 T T' -> False) -> nsubtypeI2 T T'.
Proof. intros.
       specialize(classic (nsubtypeI2 T T')); intro Heq.
       destruct Heq as [Heq | Heq].
       - easy.
       - destruct H.
         unfold nsubtypeI2 in *.
         unshelve econstructor.
         intros.
         eapply nexfl with (x := U) in Heq.
         apply not_and_or in Heq.
         destruct Heq as [Heq | Heq].
         easy.
         eapply nexfl with (x := V') in Heq.
         apply not_and_or in Heq.
         destruct Heq as [Heq | Heq].
         easy.
         apply not_all_ex_not  in Heq.
         destruct Heq as (W, Heq).
         apply not_all_ex_not  in Heq.
         destruct Heq as (W', Heq).
         exists W. exists W'.
         intros.
         
         apply imply_to_and in Heq.
         split. easy.
         destruct Heq as (Hn1, Heq).
         apply imply_to_and in Heq.
         split. easy.
         destruct Heq as (Hn2, Heq).
         apply nRefLH.
         easy.
Qed.
  
Definition subltypeI2 (T T': local): Prop := subtypeI2 (lt2st T) (lt2st T').

Definition nsubltypeI2 (T T': local): Prop := nsubtypeI2 (lt2st T) (lt2st T').

Lemma sublNeqL: forall T T', (subltypeI2 T T' -> False) -> nsubltypeI2 T T'.
Proof. intros.
       apply subNeqIL2. easy.
Qed.

Lemma sublNeqR2: forall T T', nsubltypeI2 T T' -> (subltypeI2 T T' -> False).
Proof. intros.
       apply subNeqIR2 with (T := lt2st T) (T' := lt2st T'); easy.
Qed.





