Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts 
               ST.subtyping.subtyping ST.negations.nrefinement.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Definition nsubtype (T T': st): Prop :=
  exists U,  (st2soC U T) /\
  exists V', (st2siC V' T') /\
  (forall W W', st2sisoC (@und W) U /\ st2sisoC (@und W') V' /\ nRefinement W W').

Definition nsubltype (T T': local): Prop := nsubtype (lt2st T) (lt2st T').

Lemma subNeqR: forall T T', subtype T T' -> (nsubtype T T' -> False).
Proof. intros.
       unfold nsubtype in *.
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

Lemma subNeqL: forall T T', (subtype T T' -> False) -> nsubtype T T'.
Proof. intros.
       specialize(classic (nsubtype T T')); intro Heq.
       destruct Heq as [Heq | Heq].
       - easy.
       - destruct H.
         unfold nsubtype in *.
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

Lemma sublNeqL: forall T T', (subltype T T' -> False) -> nsubltype T T'.
Proof. intros.
       apply subNeqL. easy.
Qed.

Lemma sublNeqR: forall T T', nsubltype T T' -> (subltype T T' -> False).
Proof. intros.
       apply subNeqR with (T := lt2st T) (T' := lt2st T'); easy.
Qed.