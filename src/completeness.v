Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.refinement ST.src.reorderingfacts ST.src.subtyping ST.src.nrefinement ST.src.nsubtyping.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Lemma subneqL: forall T T', subtype T T' -> nsubtype T T' -> False.
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H0 as (U, H0).
       specialize(H U).
       destruct H0 as [H0 | H0].
       destruct H as (H, Ha).
       easy.
       destruct H as (Ha, H).
       destruct H0 as (V', H0).
       specialize(H V').
       destruct H as (Hb, H).
       destruct H0 as [H0 | H0].
       easy.
       destruct H as (W, H).
       specialize(H0 W).
       destruct H as (Hc, H).
       destruct H0 as [H0 | H0].
       easy.
       destruct H as (W', H).
       destruct H as (Hd, H).
       specialize(H0 W').
       destruct H0 as [H0 | H0].
       easy.
       apply (nrefNL W W'); easy.
Qed.

Lemma subneqR: forall T T', (subtype T T' -> False) -> nsubtype T T'.
Proof. intros.
       unfold subtype, nsubtype in *.
       apply not_all_ex_not in H.
       destruct H as (U, H).
       exists U.
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       apply not_all_ex_not in H.
       destruct H as (V', H).
       right. exists V'. 
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       right. intro W.
       apply not_ex_all_not with (n := W) in H.
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       right. intro W'.
       apply not_ex_all_not with (n := W') in H.
       apply not_and_or in H.
       destruct H as [H | H].
       left. easy.
       right. apply nrefNR. easy.
Qed.

Theorem completeness: forall T T', (subtype T T' -> False) <-> nsubtype T T'.
Proof. split.
       apply (subneqR T T').
       intros. apply (subneqL T T'); easy.
Qed.
