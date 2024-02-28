Require Import ST.src.stream ST.src.st ST.src.so ST.src.si 
               ST.src.reordering ST.src.siso 
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping 
               ST.negations.nrefinement ST.negations.nsubtyping.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Lemma subNeqR: forall T T', nsubtype T T' -> (subtype T T' -> False).
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H as (U, H).
       specialize(H0 U).
       destruct H0 as (p, Ha).
       specialize(H p).
       destruct H as (V', H).
       specialize(Ha V').
       destruct Ha as (q, Ha).
       specialize(H q).
       destruct Ha as (W, Ha).
       destruct Ha as (r, Ha).
       specialize(H W r).
       destruct Ha as (W', Ha).
       destruct Ha as (s, Ha).
       specialize(H W' s).
       apply (nRefR W W'); easy.
Qed.

Lemma subNeqL: forall T T', (subtype T T' -> False) -> nsubtype T T'.
Proof. intros.
       unfold subtype, nsubtype in *.
       apply not_all_ex_not in H.
       destruct H as (U, H).
       exists U.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Ha. easy.

       apply not_all_ex_not in H.
       destruct H as (V', H).
       intro Ha.
       exists V'.
       intro Hb. 
       apply not_and_or in H.
       destruct H as [H | H].
       easy.
       intro W.
       apply not_ex_all_not with (n := W) in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hc. easy.
       intros Hc W'.
       apply not_ex_all_not with (n := W') in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hd. easy.
       intro Hd.
       apply nRefL. easy.
Qed.

Theorem completeness: forall T T', (subtype T T' -> False) <-> nsubtype T T'.
Proof. split.
       apply (subNeqL T T').
       intros. apply (subNeqR T T'); easy.
Qed.

