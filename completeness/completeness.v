Require Import ST.src.stream ST.src.st ST.src.so ST.src.si 
               ST.src.reordering ST.src.siso 
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping 
               ST.negations.nrefinement ST.negations.nsubtyping.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Lemma subNeqR: forall T T', nsubtype T T' -> (subtype2 T T' -> False).
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H0 as (W, (Ha, (W',(Hb,Hc)))).
       specialize(H W Ha W' Hb).
       apply (nRefR W W'); easy.
Qed.

Lemma subNeqL: forall T T', (subtype2 T T' -> False) -> nsubtype T T'.
Proof. intros.
       unfold subtype, nsubtype in *.
       intro W.
       apply not_ex_all_not with (n := W) in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Ha. easy.
       intros Ha W'.
       apply not_ex_all_not with (n := W') in H.
       apply not_and_or in H.
       destruct H as [H | H].
       intro Hb. easy.
       intro Hb.
       apply nRefL. easy.
Qed.

Theorem completeness: forall T T', (subtype2 T T' -> False) <-> nsubtype T T'.
Proof. split.
       apply (subNeqL T T').
       intros. apply (subNeqR T T'); easy.
Qed.
