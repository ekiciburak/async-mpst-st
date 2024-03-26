Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si 
               ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping 
               ST.negations.nrefinement ST.negations.nsubtyping.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Lemma subNeqL: forall T T', (subtype2 T T' -> False) -> nsubtype T T'.
Proof. intros.
       unfold subtype2, nsubtype in *.
       intro l.
       apply not_ex_all_not with (n := l) in H.
       apply not_and_or in H.
       intro Ha.
       destruct H as [H | H]. easy.
       apply trivL2. easy.
Qed.

Lemma subNeqR: forall T T', nsubtype T T' -> (subtype2 T T' -> False).
Proof. intros.
       unfold subtype2, nsubtype in *.
       destruct H0 as (l, H0).
       specialize(H l).
       apply (trivL1 l). easy.
       apply H. apply H0.
Qed.

Theorem completeness: forall T T', (subtype2 T T' -> False) <-> nsubtype T T'.
Proof. split.
       apply (subNeqL T T').
       intros. apply (subNeqR T T'); easy.
Qed.

