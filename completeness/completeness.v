Require Import ST.src.stream ST.src.st ST.src.so ST.src.si 
               ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping 
               ST.negations.nrefinement ST.negations.nsubtyping.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Lemma refComplete: forall w w', ((@und w) ~< (@und w') -> False) <-> nRefinement w w'.
Proof. split.
       apply nRefL.
       apply nRefR.
Qed.

Theorem completeness: forall T T', (subtype T T' -> False) <-> nsubtype T T'.
Proof. split.
       apply (subNeqL T T').
       intros. apply (subNeqR T T'); easy.
Qed.

Theorem lcompletenessI: forall T T', (subltype T T' -> False) <-> nsubltype T T'.
Proof. split.
       apply (sublNeqL T T').
       intros. apply (sublNeqR T T'); easy.
Qed.