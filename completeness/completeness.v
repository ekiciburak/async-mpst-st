Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si 
               ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping 
               ST.negations.nrefinement ST.negations.nsubtyping.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

(* completeness for the main relation *)
Lemma sublNeqL: forall T T', (subltypeI T T' -> False) -> nsubltypeI T T'.
Proof. intros.
       apply subNeqIL. easy.
Qed.

Lemma sublNeqR: forall T T', nsubltypeI T T' -> (subltypeI T T' -> False).
Proof. intros.
       apply subNeqIR with (T := lt2st T) (T' := lt2st T'); easy.
Qed.

Theorem completenessI: forall T T', (subtypeI T T' -> False) <-> nsubtypeI T T'.
Proof. split.
       apply (subNeqIL T T').
       intros. apply (subNeqIR T T'); easy.
Qed.

Theorem lcompletenessI: forall T T', (subltypeI T T' -> False) <-> nsubltypeI T T'.
Proof. split; [ apply (sublNeqL T T') | intros; apply (sublNeqR T T'); easy]. Qed.

(* (* completemess for the relation proving actual examples *)

Lemma subNeqLA: forall T T', (subtype T T' -> False) -> nsubtype T T'.
Proof. unfold subtype, nsubtype in *.
       intros.
       apply trivL2.
       intros.
       apply H. exists l. split; easy.
Qed.

Lemma subNeqRA: forall T T', nsubtype T T' -> (subtype T T' -> False).
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H0 as (l, H0).
       specialize(H l).
       apply (trivL1 l). easy.
       apply H. apply H0.
Qed.

Theorem lcompleteness: forall T T', (subltype T T' -> False) <-> nsubltype T T'.
Proof. split.
       apply (subNeqLA T T').
       intros. apply (subNeqRA T T'); easy.
Qed. *)


 