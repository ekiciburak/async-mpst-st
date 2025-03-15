From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.src.st ST.types.local.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Inductive st2si (R: st -> st -> Prop): st -> st -> Prop :=
  | st2si_end: st2si R st_end st_end
  | st2si_rcv: forall l s x xs y p,
               R x y ->
               copathsel l s xs y ->
               st2si R (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2si_snd: forall p xs ys,
               Forall2C (fun u v => exists l s t l' s' t', u = (l,s,t) /\ v = (l',s',t') /\ R t t') ys xs ->
               st2si R (st_send p ys) (st_send p xs).

Definition st2siC s1 s2 := paco2 (st2si) bot2 s1 s2.

Lemma st2so_mon: monotone2 st2si.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2si_end.
       - specialize (st2si_rcv r'); intro HS.
         apply HS with (y := y). apply LE. easy. easy.
       - specialize (st2si_snd r'); intro HS.
         apply HS. 
         apply monH2 with (r := r); easy.
Qed.
