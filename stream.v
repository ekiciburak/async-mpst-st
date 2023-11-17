
From Paco Require Import paco.
Require Import Setoid.
Require Import Morphisms.

Inductive colistF (a : Type) (x : Type) :=
  | conil : colistF a x
  | cocons: a -> x -> colistF a x.

CoInductive coseq (a : Type) : Type :=
  Delay
  {
    force: colistF a (coseq a) 
  }.

Arguments force {_} _.
Arguments conil { _ _ } .
Arguments cocons { _ _ } _ _.
Arguments Delay {_} _.

Inductive optionF (a : Type) :=
  | none: optionF a
  | some: a -> optionF a.

CoInductive cooption (a : Type) : Type :=
  DelayO
  {
    forceO: optionF (coseq a) 
  }.

Arguments none {_}.
Arguments some {_} _.
Arguments DelayO {_} _.

Definition coseq_id {A: Type} (s: coseq A): coseq A :=
  Delay
  match force s with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Lemma coseq_eq: forall {A} s, s = @coseq_id A s.
Proof. intros A s.
       unfold coseq_id.
       destruct s.
       simpl.
       destruct force0; easy.
Qed.

CoFixpoint nats_from (n : nat) : coseq nat := 
  Delay (cocons n (nats_from (S n))).

CoFixpoint map {A B: Type} (f: A -> B) (xs: coseq A): coseq B := 
  Delay
  match force xs with
    | conil       => conil
    | cocons x xs => cocons (f x) (map f xs)
  end.

Inductive CoIn {A: Type} (x: A) (xs: coseq A) : Prop :=
  | CoInSplit y ys : force xs = cocons y ys -> x = y \/ CoIn x ys -> CoIn x xs.

Inductive sseq_gen {A: Type} (seq: coseq A -> coseq A -> Prop): coseq A -> coseq A -> Prop :=
  | _sseq_gen_n: sseq_gen seq (Delay conil) (Delay conil)
  | _sseq_gen_c: forall n s1 s2 (R: seq s1 s2), sseq_gen seq (Delay (cocons n s1)) (Delay (cocons n s2))
  | _sseq_set  : forall n m s1 s2, 
                 sseq_gen seq (Delay (cocons m (Delay (cocons n s1)))) (Delay (cocons m (Delay (cocons n s2)))) ->
                 sseq_gen seq (Delay (cocons n (Delay (cocons m s1)))) (Delay (cocons m (Delay (cocons n s2)))).

Definition sseq {A} s1 s2 := paco2 (@sseq_gen A) bot2 s1 s2.
