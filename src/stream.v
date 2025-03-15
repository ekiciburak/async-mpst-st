From Paco Require Import paco.
Require Import Setoid List.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

(* Inductive colistF (a : Type) (x : Type) :=
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
 *)
 
CoInductive coseq (a : Type) :=
  | conil : coseq a
  | cocons: a -> coseq a -> coseq a.

Arguments conil { _ } .
Arguments cocons { _ } _ _.

(* Inductive optionF (a : Type) :=
  | none: optionF a
  | some: a -> optionF a.

CoInductive cooption (a : Type) : Type :=
  DelayO
  {
    forceO: optionF a
  }.

Arguments none {_}.
Arguments some {_} _.
Arguments DelayO {_} _.
Arguments cooption {_}.
 *)
 
Definition coseq_id {A: Type} (s: coseq A): coseq A :=
  match s with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Lemma coseq_eq: forall {A} s, s = @coseq_id A s.
Proof. intros A s.
       unfold coseq_id.
       destruct s.
       simpl. easy. easy.
Qed.

(* Definition stream_id {A: Type} (s: stream A): stream A :=
  match s with
    | conils       => conils
    | coconss x xs => coconss x xs
  end.

Lemma stream_eq: forall {A} s, s = @stream_id A s.
Proof. intros A s.
       unfold stream_id.
       destruct s; easy.
Qed.

Fixpoint conth {A: Type} (s: coseq A) (n: nat): option A :=
  match n with
    | O   => 
      match force s with
        | conil       => None
        | cocons x xs => Some x
      end 
    | S k =>
      match force s with
        | conil       => None
        | cocons x xs => conth xs k
      end
  end.

CoFixpoint nats_from (n : nat) : coseq nat := 
  Delay (cocons n (nats_from (S n))). *)

CoFixpoint comap {A B: Type} (f: A -> B) (xs: coseq A): coseq B := 
  match xs with
    | conil       => conil
    | cocons x xs => cocons (f x) (comap f xs)
  end.

CoFixpoint cozip {A B: Type} (xs: coseq A) (ys: coseq B): coseq (A*B) := 
  match xs, ys with
    | cocons u us, cocons v vs => cocons (u,v) (cozip us vs)
    | _,_                      => conil
  end.

Inductive colen_eq {A B: Type} (R: coseq A -> coseq B -> Prop): coseq A -> coseq B -> Prop :=
  | coconsnseq: forall u us v vs, R us vs -> colen_eq R (cocons u us) (cocons v vs)
  | coconileq : colen_eq R conil conil.

Definition colen_eqC {A B: Type} xs ys := paco2 (@colen_eq A B) bot2 xs ys.

CoFixpoint appendC {A: Type} (l ys: coseq A): coseq A := 
  match l with
    | conil       => ys
    | cocons x xs => (cocons x (appendC xs ys))
  end.

CoFixpoint appendL {A: Type} (l: list A) (ys: coseq A): coseq A := 
  match l with
    | nil       => ys
    | cons x xs => (cocons x (appendL xs ys))
  end.

Print Forall.

Inductive ForallH {A : Type} (P : A -> Prop) (R: coseq A -> Prop) : coseq A -> Prop :=
  | Forall_conil  : ForallH P R conil
  | Forall_cocons : forall x l, P x -> R l -> ForallH P R (cocons x l).

Definition ForallC {A: Type} P xs := paco1 (@ForallH A P) bot1 xs.

Inductive Forall2H {A B : Type} (P : A -> B -> Prop) (R: coseq A -> coseq B -> Prop ) : coseq A -> coseq B -> Prop :=
  | Forall2_conil : Forall2H P R conil conil
  | Forall2_cocons: forall x y l l',
                    P x y -> R l l' -> Forall2H P R (cocons x l) (cocons y l').

Definition Forall2C {A B: Type} P xs ys := paco2 (@Forall2H A B P) bot2 xs ys.

Inductive Forall3H {A B C: Type} (P : A -> B -> C -> Prop) (R: coseq A -> coseq B -> coseq C -> Prop ) : coseq A -> coseq B -> coseq C -> Prop :=
  | Forall3_conil : Forall3H P R conil conil conil
  | Forall3_cocons: forall x y z l l' l'',
                    P x y z -> R l l' l'' -> Forall3H P R (cocons x l) (cocons y l') (cocons z l'').

Definition Forall3C {A B C: Type} P xs ys zs := paco3 (@Forall3H A B C P) bot3 xs ys zs.

Lemma anl: forall {A: Type} xs, @appendC A conil xs = xs.
Proof. intros.
       destruct xs. simpl.
       rewrite(coseq_eq(appendC  conil conil)). simpl. easy.
       rewrite(coseq_eq (appendC conil (cocons a xs))). simpl. easy.
Qed.

Lemma anl2: forall {A: Type} xs, @appendL A nil xs = xs.
Proof. intros.
       destruct xs. simpl.
       simpl.
       rewrite(coseq_eq(appendL nil conil)).
       unfold coseq_id. simpl. easy.
       rewrite(coseq_eq(appendL nil (cocons a xs))). simpl. easy.
Qed.

Lemma app_assoc: forall {A: Type} xs ys zs,
  @appendL A xs (appendL ys zs) = appendL (xs ++ ys) zs.
Proof. intros A xs.
       induction xs; intros.
       simpl. rewrite anl2. easy.
       simpl.
       rewrite(coseq_eq(appendL (a :: xs) (appendL ys zs))).
       unfold coseq_id. simpl.
       rewrite IHxs.
       rewrite(coseq_eq(appendL (a :: xs ++ ys) zs)).
       unfold coseq_id. simpl. easy.
Qed.

(* unsound coinductive membership check *)
Inductive coseqInC {A: Type} (R: A -> coseq A -> Prop): A -> coseq A -> Prop :=
  | CoInSplit1A x xs {ys}: xs = cocons x ys -> coseqInC R x xs 
  | CoInSplit2A x xs y ys: xs = cocons y ys -> x <> y -> R x ys -> coseqInC R x xs.

Definition coseqCoIn {A}:= paco2 (@coseqInC A) bot2.

Lemma coseqCoIn_mon: forall {A: Type}, monotone2 (@coseqInC A).

Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - specialize(@CoInSplit1A A r' x xs ys H); intro Ha. apply Ha.
       - specialize(@CoInSplit2A A r' x xs y ys H H0); intro Ha.
         apply Ha, LE, H1.
Qed.

CoFixpoint cA {A: Type} (a: A): coseq A := (cocons a (cA a)).

Lemma unsound_coseqCoIn: forall A (a b: A), a <> b -> coseqCoIn b (cA a).
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(cA a)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := a) (ys := (cA a)). simpl. easy. easy.
       right. easy.
Qed.
(**)


