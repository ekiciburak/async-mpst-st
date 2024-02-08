
From Paco Require Import paco.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

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

CoInductive stream (a : Type) :=
  | conils : stream a
  | coconss: a -> stream a -> stream a.

Arguments conils { _ } .
Arguments coconss { _ } _ _.

Inductive optionF (a : Type) :=
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

Definition stream_id {A: Type} (s: stream A): stream A :=
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
  Delay (cocons n (nats_from (S n))).

CoFixpoint map {A B: Type} (f: A -> B) (xs: coseq A): coseq B := 
  Delay
  match force xs with
    | conil       => conil
    | cocons x xs => cocons (f x) (map f xs)
  end.

CoFixpoint appendC {A: Type} (l ys: coseq A): coseq A := 
  match force l with
    | conil       => ys
    | cocons x xs => Delay (cocons x (appendC xs ys))
  end.

CoFixpoint appendL {A: Type} (l: list A) (ys: coseq A): coseq A := 
  match l with
    | nil       => ys
    | cons x xs => Delay (cocons x (appendL xs ys))
  end.

Lemma anl: forall {A: Type} xs, @appendC A {| force := conil |} xs = xs.
Proof. intros.
       destruct xs. simpl.
       rewrite(coseq_eq(appendC {| force := conil |} {| force := force0 |})).
       unfold coseq_id. simpl.
       destruct force0; easy.
Qed.

Lemma anl2: forall {A: Type} xs, @appendL A nil xs = xs.
Proof. intros.
       destruct xs. simpl.
       simpl.
       rewrite(coseq_eq(appendL nil {| force := force0 |})).
       unfold coseq_id. simpl.
       destruct force0; easy.
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

Inductive sin {A: Type}: A -> stream A -> Prop :=
  | sin1 x xs y ys: xs = coconss y ys -> x = y  -> sin x xs 
  | sin2 x xs y ys: xs = coconss y ys -> x <> y -> sin x ys -> sin x xs.

Inductive CoInR {A: Type}: A -> coseq A -> Prop :=
  | CoInSplit1 x xs y ys: force xs = cocons y ys -> x = y  -> CoInR x xs
  | CoInSplit2 x xs y ys: force xs = cocons y ys -> x <> y -> CoInR x ys -> CoInR x xs.

Inductive CoInRA {A: Type} (R: A -> coseq A -> Prop): A -> coseq A -> Prop :=
  | CoInSplit1A x xs {ys}: force xs = cocons x ys -> CoInRA R x xs 
  | CoInSplit2A x xs y ys: force xs = cocons y ys -> x <> y -> R x ys -> CoInRA R x xs.

Definition CoIn {A} s1 s2 := paco2 (@CoInRA A) bot2 s1 s2.

Lemma CoIn_mon: forall {A: Type}, monotone2 (@CoInRA A).
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - specialize(@CoInSplit1A A r' x xs ys H); intro Ha. apply Ha.
       - specialize(@CoInSplit2A A r' x xs y ys H H0); intro Ha.
         apply Ha, LE, H1.
Qed.

Inductive CoNInR {A: Type}: A -> coseq A -> Prop :=
  | CoNInSplit1 x: CoNInR x (Delay conil)
  | CoNInSplit2 x xs y ys: force xs = cocons y ys -> x <> y -> CoNInR x ys -> CoNInR x xs.

Inductive CoNInRA {A: Type} (R: A -> coseq A -> Prop): A -> coseq A -> Prop :=
  | CoNInSplit1A x: CoNInRA R x (Delay conil)
  | CoNInSplit2A x xs y ys: force xs = cocons y ys -> x <> y -> R x ys -> CoNInRA R x xs.

(* Definition CoNIn {A} s1 s2 := paco2 (@CoNInRA A) bot2 s1 s2. *)

Lemma inOutL: forall {A: Type} x xs, CoInR x xs -> (@CoNInR A x xs -> False).
Proof. intros.
       induction H.
       subst.
       - induction H0.
         simpl in *. easy.
         rewrite H0 in H. inversion H.
         subst. easy.
       - apply IHCoInR.
         induction H0.
         simpl in *. easy.
         rewrite H0 in H.
         inversion H.
         subst.
         apply IHCoNInR.
         specialize(IHCoInR H4). easy.
         easy. easy. easy.
Qed.

Lemma inOutR: forall {A: Type} x xs, (CoNInR x xs) -> (@CoInR A x xs -> False).
Proof. intros.
       induction H0. 
       subst.
       - induction H.
         simpl in *. easy.
         rewrite H0 in H. inversion H.
         subst. easy.
       - apply IHCoInR.
         induction H.
         simpl in *. easy.
         rewrite H0 in H.
         inversion H.
         subst.
         apply IHCoNInR.
         specialize(IHCoInR H4). easy.
         easy. easy. easy.
Qed.

Lemma inOutLCP: forall {A: Type} x xs, CoInRA (bot2) x xs -> @CoInR A x xs.
Proof. intros.
       
       inversion H.
       subst.
       case_eq xs; intros.
       - subst. destruct force0. easy. 
         simpl in H0. inversion H0. subst.
         apply CoInSplit1 with (y := x) (ys := ys). simpl. easy. easy.
       - subst. 
         case_eq xs; intros.
         + subst. destruct force0. easy.
           simpl in H0. inversion H0. subst. easy.
Qed.

Lemma inOutLA: forall {A: Type} x xs, CoIn x xs -> (@CoNInR A x xs -> False).
Proof. intros.
       induction H0.
       punfold H.
       inversion H. subst. easy.
       subst. easy.
       apply CoIn_mon.
       apply IHCoNInR.
       pfold.
       punfold H.
       inversion H. subst. rewrite H3 in H0. inversion H0. easy.
       subst. rewrite H3 in H0. inversion H0. subst.
       unfold upaco2 in H5. destruct H5.
       punfold H5.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

Lemma inOutLA_O: forall {A: Type} (Hdec: forall u v: A, u = v \/ u <> v) x xs, (@CoNInR A x xs -> False) -> CoIn x xs.
Proof. intros.
       revert xs H.
       pcofix CIH. pfold.
       destruct xs, force0.
       intros.
       destruct H0. constructor.
       destruct (Hdec x a).
       subst.
       rewrite(coseq_eq( {| force := cocons a c |})).
       unfold coseq_id. simpl.
       intros.
       apply CoInSplit1A with (ys := c). simpl. easy.
       intros.
       apply CoInSplit2A with (y := a) (ys := c). simpl. easy. easy.

       right.
       apply CIH.
       intro H1.
       apply H0.
       apply CoNInSplit2 with (y := a) (ys := c). simpl. easy. easy. easy.
Qed.

Lemma inOutRA: forall {A: Type} x xs, @CoNInR A x xs -> (CoIn x xs -> False).
Proof. intros. 
       induction H.
       punfold H0.
       inversion H0. subst. easy.
       subst. easy.
       apply CoIn_mon.
       apply IHCoNInR.
       pfold.
       punfold H0.
       inversion H0. subst. rewrite H3 in H. inversion H. easy.
       subst. rewrite H3 in H. inversion H. subst.
       unfold upaco2 in H5. destruct H5.
       punfold H5.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

(* 
Inductive CoInR {A: Type} (R: A -> coseq A -> Prop): A -> coseq A -> Prop :=
  | CoInSplit1 x xs {y ys}: force xs = cocons y ys -> x = y  -> CoInR R x xs 
  | CoInSplit2 x xs {y ys}: force xs = cocons y ys -> x <> y -> R x ys -> CoInR R x xs.

Definition CoIn {A: Type}: A -> coseq A -> Prop := fun s1 s2 => paco2 (@CoInR A) bot2 s1 s2.
*)

Inductive sseq_gen {A: Type} (seq: coseq A -> coseq A -> Prop): coseq A -> coseq A -> Prop :=
  | _sseq_gen_n: sseq_gen seq (Delay conil) (Delay conil)
  | _sseq_gen_c: forall n s1 s2 (R: seq s1 s2), sseq_gen seq (Delay (cocons n s1)) (Delay (cocons n s2))
  | _sseq_set  : forall n m s1 s2, 
                 sseq_gen seq (Delay (cocons m (Delay (cocons n s1)))) (Delay (cocons m (Delay (cocons n s2)))) ->
                 sseq_gen seq (Delay (cocons n (Delay (cocons m s1)))) (Delay (cocons m (Delay (cocons n s2)))).

Definition sseq {A} s1 s2 := paco2 (@sseq_gen A) bot2 s1 s2.
