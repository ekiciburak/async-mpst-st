From ST Require Import stream st so si siso subtyping.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Inductive queue: Type :=
  | q_eps  : queue
  | q_send : participant -> label -> st.sort -> queue
  | q_merge: queue -> queue -> queue.

Inductive q_equiv: queue -> queue -> Prop :=
  | q_lend    : forall sigma, q_equiv (q_merge q_eps sigma) sigma
  | q_rend    : forall sigma, q_equiv (q_merge sigma q_eps) sigma
  | q_assoc   : forall a b c, q_equiv (q_merge a (q_merge b c)) (q_merge (q_merge a b) c)
  | q_snd_comm: forall sigma sigma' p1 l1 s1 p2 l2 s2,
                       p1 <> p2 ->
                       q_equiv (q_merge (q_merge sigma (q_merge (q_send p1 l1 s1) (q_send p2 l2 s2))) sigma')
                               (q_merge (q_merge sigma (q_merge (q_send p2 l2 s2) (q_send p1 l1 s1))) sigma').

Inductive ctx: Type :=
  | c_nil : ctx
  | c_cons: participant -> (queue * st) -> ctx -> ctx.

Fixpoint lookup (c: ctx) (p: participant): option (queue*st) :=
  match c with
    | c_nil         => None
    | c_cons q r c' => if eqb p q then Some r else lookup c' p
  end.

Fixpoint isInP (c: ctx) (p: participant): bool :=
  match c with
    | c_nil         => false
    | c_cons q r c' => if eqb p q then true else isInP c' p
  end.

Definition c_equiv (g g': ctx): Prop :=
  forall p,
  if andb (isInP g p) (isInP g' p) 
  then  
      let qst  := lookup g p in
      let qst' := lookup g' p in
      match (qst, qst') with
        | (Some sqst, Some sqst') => q_equiv sqst.1 sqst'.1 /\ 
                                     st_equivC sqst.2 sqst'.2
        | _                       => False
      end
  else False.

Inductive action: Type :=
  | a_send   : participant -> participant -> label -> action
  | a_receive: participant -> participant -> label -> action.

Inductive ctx_red: ctx -> action -> ctx -> Prop :=
  | e_rcv: forall p q l s s' sig Tp sigq xs gamma x,
           subsort s' s ->
           List.In (l,s,x) xs ->
           ctx_red (c_cons p ((q_merge (q_send q l s') sig), Tp) (c_cons q (sigq, (st_receive p xs)) gamma))
                   (a_receive q p l)
                   (c_cons p (sig, Tp) (c_cons q (sigq, x) gamma))
  | e_snd: forall p q sig xs gamma l s Tk,
           List.In (l,s,Tk) xs ->
           ctx_red (c_cons p (sig, (st_send q xs)) gamma)
                   (a_send p q l) 
                   (c_cons p ((q_merge sig (q_merge (q_send q l s) q_eps)), Tk) gamma)
  | e_struct: forall g g1 g1' g' a,
              c_equiv g g'   ->
              c_equiv g1 g1' ->
              ctx_red g1 a g1' ->
              ctx_red g a g'
  | e_trans : forall g g1 g2 a,
              ctx_red g a g1 ->
              ctx_red g1 a g2 ->
              ctx_red g a g2.

Definition path := (ctx*action*ctx)%type.

CoFixpoint typ_env (l: coseq ctx) (a: action): coseq path :=
  match force l with
    | conil => Delay conil
    | cocons x xs =>
      match force xs with
        | conil       => Delay conil
        | cocons y ys => Delay (cocons (x,a,y) (typ_env xs a))
      end
  end.

CoFixpoint typ_path_red (l: coseq path) (a: action): coseq Prop :=
  match force l with
    | conil             => Delay conil
    | cocons (x,a,y) xs => Delay (cocons (ctx_red x a y) (typ_path_red xs a))
  end.














