From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.src.st ST.types.local.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

CoInductive si: Type :=
  | si_end    : si
  | si_receive: participant -> (label*sort*si)      -> si
  | si_send   : participant -> list (label*sort*si) -> si.

Definition si_id (s: si): si :=
  match s with
    | si_end          => si_end
    | si_receive p l  => si_receive p l
    | si_send p w     => si_send p w  
  end.

Lemma si_eq: forall s, s = si_id s.
Proof. intro s; destruct s; easy. Defined.

(* Inductive st2si (R: si -> st -> Prop): si -> st -> Prop :=
  | st2si_end: st2si R si_end st_end
  | st2si_rcv: forall l s x xs p,
               R x (pathsel l s xs) ->
               st2si R (si_receive p (l,s,x)) (st_receive p xs)
  | st2si_snd: forall p l s xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip ys xs) ->
               st2si R (si_send p (zip (zip l s) ys)) (st_send p (zip (zip l s) xs)).

Definition st2siC s1 s2 := paco2 (st2si) bot2 s1 s2. *)

(* Inductive st2si (R: st -> st -> Prop): st -> st -> Prop :=
  | st2si_end: st2si R st_end st_end
  | st2si_rcv: forall l s x s' y f p,
               f l = Some(s',y) ->
               s = s' ->
               R x y ->
               st2si R (st_receive p (sfun l s x)) (st_receive p f)
  | st2si_snd: forall p f g,
               (forall l, 
                match (f l, g l) with
                 | (Some (s1, t1), Some (s2, t2)) => s1 = s2 /\ R t1 t2
                 | (None, None)                   => True
                 | _                              => False
                end
               ) ->
               st2si R (st_send p f) (st_send p g).
 *)

Inductive st2si (R: st -> st -> Prop): st -> st -> Prop :=
  | st2si_end: st2si R st_end st_end
  | st2si_rcv: forall l s x xs y p,
               R x y ->
               copathsel l s xs y ->
               st2si R (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2si_snd: forall p xs ys,
               colen_eqC xs ys ->
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
         apply HS. easy.
         apply monH2 with (r := r); easy.
Qed.

(* Inductive st2siA (R: si -> st -> Prop): si -> st -> Prop :=
  | st2si_endA: st2siA R si_end st_end
  | st2si_rcvA: forall l s x xs p,
                R x (pathsel l s xs) ->
                st2siA R (si_receive p (l,s,x)) (st_receive p xs)
  | st2si_sndA: forall p l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip ys xs) ->
                st2siA R (si_send p (zip (zip l s) ys)) (st_send p (zip (zip l s) xs)).

Definition st2siCA s1 s2 := paco2 (st2siA) bot2 s1 s2.  *)


