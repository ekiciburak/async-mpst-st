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

Inductive st2si (R: st -> st -> Prop): st -> st -> Prop :=
  | st2si_end: st2si R st_end st_end
  | st2si_rcv: forall l s x xs p,
               R x (pathsel l s xs) ->
               st2si R (st_receive p [(l,s,x)]) (st_receive p xs)
  | st2si_snd: forall p l s xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip ys xs) ->
               st2si R (st_send p (zip (zip l s) ys)) (st_send p (zip (zip l s) xs)).

Definition st2siC s1 s2 := paco2 (st2si) bot2 s1 s2.

Lemma st2si_mon: monotone2 st2si.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2si_end.
       - specialize (st2si_rcv r'); intro HS.
         apply HS with (l := l) (s := s) (x := x).
         apply LE, H.
       - specialize (st2si_snd r'); intro HS.
         apply HS with (l := l) (s := s) (ys := ys). easy.
         apply Forall_forall.
         intros(x1,x2) Ha.
         simpl.
         apply LE.
         rewrite Forall_forall in H0.
         apply (H0 (x1,x2)).
         apply Ha.
Qed.

Inductive st2siA (R: si -> st -> Prop): si -> st -> Prop :=
  | st2si_endA: st2siA R si_end st_end
  | st2si_rcvA: forall l s x xs p,
                R x (pathsel l s xs) ->
                st2siA R (si_receive p (l,s,x)) (st_receive p xs)
  | st2si_sndA: forall p l s xs ys,
                length xs = length ys ->
                List.Forall (fun u => R (fst u) (snd u)) (zip ys xs) ->
                st2siA R (si_send p (zip (zip l s) ys)) (st_send p (zip (zip l s) xs)).

Definition st2siCA s1 s2 := paco2 (st2siA) bot2 s1 s2. 


