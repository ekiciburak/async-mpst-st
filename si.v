From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
From ST Require Import stream st.
Require Import String List.
Import ListNotations.


From Paco Require Import paco.
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

(* Inductive st2siA (R: st -> si -> Prop) : st -> si -> Prop :=
  | st2siA_end: st2siA R st_end si_end
  | st2siA_snd: forall p l s x t xs,
                List.In (l,s,x) xs ->
                R x t ->
                st2siA R (st_send p xs) t
  | st2siA_rcv: forall l s x t xs p,
                List.In (l,s,x) xs ->
                R (st_receive p [(l,s,x)]) t ->
                st2siA R (st_receive p xs) t. *)

Inductive st2si (R: st -> st -> Prop) : st -> st -> Prop :=
  | st2si_end: st2si R st_end st_end
  | st2si_rcv: forall l s x t xs p,
               List.In (l,s,x) xs ->
               R (st_receive p [(l,s,x)]) t ->
               st2si R (st_receive p xs) t
  | st2si_snd: forall p l s t xs ys,
               List.Forall (fun u => R (fst u) (snd u)) (zip xs ys) ->
               R (st_send p (zip (zip l s) ys)) t ->
               st2si R (st_send p (zip (zip l s) xs)) t.

Lemma st2si_mon: monotone2 st2si.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2si_end.
       - specialize (st2si_rcv r'); intro HS.
         apply HS with (l := l) (s := s) (x := x).
         apply H.
         apply LE, H0.
       - specialize (st2si_snd r'); intro HS.
         apply HS with (l := l) (s := s) (ys := ys).
         apply Forall_forall.
         intros(x1,x2) Ha.
         simpl.
         apply LE.
         rewrite Forall_forall in H.
         apply (H (x1,x2)).
         apply Ha.
         apply LE, H0.
Qed.

Definition st2siC s1 s2 := paco2 (st2si) bot2 s1 s2.
(* Definition st2siCA s1 s2 := paco2 (st2siA) bot2 s1 s2. *)

#[export]
Declare Instance Equivalence_st2si : Equivalence st2siC.


