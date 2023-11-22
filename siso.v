From ST Require Import stream st so si.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Inductive st2siso (R: st -> st -> Prop): st -> st -> Prop :=
  | st2siso_end: st2siso R st_end st_end
  | st2siso_rcv: forall l s x t xs p,
                 List.In (l,s,x) xs ->
                 R (st_receive p [(l,s,x)]) t ->
                 st2siso R (st_receive p xs) t
  | st2siso_snd: forall l s x t xs p,
                 List.In (l,s,x) xs ->
                 R (st_send p [(l,s,x)]) t ->
                 st2siso R (st_send p xs) t.

Lemma st2siso_mon: monotone2 st2siso.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2siso_end.
       - specialize (st2siso_rcv r'); intro HS.
         apply HS with (l := l) (s := s) (x := x).
         apply H.
         apply LE, H0.
       - specialize (st2siso_snd r'); intro HS.
         apply HS with (l := l) (s := s) (x := x).
         apply H.
         apply LE, H0.
Qed.

Definition st2sisoC s1 s2 := paco2 (st2siso) bot2 s1 s2.

#[export]
Declare Instance Equivalence_st2siso : Equivalence st2sisoC.

Definition siso_id (t: st): st :=
  match t with
    | st_receive p l => st_receive p l
    | st_send p l    => st_send p l
    | st_end         => st_end
  end.

Lemma siso_eq: forall t, t = siso_id t.
Proof. intro t.
       destruct t; try easy.
Defined.

Inductive seq_gen (seq: st -> st -> Prop): st -> st -> Prop :=
  | _seq_s_end     : seq_gen seq st_end st_end
  | _seq_s_receive : forall p1 p2 l1 l2 s1 s2 w1 w2 (R: seq w1 w2), seq_gen seq (st_receive p1 [(l1,s1,w1)]) (st_receive p2 [(l2,s2,w2)])
  | _seq_s_send    : forall p1 p2 l1 l2 s1 s2 w1 w2 (R: seq w1 w2), seq_gen seq (st_send p1 [(l1,s1,w1)]) (st_send p2 [(l2,s2,w2)]).
(*| _seq_s_merge   : forall w1 w2 w3 w4 (R1: seq w1 w3) (R2: seq w2 w4), seq_gen seq (s_merge w1 w3) (s_merge w2 w4) *)
(*| _seq_s_mreceive: forall p1 l1 s1 w1 w2 (R: seq w1 w2), seq_gen seq (s_merge w1 w2) (s_receive p1 l1 s1 w1).  *)

CoInductive siso_eq_c: st -> st -> Prop :=
  | siso_eq_fold: forall s1 s2, seq_gen siso_eq_c s1 s2 -> siso_eq_c s1 s2.

(*paco*)
Definition siso_eq_i: st -> st -> Prop := fun s1 s2 => paco2 seq_gen bot2 s1 s2.

Notation "x '==~' y" := (siso_eq_i x y) (at level 50, left associativity).

(* rewriting issues *)
#[export]
Declare Instance Equivalence_eq : Equivalence siso_eq_i.

#[export]
Declare Instance Proper_siso : Proper (siso_eq_i ==> siso_eq_i) siso_id.

Check coseq.
Check conil.

CoFixpoint act (t: st): coseq (participant * string) :=
  match t with
    | st_receive p [(l,s,w')] => Delay (cocons (p, "?"%string) (act w'))
    | st_send p [(l,s,w')]    => Delay (cocons (p, "!"%string) (act w'))
    | _                       => Delay conil
  end.

Inductive Ap (p: participant): Type :=
  | ap_receive: forall q, p <> q -> label -> st.sort -> Ap p
  | ap_merge  : forall q, p <> q -> label -> st.sort -> Ap p -> Ap p.

Arguments ap_receive {_} _ _ _ _.
Arguments ap_merge {_} _ _ _ _.

CoFixpoint fromAp (p: participant) (a: Ap p): st :=
  match a with
    | ap_receive q x l s => st_receive q [(l,s,st_end)]
    | ap_merge q x l s c => st_receive q [(l,s,(fromAp p c))]
  end.

Lemma fromAp1: forall p q x l s,
  fromAp p (ap_receive q x l s) ==~ st_receive q [(l,s,st_end)].
Proof. intros.
       rewrite (siso_eq (fromAp p (ap_receive q x l s))).
       simpl.
       reflexivity.
Qed.

CoFixpoint merge_ap_cont (p: participant) (a: Ap p) (w: st): st :=
  match a with
    | ap_receive q H l s  => st_receive q [(l,s,w)]
    | ap_merge q H l s w' => st_receive q [(l,s,(merge_ap_cont p w' w))]
  end.

Inductive Bp (p: participant): Type :=
  | bp_receivea: participant -> label -> st.sort -> Bp p
  | bp_send    : forall q: participant, p <> q -> label -> st.sort -> Bp p
  | bp_mergea  : participant -> label -> st.sort -> Bp p -> Bp p
  | bp_merge   : forall q: participant, p <> q -> label -> st.sort -> Bp p -> Bp p
  | bp_end     : Bp p.

Arguments bp_receivea {_} _ _ _.
Arguments bp_send {_} _ _ _ _.
Arguments bp_mergea {_} _ _ _ _.
Arguments bp_merge {_} _ _ _ _ _.
Arguments bp_end {_}.

Fixpoint Bpn (p: participant) (b: Bp p) (n: nat): Bp p :=
  match n with
    | O   => bp_end
    | S k =>
      match b with
        | bp_receivea q l s  => bp_mergea q l s (Bpn p b k)
        | bp_send q H l s    => bp_merge q H l s (Bpn p b k)
        | bp_mergea q l s c  => bp_mergea q l s (bp_mergea q l s (Bpn p b k))
        | bp_merge q H l s c => bp_merge q H l s (bp_merge q H l s (Bpn p b k))
        | bp_end             => bp_end
      end 
  end.

Compute (Bpn "p" (bp_mergea "p" "l1" (I) (bp_receivea "p" "l1" (I))) 3).
Compute (Bpn "p" (bp_receivea "p" "l1" (I)) 4).

CoFixpoint fromBp (p: participant) (b: Bp p): st :=
  match b with 
    | bp_receivea q l s  => st_receive q [(l,s,st_end)]
    | bp_send q x l s    => st_send q [(l,s,st_end)]
    | bp_mergea q l s c  => st_receive q [(l,s,(fromBp p c))]
    | bp_merge q x l s c => st_send q [(l,s,(fromBp p c))]
    | bp_end             => st_end
  end.

CoFixpoint merge_bp_cont (p: participant) (b: Bp p) (w: st): st :=
  match b with 
    | bp_receivea q l s  => st_receive q [(l,s,w)]
    | bp_send q x l s    => st_send q [(l,s,w)]
    | bp_mergea q l s c  => st_receive q [(l,s,(merge_bp_cont p c w))]
    | bp_merge q x l s c => st_send q [(l,s,(merge_bp_cont p c w))]
    | bp_end             => w
  end.

Fixpoint merge_bp_contn (p: participant) (b: Bp p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_bp_contn p b (merge_bp_cont p b w) k
  end.

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | _sref_in : forall w w' p l s s',
                      subsort s' s -> 
                      seq w w' ->
                      refinementR seq (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])

  | _sref_out: forall w w' p l s s',
                      subsort s s' -> 
                      seq w w' ->
                      refinementR seq (st_send p [(l,s,w)]) (st_send p [(l,s',w')])

  | _sref_a  : forall w w' p l s s' a,
                      subsort s' s ->
                      seq w (merge_ap_cont p a w') ->
                      (*bisim*) sseq (act w) (act (merge_ap_cont p a w')) ->
                      refinementR seq (st_receive p [(l,s,w)]) (merge_ap_cont p a (st_receive p [(l,s',w')]))

  | _sref_b  : forall w w' p l s s' b n,
                      subsort s s' -> 
                      seq w (merge_bp_cont p (Bpn p b n) w') ->
(*                       (*bisim*) sseq (act w) (act (merge_bp_contn p b w' n)) -> *)
                      refinementR seq (st_send p [(l,s,w)]) (merge_bp_cont p (Bpn p b n) (st_send p [(l,s',w')]))

  | _sref_end: refinementR seq st_end st_end.

(* rewriting issues *)
#[export]
Declare Instance Equivalence_seq_genR (r: st -> st -> Prop): Equivalence r -> Equivalence (refinementR r).

(* Definition refinement_eq_i: relation siso := fun s1 s2 => paco2 refinementR refinement s1 s2. *)

Definition refinement_eq_i: st -> st -> Prop := fun s1 s2 => paco2 refinementR bot2 s1 s2.

Notation "x '~<' y" := (refinement_eq_i x y) (at level 50, left associativity).

(* rewriting issues *)
#[export]
Declare Instance Equivalence_ref_eqi: Equivalence refinement_eq_i.

(* #[export]
Declare Instance Proper_refinement_siso : forall x y, Proper (refinement_eq_i x y) siso_eq_i x y. *)

