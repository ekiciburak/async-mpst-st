Require Import ST.src.stream ST.src.st ST.src.so ST.src.si.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

CoFixpoint act (t: st): coseq (participant * string) :=
  match t with
    | st_receive p [(l,s,w')] => Delay (cocons (p, "?"%string) (act w'))
    | st_send p [(l,s,w')]    => Delay (cocons (p, "!"%string) (act w'))
    | _                       => Delay conil
  end.

CoFixpoint acts (t: st): stream (participant * string) :=
  match t with
    | st_receive p [(l,s,w')] => (coconss (p, "?"%string) (acts w'))
    | st_send p [(l,s,w')]    => (coconss (p, "!"%string) (acts w'))
    | _                       => conils
  end.

CoInductive action: st -> coseq (participant * string) -> Prop :=
  | a_end: action st_end (Delay conil)
  | a_rcv: forall (p:participant) l s w a,
           action w a ->
           action (st_receive p [(l,s,w)]) (Delay (cocons (p, "?"%string) a))
  | a_snd: forall (p: (participant)) l s w a,
           action w a ->
           action (st_send p [(l,s,w)]) (Delay (cocons (p, "!"%string) a)).

Inductive Ap (p: participant): Type :=
  | ap_receive: forall q, p <> q -> label -> st.sort -> Ap p
  | ap_merge  : forall q, p <> q -> label -> st.sort -> Ap p -> Ap p
  | ap_end    : Ap p.

Arguments ap_receive {_} _ _ _ _.
Arguments ap_merge {_} _ _ _ _.
Arguments ap_end {_}.

Fixpoint Apn (p: participant) (a: Ap p) (n: nat): Ap p :=
  match n with
    | O   => ap_end
    | S k =>
      match a with
        | ap_receive q H l s => ap_merge q H l s (Apn p a k)
        | ap_merge q H l s c => ap_merge q H l s (ap_merge q H l s (Apn p a k))
        | ap_end             => ap_end
      end 
  end.

Fixpoint apListA (p: participant) (a: Ap p): list (Ap p) :=
  match a with
    | ap_receive q H l s => [a]
    | ap_merge q H l s c => ap_receive q H l s :: (apListA p c)
    | ap_end             => nil
  end.

Fixpoint listApA (p: participant) (l: list (Ap p)): Ap p :=
  match l with
    | nil   => ap_end
    | x::xs => 
      match x with
        | ap_receive q H l s      => ap_merge q H l s (listApA p xs)
        | _                       => x
      end
  end.

Fixpoint nappA {A: Type} (n: nat) (l: list A): list A :=
  match n with
    | O   => nil
    | S k => l ++ nappA k l
  end.

Definition ApnA2 (p: participant) (a: Ap p) (n: nat): Ap p :=
  listApA p (nappA n (apListA p a)).


Fixpoint apList (p: participant) (a: Ap p): list (Ap p) :=
  match a with
    | ap_receive q H l s => [a]
    | ap_merge q H l s c => ap_merge q H l s ap_end :: (apList p c)
    | ap_end             => nil
  end.

Fixpoint listAp (p: participant) (l: list (Ap p)): Ap p :=
  match l with
    | nil   => ap_end
    | [ap_receive q H l s] => ap_receive q H l s
    | x::xs => 
      match x with
        | ap_receive q H l s      => ap_merge q H l s (listAp p xs)
        | ap_merge q H l s ap_end => ap_merge q H l s (listAp p xs)
        | _                       => x
      end
  end.

Lemma aplisteq: forall p a, listAp p (apList p a) = a.
Proof. intros p a.
       induction a; intros.
       - simpl. easy.
       - simpl. rewrite IHa. easy.
       - simpl. easy.
Qed.

Fixpoint napp {A: Type} (n: nat) (l: list A): list A :=
  match n with
    | O   => nil
    | S k => l ++ napp k l
  end.

Definition ApnA (p: participant) (a: Ap p) (n: nat): Ap p :=
  listAp p (napp n (apList p a)).

CoFixpoint fromAp (p: participant) (a: Ap p): st :=
  match a with
    | ap_receive q x l s => st_receive q [(l,s,st_end)]
    | ap_merge q x l s c => st_receive q [(l,s,(fromAp p c))]
    | ap_end             => st_end
  end.

Fixpoint actA (p: participant) (a: Ap p): list (participant * string) :=
  match a with
    | ap_receive q x l s => cons (q, "?"%string) nil
    | ap_merge q x l s c => cons (q, "?"%string) (actA p c)
    | _                  => nil
  end.

Fixpoint actAn (p: participant) (a: Ap p) (n: nat): list (participant * string) :=
  match n with
    | O   => nil
    | S k =>
      match a with
        | ap_receive q x l s => cons (q, "?"%string) (actAn p a k)
        | ap_merge q x l s c => (cons (q, "?"%string) (actA p c)) ++ (actAn p a k)
        | _                  => nil
      end
  end.

CoFixpoint merge_ap_cont (p: participant) (a: Ap p) (w: st): st :=
  match a with
    | ap_receive q H l s  => st_receive q [(l,s,w)]
    | ap_merge q H l s w' => st_receive q [(l,s,(merge_ap_cont p w' w))]
    | ap_end              => w
  end.

Fixpoint merge_ap_contn (p: participant) (a: Ap p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ap_cont p a (merge_ap_contn p a w k)
  end.

Fixpoint merge_ap_contnA (p: participant) (a: Ap p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => 
      match a with
        | ap_receive q H l s  => st_receive q [(l,s,merge_ap_contnA p a w k)]
        | ap_merge q H l s w' => st_receive q [(l,s,(merge_ap_contnA p w' w k))]
        | ap_end              => w
      end
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

Inductive Cp (p: participant): Type :=
  | cp_receive: forall q, p <> q -> label -> st.sort -> Cp p
  | cp_mergea : forall q, p <> q -> label -> st.sort -> Cp p -> Cp p
  | cp_send   : participant -> label -> st.sort -> Cp p
  | cp_merge  : participant -> label -> st.sort -> Cp p -> Cp p
  | cp_end    : Cp p.

Arguments cp_receive {_} _ _ _ _.
Arguments cp_merge {_} _ _ _ _.
Arguments cp_end {_}.
Arguments cp_send {_} _ _ _.
Arguments cp_mergea {_} _ _ _ _.

CoFixpoint merge_cp_cont (p: participant) (c: Cp p) (w: st): st :=
  match c with 
    | cp_receive q H l s  => st_receive q [(l,s,w)]
    | cp_send q l s       => st_send q [(l,s,w)]
    | cp_mergea q H l s c => st_receive q [(l,s,(merge_cp_cont p c w))]
    | cp_merge q l s c    => st_send q [(l,s,(merge_cp_cont p c w))]
    | cp_end              => w
  end.

Fixpoint merge_cp_contn (p: participant) (c: Cp p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_cp_cont p c (merge_cp_contn p c w k)
  end.

Fixpoint actC (p: participant) (c: Cp p): list (participant * string) :=
  match c with
    | cp_receive q x l s  => cons (q, "?"%string) nil
    | cp_mergea q x l s c => cons (q, "?"%string) (actC p c)
    | cp_send q l s       => cons (q, "!"%string) nil
    | cp_merge q l s c    => cons (q, "!"%string) (actC p c)
    | _                   => nil
  end.

Fixpoint actCn (p: participant) (c: Cp p) (n: nat): list (participant * string) :=
  match n with
    | O   => nil
    | S k =>
      match c with
        | cp_receive q x l s    => cons (q, "?"%string) (actCn p c k)
        | cp_mergea q x l s cnt => (cons (q, "?"%string) (actC p cnt)) ++ (actCn p c k)
        | cp_send q l s         => cons (q, "!"%string) (actCn p c k)
        | cp_merge q l s cnt    => (cons (q, "!"%string) (actC p cnt)) ++ (actCn p c k)
        | _                     => nil
      end
  end.

Lemma Ap2Cp: forall p, Ap p -> Cp p.
Proof. intros p a.
       induction a; intros.
       exact (cp_receive q n s s0).
       exact (cp_mergea q n s s0 IHa).
       exact (cp_end).
Defined.

Fixpoint Bpn (p: participant) (b: Bp p) (n: nat): Bp p :=
  match n with
    | O   => bp_end
    | S k =>
      match b in (Bp _) with
        | bp_receivea q l s  => bp_mergea q l s (Bpn p b k)
        | bp_send q H l s    => bp_merge q H l s (Bpn p b k)
        | bp_mergea q l s c  => bp_mergea q l s (bp_mergea q l s (Bpn p b k))
        | bp_merge q H l s c => bp_merge q H l s (bp_merge q H l s (Bpn p b k))
        | bp_end             => bp_end
      end 
  end. 

CoFixpoint fromBp (p: participant) (b: Bp p): st :=
  match b with 
    | bp_receivea q l s  => st_receive q [(l,s,st_end)]
    | bp_send q x l s    => st_send q [(l,s,st_end)]
    | bp_mergea q l s c  => st_receive q [(l,s,(fromBp p c))]
    | bp_merge q x l s c => st_send q [(l,s,(fromBp p c))]
    | bp_end             => st_end
  end.

Fixpoint actB (p: participant) (b: Bp p): list (participant * string) :=
  match b with
    | bp_receivea q l s  => cons (q, "?"%string) nil
    | bp_send q x l s    => cons (q, "!"%string) nil
    | bp_mergea q l s c  => cons (q, "?"%string) (actB p c)
    | bp_merge q x l s c => cons (q, "!"%string) (actB p c)
    | _                  => nil
  end.

Fixpoint actBn (p: participant) (b: Bp p) (n: nat): list (participant * string) :=
  match n with
    | O   => nil
    | S k =>
      match b with
        | bp_receivea q l s  => cons (q, "?"%string) (actBn p b k)
        | bp_send q x l s    => cons (q, "!"%string) (actBn p b k)
        | bp_mergea q l s c  => (cons (q, "?"%string) (actB p c)) ++ (actBn p b k)
        | bp_merge q x l s c => (cons (q, "!"%string) (actB p c)) ++ (actBn p b k)
        | _                  => nil
      end
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
    | S k  => merge_bp_cont p b (merge_bp_contn p b w k)
  end.

Fixpoint bpList (p: participant) (b: Bp p): list (Bp p) :=
  match b with
    | bp_receivea q l s  => [b]
    | bp_send q x l s    => [b]
    | bp_mergea q l s c  => bp_receivea q l s :: (bpList p c)
    | bp_merge q H l s c => bp_send q H l s :: (bpList p c)
    | bp_end             => nil
  end.

Fixpoint listBp (p: participant) (l: list (Bp p)): Bp p :=
  match l with
    | nil   => bp_end
    | x::xs => 
      match x with
        | bp_receivea q l s => bp_mergea q l s (listBp p xs)
        | bp_send q H l s   => bp_merge q H l s (listBp p xs)
        | _                 => x
      end
  end.

Definition BpnA (p: participant) (b: Bp p) (n: nat): Bp p :=
  listBp p (napp n (bpList p b)).

Fixpoint cpList (p: participant) (c: Cp p): list (Cp p) :=
  match c with
    | cp_receive q H l s  => [c]
    | cp_mergea q H l s c => cp_receive q H l s :: (cpList p c)
    | cp_send q l s       => [c]
    | cp_merge q l s c    => cp_send q l s :: (cpList p c)
    | cp_end              => nil
  end.

Fixpoint listCp (p: participant) (l: list (Cp p)): Cp p :=
  match l with
    | nil   => cp_end
    | x::xs => 
      match x with
        | cp_receive q H l s => cp_mergea q H l s (listCp p xs)
        | cp_send q l s      => cp_merge q l s (listCp p xs)
        | _                  => x
      end
  end.

Definition CpnA (p: participant) (c: Cp p) (n: nat): Cp p :=
  listCp p (napp n (cpList p c)).


Inductive Dp (p: participant): Type :=
  | dp_receive: forall q, p <> q -> label -> st.sort -> Dp p
  | dp_mergea : forall q, p <> q -> label -> st.sort -> Dp p -> Dp p
  | dp_send   : forall q, p <> q -> label -> st.sort -> Dp p
  | dp_merge  : forall q, p <> q -> label -> st.sort -> Dp p -> Dp p
  | dp_end    : Dp p.

Arguments dp_receive {_} _ _ _ _.
Arguments dp_merge {_} _ _ _ _.
Arguments dp_end {_}.
Arguments dp_send {_} _ _ _.
Arguments dp_mergea {_} _ _ _ _.

CoFixpoint merge_dp_cont (p: participant) (d: Dp p) (w: st): st :=
  match d with 
    | dp_receive q H l s  => st_receive q [(l,s,w)]
    | dp_send q H l s     => st_send q [(l,s,w)]
    | dp_mergea q H l s c => st_receive q [(l,s,(merge_dp_cont p c w))]
    | dp_merge q H l s c  => st_send q [(l,s,(merge_dp_cont p c w))]
    | dp_end              => w
  end.

Fixpoint merge_dp_contn (p: participant) (d: Dp p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_dp_cont p d (merge_dp_contn p d w k)
  end.

Fixpoint actD (p: participant) (d: Dp p): list (participant * string) :=
  match d with
    | dp_receive q x l s  => cons (q, "?"%string) nil
    | dp_mergea q x l s c => cons (q, "?"%string) (actD p c)
    | dp_send q x l s     => cons (q, "!"%string) nil
    | dp_merge q x l s c  => cons (q, "!"%string) (actD p c)
    | _                   => nil
  end.

Fixpoint actDn (p: participant) (d: Dp p) (n: nat): list (participant * string) :=
  match n with
    | O   => nil
    | S k =>
      match d with
        | dp_receive q x l s    => cons (q, "?"%string) (actDn p d k)
        | dp_mergea q x l s cnt => (cons (q, "?"%string) (actD p cnt)) ++ (actDn p d k)
        | dp_send q x l s       => cons (q, "!"%string) (actDn p d k)
        | dp_merge q x l s cnt  => (cons (q, "!"%string) (actD p cnt)) ++ (actDn p d k)
        | _                     => nil
      end
  end.

Fixpoint dpList (p: participant) (d: Dp p): list (Dp p) :=
  match d with
    | dp_receive q H l s  => [d]
    | dp_mergea q H l s c => dp_receive q H l s :: (dpList p c)
    | dp_send q H l s     => [d]
    | dp_merge q H l s c  => dp_send q H l s :: (dpList p c)
    | dp_end              => nil
  end.

Fixpoint listDp (p: participant) (l: list (Dp p)): Dp p :=
  match l with
    | nil   => dp_end
    | x::xs => 
      match x with
        | dp_receive q H l s => dp_mergea q H l s (listDp p xs)
        | dp_send q H l s    => dp_merge q H l s (listDp p xs)
        | _                  => x
      end
  end.

Definition DpnA (p: participant) (d: Dp p) (n: nat): Dp p :=
  listDp p (napp n (dpList p d)).

