From ST Require Import stream st so si.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

(* CoInductive so: Type :=
  | so_end    : so 
  | so_receive: participant -> list (label*sort*so) -> so 
  | so_send   : participant -> (label*sort*so) -> so.

CoInductive si: Type :=
  | si_end    : si
  | si_receive: participant -> si -> si 
  | si_send   : participant -> list (label*sort*si) -> si.
  
 *)

(* CoInductive siso: Type :=
  | siso_end    : siso 
  | siso_receive: participant -> (label*st.sort*siso) -> siso 
  | siso_send   : participant -> (label*st.sort*siso) -> siso. *)

(* Inductive so2siso (R: so -> siso -> Prop): so -> siso -> Prop :=
  | so2siso_end: so2siso R so_end siso_end
  | so2siso_rcv: forall p l s x t,
                 R t x ->
                 so2siso R t (siso_receive p (l,s,x))
  | so2siso_snd: forall p l s x t,
                 R t (siso_send p (l,s,x)) ->
                 so2siso R t (siso_send p (l,s,x)).
 *)
(* Inductive so2siso (R: so -> siso -> Prop): so -> siso -> Prop :=
  | so2siso_end: so2siso R so_end siso_end
  | so2siso_rcv: forall p l s x xs t,
                 List.In (l,s,x) xs ->
                 R (so_receive p [(l,s,x)]) t ->
                 so2siso R (so_receive p xs) t
  | so2siso_snd: forall p l s x t,
                 R x t ->
                 so2siso R (so_send p (l,s,x)) t. *)

(* Inductive si2siso (R: si -> siso -> Prop): si -> siso -> Prop :=
  | si2siso_end: si2siso R si_end siso_end
  | si2siso_snd: forall p l s x xs t,
                 List.In (l,s,x) xs ->
                 R (si_send p [(l,s,x)]) t ->
                 si2siso R (si_send p xs) t
  | si2siso_rcv: forall p l s x t,
                 R x t ->
                 si2siso R (si_receive p (l,s,x)) t. *)

(* Inductive si2siso (R: si -> siso -> Prop): si -> siso -> Prop :=
  | si2siso_end: si2siso R si_end siso_end
  | si2siso_rcv: forall p l s x t,
                 R t (siso_receive p (l,s,x)) ->
                 si2siso R t (siso_receive p (l,s,x))
  | si2siso_snd: forall l s x t p,
                 R t x ->
                 si2siso R t (siso_send p (l,s,x)).
*)

Inductive singletonI (R: st -> Prop): st -> Prop :=
  | ends : singletonI R st_end
  | sends: forall p l s w, R w -> singletonI R (st_send p [(l,s,w)])
  | recvs: forall p l s w, R w -> singletonI R (st_receive p [(l,s,w)]).

Definition singleton s := paco1 (singletonI) bot1 s.

Lemma sI_mon: monotone1 singletonI.
Proof. unfold monotone1.
       intros.
       induction IN; intros.
       - apply ends.
       - apply sends, LE, H.
       - apply recvs, LE, H.
Qed.

Class siso: Type := mk_siso 
{ und  : st; 
  sprop: singleton und
}.

Lemma siso_same: forall s1 s2, @und s1 = @und s2 -> JMeq (@sprop s1) (@sprop s2) -> s1 = s2.
Proof. intros.
       destruct s1, s2. simpl in *.
       subst.
       easy.
Qed.

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

(*
Inductive st2sisoA (R: st -> siso -> Prop): st -> siso -> Prop :=
  | st2sisoA_end: st2sisoA R st_end siso_end
  | st2sisoA_rcv: forall l s x t xs p,
                  List.In (l,s,x) xs ->
                  R (st_receive p [(l,s,x)]) t ->
                  st2sisoA R (st_receive p xs) t
  | st2sisoA_snd: forall l s x t xs p,
                  List.In (l,s,x) xs ->
                  R (st_send p [(l,s,x)]) t ->
                  st2sisoA R (st_send p xs) t. *)

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

Definition st2sisoC s1 s2 := paco2 (st2siso) bot2 s2 s1.
(* Definition so2sisoC s1 s2 := paco2 (so2siso) bot2 s1 s2.
Definition si2sisoC s1 s2 := paco2 (si2siso) bot2 s1 s2.
Definition st2sisoCA s1 s2 := paco2 (st2sisoA) bot2 s1 s2. *)

(* #[export]
Declare Instance Equivalence_st2siso : Equivalence st2sisoC. *)

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

(* Definition siso_idA (t: siso): siso :=
  match t with
    | siso_receive p a => siso_receive p a
    | siso_send p a    => siso_send p a
    | siso_end         => siso_end
  end.

Lemma siso_eqA: forall t, t = siso_idA t.
Proof. intro t.
       destruct t; try easy.
Defined. *)

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

Inductive actT: Type :=
  | rcv: actT
  | snd: actT.

Definition actTeqb (a1 a2: actT): bool :=
  match (a1, a2) with
    | (rcv,rcv)
    | (snd,snd) => true
    | _         => false
  end.

Lemma act_dec: forall a1 a2, actTeqb a1 a2 = true \/ actTeqb a1 a2 = false.
Proof. intros a1 a2.
       case_eq a1; case_eq a2; intros.
       - left. easy.
       - right. easy.
       - right. easy.
       - left. easy.
Qed.

Lemma act_eqb_eq: forall a1 a2, actTeqb a1 a2 = true -> a1 = a2.
Proof. intros a1 a2 Ha.
       case_eq a1; case_eq a2; intros; try easy.
       - subst. easy.
       - subst. easy.
Qed.

Lemma act_neqb_neq: forall a1 a2, actTeqb a1 a2 = false -> a1 <> a2.
Proof. intros a1 a2 Ha.
       case_eq a1; case_eq a2; intros; try easy.
       - subst. easy.
       - subst. easy.
Qed.


CoFixpoint act (t: st): coseq (participant * actT) :=
  match t with
    | st_receive p [(l,s,w')] => Delay (cocons (p, rcv) (act w'))
    | st_send p [(l,s,w')]    => Delay (cocons (p, snd) (act w'))
    | _                       => Delay conil
  end.

CoFixpoint acts (t: st): stream (participant * actT) :=
  match t with
    | st_receive p [(l,s,w')] => (coconss (p, rcv) (acts w'))
    | st_send p [(l,s,w')]    => (coconss (p, snd) (acts w'))
    | _                       => conils
  end.
  
(* CoFixpoint actC (t: siso): coseq (participant * string) :=
  match t with
    | siso_receive p (l,s,w') => Delay (cocons (p, "?"%string) (actC w'))
    | siso_send p (l,s,w')    => Delay (cocons (p, "!"%string) (actC w'))
    | _                       => Delay conil
  end. *)

CoInductive action: st -> coseq (participant * actT) -> Prop :=
  | a_end: action st_end (Delay conil)
  | a_rcv: forall (p:participant) l s w a,
           action w a ->
           action (st_receive p [(l,s,w)]) (Delay (cocons (p, rcv) a))
  | a_snd: forall (p: (participant)) l s w a,
           action w a ->
           action (st_send p [(l,s,w)]) (Delay (cocons (p, snd) a)).

Inductive Ap (p: participant): Type :=
  | ap_receive: forall q, p <> q -> label -> st.sort -> Ap p
  | ap_merge  : forall q, p <> q -> label -> st.sort -> Ap p -> Ap p
  | ap_end    : Ap p.

Arguments ap_receive {_} _ _ _ _.
Arguments ap_merge {_} _ _ _ _.
Arguments ap_end {_}.

Inductive Ap2 (p: participant): Type :=
  | ap_receive2: forall q, p <> q -> label -> st.sort -> Ap2 p
  | ap_merge2  : forall q, p <> q -> label -> st.sort -> Ap2 p -> Ap2 p.

Arguments ap_receive2 {_} _ _ _ _.
Arguments ap_merge2 {_} _ _ _ _.

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

Fixpoint Apn2 (p: participant) (a: Ap2 p) (n: nat): Ap2 p :=
  match n with
    | 0   => a
    | S k => 
      match a with
        | ap_receive2 q H l s => ap_merge2 q H l s (Apn2 p a k)
        | ap_merge2 q H l s c => ap_merge2 q H l s (ap_merge2 q H l s (Apn2 p a k))
      end
  end.

(* Parameters (p q: participant) (l: label) (s: st.sort) (H: p <> q).
Compute Apn2 p (ap_merge2 q H l s (ap_receive2 q H l s)) 2. *)

CoFixpoint merge_ap_cont2 (p: participant) (a: Ap2 p) (w: st): st :=
  match a with
    | ap_receive2 q H l s  => st_receive q [(l,s,w)]
    | ap_merge2 q H l s w' => st_receive q [(l,s,(merge_ap_cont2 p w' w))]
  end.

Definition merge_ap_contn2 (p: participant) (a: Ap2 p) (w: st) (n: nat): st :=
  merge_ap_cont2 p (Apn2 p a n) w.

(* Parameters (p q: participant) (l: label) (s: st.sort) (H: p <> q).
Compute merge_ap_cont2 p (Apn2 p ( ap_receive2 q H l s) 4) (st_end). *)

CoFixpoint fromAp (p: participant) (a: Ap p): st :=
  match a with
    | ap_receive q x l s => st_receive q [(l,s,st_end)]
    | ap_merge q x l s c => st_receive q [(l,s,(fromAp p c))]
    | ap_end             => st_end
  end.

Fixpoint actA (p: participant) (a: Ap p): list (participant * actT) :=
  match a with
    | ap_receive q x l s => cons (q, rcv) nil
    | ap_merge q x l s c => cons (q, rcv) (actA p c)
    | _                  => nil
  end.

Fixpoint actAn (p: participant) (a: Ap p) (n: nat): list (participant * actT) :=
  match n with
    | O   => nil
    | S k =>
      match a with
        | ap_receive q x l s => cons (q, rcv) (actAn p a k)
        | ap_merge q x l s c => (cons (q, rcv) (actA p c)) ++ (actAn p a k)
        | _                  => nil
      end
  end.

CoFixpoint merge_ap_cont (p: participant) (a: Ap p) (w: st): st :=
  match a with
    | ap_receive q H l s  => st_receive q [(l,s,w)]
    | ap_merge q H l s w' => st_receive q [(l,s,(merge_ap_cont p w' w))]
    | ap_end              => w
  end.

(* CoFixpoint merge_ap_contB (p: participant) (a: Ap p) (w: siso): siso :=
  match a with
    | ap_receive q H l s  => siso_receive q (l,s,w)
    | ap_merge q H l s w' => siso_receive q (l,s,(merge_ap_contB p w' w))
    | ap_end              => w
  end.
 *)

Fixpoint merge_ap_contn (p: participant) (a: Ap p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ap_cont p a (merge_ap_contn p a w k)
  end.

(* Fixpoint merge_ap_contnB (p: participant) (a: Ap p) (w: siso) (n: nat): siso :=
  match n with
    | O    => w
    | S k  => merge_ap_contB p a (merge_ap_contnB p a w k)
  end. *)

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

Fixpoint actC (p: participant) (c: Cp p): list (participant * actT) :=
  match c with
    | cp_receive q x l s  => cons (q, rcv) nil
    | cp_mergea q x l s c => cons (q, rcv) (actC p c)
    | cp_send q l s       => cons (q, snd) nil
    | cp_merge q l s c    => cons (q, snd) (actC p c)
    | _                   => nil
  end.

Fixpoint actCn (p: participant) (c: Cp p) (n: nat): list (participant * actT) :=
  match n with
    | O   => nil
    | S k =>
      match c with
        | cp_receive q x l s    => cons (q, rcv) (actCn p c k)
        | cp_mergea q x l s cnt => (cons (q, rcv) (actC p cnt)) ++ (actCn p c k)
        | cp_send q l s         => cons (q, snd) (actCn p c k)
        | cp_merge q l s cnt    => (cons (q, snd) (actC p cnt)) ++ (actCn p c k)
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

Lemma Ap2CpCont: forall p a w, merge_ap_cont p a w = merge_cp_cont p (Ap2Cp p a) w.
Proof. intros.
       induction a; intros.
       simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) w)). simpl. easy.
       simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 (Ap2Cp p a)) w)). 
       simpl. rewrite IHa. easy.
       simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)).
       rewrite(siso_eq(merge_cp_cont p cp_end w)).
       simpl. easy.
Qed.

(* 
From Equations Require Import Equations.

Equations Bpn (p: participant) (b: Bp p) (n: nat): Bp p :=
  Bpn p b O                        := bp_end;
  Bpn p (bp_receivea q l s) (S k)  :=  bp_mergea q l s (Bpn p (bp_receivea q l s) k);
  Bpn p (bp_send q H l s) (S k)    :=  bp_merge q H l s (Bpn p (bp_send q H l s) k);
  Bpn p (bp_mergea q l s c) (S k)  :=  bp_mergea q l s (Bpn p (bp_mergea q l s c) k);
  Bpn p (bp_merge q H l s c) (S k) :=  bp_merge q H l s (Bpn p (bp_merge q H l s c) k);
  Bpn p (bp_end) (S k)             :=  bp_end.  *)


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

Fixpoint actB (p: participant) (b: Bp p): list (participant * actT) :=
  match b with
    | bp_receivea q l s  => cons (q, rcv) nil
    | bp_send q x l s    => cons (q, snd) nil
    | bp_mergea q l s c  => cons (q, rcv) (actB p c)
    | bp_merge q x l s c => cons (q, snd) (actB p c)
    | _                  => nil
  end.

Fixpoint actBn (p: participant) (b: Bp p) (n: nat): list (participant * actT) :=
  match n with
    | O   => nil
    | S k =>
      match b with
        | bp_receivea q l s  => cons (q, rcv) (actBn p b k)
        | bp_send q x l s    => cons (q, snd) (actBn p b k)
        | bp_mergea q l s c  => (cons (q, rcv) (actB p c)) ++ (actBn p b k)
        | bp_merge q x l s c => (cons (q, snd) (actB p c)) ++ (actBn p b k)
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

(* CoFixpoint merge_bp_contB (p: participant) (b: Bp p) (w: siso): siso :=
  match b with 
    | bp_receivea q l s  => siso_receive q (l,s,w)
    | bp_send q x l s    => siso_send q (l,s,w)
    | bp_mergea q l s c  => siso_receive q (l,s,(merge_bp_contB p c w))
    | bp_merge q x l s c => siso_send q (l,s,(merge_bp_contB p c w))
    | bp_end             => w
  end. *)

Fixpoint merge_bp_contn (p: participant) (b: Bp p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_bp_cont p b (merge_bp_contn p b w k)
  end.

(* Fixpoint merge_bp_contnB (p: participant) (b: Bp p) (w: siso) (n: nat): siso :=
  match n with
    | O    => w
    | S k  => merge_bp_contB p b (merge_bp_contnB p b w k)
  end. *)

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

Fixpoint actD (p: participant) (d: Dp p): list (participant * actT) :=
  match d with
    | dp_receive q x l s  => cons (q, rcv) nil
    | dp_mergea q x l s c => cons (q, rcv) (actD p c)
    | dp_send q x l s     => cons (q, snd) nil
    | dp_merge q x l s c  => cons (q, snd) (actD p c)
    | _                   => nil
  end.

Fixpoint actDn (p: participant) (d: Dp p) (n: nat): list (participant * actT) :=
  match n with
    | O   => nil
    | S k =>
      match d with
        | dp_receive q x l s    => cons (q, rcv) (actDn p d k)
        | dp_mergea q x l s cnt => (cons (q, rcv) (actD p cnt)) ++ (actDn p d k)
        | dp_send q x l s       => cons (q, snd) (actDn p d k)
        | dp_merge q x l s cnt  => (cons (q, snd) (actD p cnt)) ++ (actDn p d k)
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

Lemma bpend_ann: forall n p w, merge_bp_contn p (bp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_bp_cont p bp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma apend_ann: forall n p w, merge_ap_contn p (ap_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
Qed.

Lemma apend_an: forall p w, merge_ap_cont p (ap_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
Qed.

Lemma bpend_an: forall p w, merge_bp_cont p (bp_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_bp_cont p bp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma cpend_ann: forall n p w, merge_cp_contn p (cp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma cpend_an: forall p w, merge_cp_cont p (cp_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma dpend_ann: forall n p w, merge_dp_contn p (dp_end) w n = w.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. rewrite IHn. simpl.
       rewrite(siso_eq(merge_dp_cont p dp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma dpend_an: forall p w, merge_dp_cont p (dp_end) w = w.
Proof. intros.
       rewrite(siso_eq(merge_dp_cont p dp_end w)). simpl.
       destruct w; easy.
Qed.

Lemma mcomm: forall n p b w,
             merge_bp_contn p b (merge_bp_cont p b w) n =
             merge_bp_cont p b (merge_bp_contn p b w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mcomm2: forall n p a w,
             merge_ap_contn p a (merge_ap_cont p a w) n =
             merge_ap_cont p a (merge_ap_contn p a w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mcomm3: forall n p c w,
             merge_cp_contn p c (merge_cp_cont p c w) n =
             merge_cp_cont p c (merge_cp_contn p c w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mcomm4: forall n p d w,
             merge_dp_contn p d (merge_dp_cont p d w) n =
             merge_dp_cont p d (merge_dp_contn p d w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma mergeSw: forall p a l w,
merge_ap_cont p (listAp p (apList p a ++ l)) w =
merge_ap_cont p a (merge_ap_cont p (listAp p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(siso_eq((merge_ap_cont p ap_end w))). simpl.
       destruct w; easy.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p (listAp p (a :: l0)) w))).
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 (listAp p (a :: l0))) w)).
       simpl. easy.
       simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 (listAp p (apList p a ++ l))) w)).
       simpl. rewrite IHa.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (merge_ap_cont p (listAp p l) w))).
       simpl. easy.
       simpl.
       rewrite apend_an.
       easy.
Qed.

Lemma mergeSw2: forall p a l w,
merge_ap_cont p (listApA p (apListA p a ++ l)) w =
merge_ap_cont p a (merge_ap_cont p (listApA p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 ap_end) w)). simpl.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p ap_end w))).
       simpl. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 (listApA p (a :: l0))) w)).
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (merge_ap_cont p (listApA p (a :: l0)) w))).
       simpl. easy.
       rewrite(siso_eq(merge_ap_cont p (listApA p (apListA p (ap_merge q n s s0 a) ++ l)) w)).
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (merge_ap_cont p (listApA p l) w))).
       simpl.
       rewrite IHa. easy.
       setoid_rewrite(siso_eq(merge_ap_cont p (listApA p (apListA p ap_end ++ l)) w)) at 1.
       rewrite(siso_eq(merge_ap_cont p ap_end (merge_ap_cont p (listApA p l) w))).
       simpl. easy.
Qed.

Lemma mergeSw3: forall p b l w,
merge_bp_cont p (listBp p (bpList p b ++ l)) w =
merge_bp_cont p b (merge_bp_cont p (listBp p l) w).
Proof. intros p b.
       induction b; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 bp_end) w)). simpl.
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (merge_bp_cont p bp_end w))).
       simpl. easy.
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 (listBp p (b :: l0))) w )).
       rewrite(siso_eq(merge_bp_cont p (bp_receivea s s0 s1) (merge_bp_cont p (listBp p (b :: l0)) w))).
       simpl. easy.
       rewrite(siso_eq(merge_bp_cont p (listBp p (bpList p (bp_send q n s s0) ++ l)) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_send q n s s0) (merge_bp_cont p (listBp p l) w))).
       simpl. easy.
       rewrite(siso_eq(merge_bp_cont p (listBp p (bpList p (bp_mergea s s0 s1 b) ++ l)) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_mergea s s0 s1 b) (merge_bp_cont p (listBp p l) w))).
       simpl.
       rewrite IHb. easy.
       rewrite(siso_eq(merge_bp_cont p (listBp p (bpList p (bp_merge q n s s0 b) ++ l)) w)).
       rewrite(siso_eq(merge_bp_cont p (bp_merge q n s s0 b) (merge_bp_cont p (listBp p l) w))).
       simpl. rewrite IHb. easy.
       simpl. rewrite bpend_an. easy.
Qed.

Lemma mergeSw4: forall p a l w,
merge_cp_cont p (listCp p (cpList p a ++ l)) w =
merge_cp_cont p a (merge_cp_cont p (listCp p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst.
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 cp_end) w)). simpl.
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (merge_cp_cont p cp_end w))).
       simpl. rewrite cpend_an. easy.

       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 (listCp p (c :: l0))) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_receive q n s s0) (merge_cp_cont p (listCp p (c :: l0)) w))).
       simpl. easy.

       rewrite(siso_eq(merge_cp_cont p (listCp p (cpList p (cp_mergea q n s s0 a) ++ l)) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_mergea q n s s0 a) (merge_cp_cont p (listCp p l) w))).
       simpl. rewrite IHa. easy.

       rewrite(siso_eq(merge_cp_cont p (listCp p (cpList p (cp_send s s0 s1) ++ l)) w)).
       rewrite(siso_eq(merge_cp_cont p (cp_send s s0 s1) (merge_cp_cont p (listCp p l) w))).
       simpl. easy.

       setoid_rewrite(siso_eq(merge_cp_cont p (listCp p (cpList p (cp_merge s s0 s1 a) ++ l)) w)) at 1.
       rewrite(siso_eq(merge_cp_cont p (cp_merge s s0 s1 a) (merge_cp_cont p (listCp p l) w))).
       simpl. rewrite IHa. easy.
       simpl.
       rewrite cpend_an.
       easy.
Qed.

Lemma mergeSw5: forall p a l w,
merge_dp_cont p (listDp p (dpList p a ++ l)) w =
merge_dp_cont p a (merge_dp_cont p (listDp p l) w).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq l; intros.
       subst. simpl.
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q n s s0 dp_end) w)). simpl.
       rewrite(siso_eq(merge_dp_cont p (dp_receive q n s s0) (merge_dp_cont p dp_end w))).
       simpl. rewrite dpend_an. easy.

       rewrite(siso_eq(merge_dp_cont p (dp_mergea q n s s0 (listDp p (d :: l0))) w)).
       rewrite(siso_eq(merge_dp_cont p (dp_receive q n s s0) (merge_dp_cont p (listDp p (d :: l0)) w))).
       simpl. easy.

       rewrite(siso_eq(merge_dp_cont p (listDp p (dpList p (dp_mergea q n s s0 a) ++ l)) w )).
       rewrite(siso_eq(merge_dp_cont p (dp_mergea q n s s0 a) (merge_dp_cont p (listDp p l) w))).
       simpl. rewrite IHa. easy.

       rewrite(siso_eq(merge_dp_cont p (listDp p (dpList p (dp_send q n s s0) ++ l)) w )).
       rewrite(siso_eq(merge_dp_cont p (dp_send q n s s0) (merge_dp_cont p (listDp p l) w))).
       simpl. easy.

       setoid_rewrite(siso_eq(merge_dp_cont p (listDp p (dpList p (dp_merge q n s s0 a) ++ l)) w)) at 1.
       rewrite(siso_eq(merge_dp_cont p (dp_merge q n s s0 a) (merge_dp_cont p (listDp p l) w))).
       simpl. rewrite IHa. easy.
       simpl.
       rewrite dpend_an.
       easy.
Qed.

Lemma mergeeq: forall n p a w,
  merge_ap_cont p (ApnA p a n) w = merge_ap_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold ApnA. simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold ApnA. simpl.
       rewrite mergeSw. 
       easy.
Qed.

Lemma mergeeq2: forall n p a w,
  merge_ap_cont p (ApnA2 p a n) w = merge_ap_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold ApnA2. simpl.
       rewrite(siso_eq(merge_ap_cont p ap_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold ApnA2. simpl.
       rewrite mergeSw2. 
       easy.
Qed.

Lemma mergeeq3: forall n p b w,
  merge_bp_cont p (BpnA p b n) w = merge_bp_contn p b w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold BpnA. simpl.
       rewrite bpend_an. easy.
       simpl.
       rewrite <- IHn.

       unfold BpnA. simpl.
       rewrite mergeSw3. 
       easy.
Qed.

Lemma mergeeq4: forall n p a w,
  merge_cp_cont p (CpnA p a n) w = merge_cp_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold CpnA. simpl.
       rewrite(siso_eq(merge_cp_cont p cp_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold CpnA. simpl.
       rewrite mergeSw4. 
       easy.
Qed.

Lemma mergeeq5: forall n p a w,
  merge_dp_cont p (DpnA p a n) w = merge_dp_contn p a w n.
Proof. intro n.
       induction n; intros.
       simpl. unfold DpnA. simpl.
       rewrite(siso_eq(merge_dp_cont p dp_end w)). simpl.
       destruct w; easy.
       simpl.
       rewrite <- IHn.

       unfold DpnA. simpl.
       rewrite mergeSw5. 
       easy.
Qed.

Lemma hm1: forall p b w, act (merge_bp_cont p b w) = appendL (actB p b) (act w).
Proof. intros p b.
       induction b; intros.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_receivea s s0 s1) w))).
       rewrite(coseq_eq( appendL (actB p (bp_receivea s s0 s1)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_send q n s s0) w))).
       unfold coseq_id. simpl.
       rewrite(coseq_eq(appendL [(q, snd)] (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_mergea s s0 s1 b) w) )).
       rewrite(coseq_eq(appendL (actB p (bp_mergea s s0 s1 b)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHb. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_merge q n s s0 b) w))).
       rewrite(coseq_eq(appendL (actB p (bp_merge q n s s0 b)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHb. easy.

       rewrite(siso_eq(merge_bp_cont p bp_end w)).
       simpl. rewrite anl2.
       destruct w; easy.
Qed.

Lemma hm1a: forall p a w, act (merge_ap_cont p a w) = appendL (actA p a) (act w).
Proof. intros p a.
       induction a; intros.
       rewrite(coseq_eq(act(merge_ap_cont p (ap_receive q n s s0) w))).
       rewrite(coseq_eq( appendL (actA p (ap_receive q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_ap_cont p (ap_merge q n s s0 a) w))).
       rewrite(coseq_eq(appendL (actA p (ap_merge q n s s0 a)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHa. easy.

       rewrite(siso_eq(merge_ap_cont p ap_end w)).
       simpl. rewrite anl2.
       destruct w; easy.
Qed.

Lemma hm1c: forall p c w, act (merge_cp_cont p c w) = appendL (actC p c) (act w).
Proof. intros p c.
       induction c; intros.
       rewrite(coseq_eq(act (merge_cp_cont p (cp_receive q n s s0) w))).
       rewrite(coseq_eq(appendL (actC p (cp_receive q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_cp_cont p (cp_mergea q n s s0 c) w))).
       rewrite(coseq_eq(appendL (actC p (cp_mergea q n s s0 c)) (act w))).
       unfold coseq_id.
       simpl. rewrite IHc. easy.
       
       rewrite(coseq_eq(act (merge_cp_cont p (cp_send s s0 s1) w))).
       rewrite(coseq_eq(appendL (actC p (cp_send s s0 s1)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_cp_cont p (cp_merge s s0 s1 c) w))).
       rewrite(coseq_eq(appendL (actC p (cp_merge s s0 s1 c)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHc. easy.

       rewrite cpend_an. simpl. rewrite anl2.
       easy.
Qed.

Lemma hm1d: forall p c w, act (merge_dp_cont p c w) = appendL (actD p c) (act w).
Proof. intros p c.
       induction c; intros.
       rewrite(coseq_eq(act (merge_dp_cont p (dp_receive q n s s0) w) )).
       rewrite(coseq_eq(appendL (actD p (dp_receive q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_dp_cont p (dp_mergea q n s s0 c) w))).
       rewrite(coseq_eq(appendL (actD p (dp_mergea q n s s0 c)) (act w))).
       unfold coseq_id.
       simpl. rewrite IHc. easy.
       
       rewrite(coseq_eq(act (merge_dp_cont p (dp_send q n s s0) w))).
       rewrite(coseq_eq(appendL (actD p (dp_send q n s s0)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.
       
       rewrite(coseq_eq(act (merge_dp_cont p (dp_merge q n s s0 c) w))).
       rewrite(coseq_eq(appendL (actD p (dp_merge q n s s0 c)) (act w))).
       unfold coseq_id. simpl.
       rewrite IHc. easy.

       rewrite dpend_an. simpl. rewrite anl2.
       easy.
Qed.


Lemma unfcs: forall n p b, (actBn p b n ++ actB p b) = (actBn p b n.+1).
Proof. intro n.
       induction n; intros.
       destruct b; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p b).
       simpl in *.
       destruct b.
       simpl in *. rewrite IHn. easy.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl. easy.
Qed.

Lemma unfcsa: forall n p a, (actAn p a n ++ actA p a) = (actAn p a n.+1).
Proof. intro n.
       induction n; intros.
       destruct a; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p a).
       simpl in *.
       destruct a.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.
       simpl. easy.
Qed.

Lemma unfcsc: forall n p c, (actCn p c n ++ actC p c) = (actCn p c n.+1).
Proof. intro n.
       induction n; intros.
       destruct c; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p c).
       simpl in *.
       destruct c.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       rewrite <- app_comm_cons.
       rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl. easy.
Qed.

Lemma unfcsd: forall n p c, (actDn p c n ++ actD p c) = (actDn p c n.+1).
Proof. intro n.
       induction n; intros.
       destruct c; simpl; try easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       specialize(IHn p c).
       simpl in *.
       destruct c.
       simpl in *. rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       rewrite <- app_comm_cons.
       rewrite IHn. easy.

       simpl in *.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       rewrite app_comm_cons.
       f_equal.
       rewrite <- IHn. easy.

       simpl. easy.
Qed.

Lemma hm2: forall n p, actBn p bp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma hm2a: forall n p, actAn p ap_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma hm2c: forall n p, actCn p cp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.

Lemma hm2d: forall n p, actDn p dp_end n = [].
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. easy.
Qed.


Lemma h0: forall (n: nat) p b w, 
act (merge_bp_contn p b w n) = appendL (actBn p b n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p b (merge_bp_contn p b w 1)).
       simpl in IHn.
       rewrite mcomm in IHn.
       rewrite IHn.
       rewrite hm1.
       rewrite stream.app_assoc.
       f_equal.
       destruct b; try easy.
       rewrite unfcs.
       simpl. easy.

       rewrite unfcs.
       simpl. easy.

       rewrite unfcs.
       simpl. easy.

       rewrite unfcs.
       simpl. easy.

       simpl.
       rewrite hm2.
       easy. 
Qed.

Lemma h1: forall (n: nat) p a w, 
act (merge_ap_contn p a w n) = appendL (actAn p a n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p a (merge_ap_contn p a w 1)).
       simpl in IHn.
       rewrite mcomm2 in IHn.
       rewrite IHn.
       rewrite hm1a.
       rewrite stream.app_assoc.
       f_equal.
       destruct a; try easy.
       rewrite unfcsa.
       simpl. easy.

       rewrite unfcsa.
       simpl. easy.

       simpl.
       rewrite hm2a.
       easy. 
Qed.

Lemma hh2: forall n p s s0 s1, actCn p (cp_send s s0 s1) n ++ actC p (cp_send s s0 s1) = ((s, snd) :: actCn p (cp_send s s0 s1) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. f_equal.
       rewrite IHn. easy.
Qed.

Lemma hh2d: forall n p q s s0 n0, actDn p (dp_send q n0 s s0) n ++ [(q, snd)] = ((q, snd) :: actDn p (dp_send q n0 s s0) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl. f_equal.
       rewrite IHn. easy.
Qed.

Lemma hh3: forall n p c s s0 s1, 
actCn p (cp_merge s s0 s1 c) n ++ ((s, snd) :: actC p c)%SEQ =
((s, snd) :: actC p c)%SEQ ++ actCn p (cp_merge s s0 s1 c) n.
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite app_nil_r. easy.

       simpl. f_equal.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       f_equal.
       rewrite IHn. easy.
Qed.

Lemma hh3d: forall n p q c s s0 n0, 
actDn p (dp_merge q n0 s s0 c) n ++ actD p (dp_merge q n0 s s0 c) =
((q, snd) :: actD p c ++ actDn p (dp_merge q n0 s s0 c) n)%SEQ.
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite app_comm_cons.
       rewrite app_nil_r. easy.

       simpl. f_equal.
       rewrite <- List.app_assoc.
       rewrite app_comm_cons.
       f_equal.
       rewrite IHn. easy.

       rewrite <- app_comm_cons.
       rewrite <- IHn.
       simpl. easy.
Qed.

Lemma h2: forall (n: nat) p c w, 
act (merge_cp_contn p c w n) = appendL (actCn p c n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p c (merge_cp_contn p c w 1)).
       simpl in IHn.
       rewrite mcomm3 in IHn.
       rewrite IHn.
       rewrite hm1c.
       rewrite stream.app_assoc.
       f_equal.
       destruct c; try easy.
       rewrite unfcsc.
       simpl. easy.

       rewrite unfcsc.
       simpl. easy.

       simpl.
       rewrite hh2. easy.

       rewrite hh3. simpl.
       rewrite app_comm_cons.
       easy.

       simpl.
       rewrite hm2c.
       easy. 
Qed.

Lemma h3: forall (n: nat) p c w, 
act (merge_dp_contn p c w n) = appendL (actDn p c n) (act w).
Proof. intro n.
       induction n; intros.
       simpl. rewrite anl2. easy.
       simpl.
       pose proof IHn as IHnn.
       specialize(IHn p c (merge_dp_contn p c w 1)).
       simpl in IHn.
       rewrite mcomm4 in IHn.
       rewrite IHn.
       rewrite hm1d.
       rewrite stream.app_assoc.
       f_equal.
       destruct c; try easy.
       rewrite unfcsd.
       simpl. easy.

       rewrite unfcsd.
       simpl. easy.

       simpl.
       rewrite hh2d. easy.

       rewrite hh3d. simpl.
       rewrite app_comm_cons.
       easy.

       simpl.
       rewrite hm2d.
       easy. 
Qed.

Definition merge_bp_contnA (p: participant) (b: Bp p) (w: st) (n: nat): st :=
merge_bp_cont p (Bpn p b n) w.

Inductive cosetIncL (R: coseq (participant * actT) -> list (participant * actT) -> Prop):
                        coseq (participant * actT) -> list (participant * actT) -> Prop :=
  | c_nil : forall ys, cosetIncL R (Delay conil) ys
  | c_incl: forall x xs ys,
            List.In x ys ->
            R xs ys ->
            cosetIncL R (Delay (cocons x xs)) ys.

Definition cosetIncLC := fun s1 s2 => paco2 cosetIncL bot2 s1 s2.

Lemma cosetIncL_mon: monotone2 cosetIncL.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - specialize (c_incl r'); intro HS.
         apply HS.
         apply H.
         apply LE, H0.
Qed.

Inductive cosetIncR: list (participant * actT) -> coseq (participant * actT) -> Prop :=
  | l_nil : forall ys, cosetIncR nil ys
  | l_incl: forall x xs ys,
            CoInR x ys ->
            cosetIncR xs ys ->
            cosetIncR (x::xs) ys.

Definition act_eq (w w': st) := forall a, CoIn a (act w) <-> CoIn a (act w').
Definition act_eqA (w w': st) := forall a, CoInR a (act w) <-> CoInR a (act w').

Definition act_neq (w w': st) := (exists a, CoInR a (act w) /\ CoNInR a (act w') \/ CoInR a (act w') /\ CoNInR a (act w)).

(* Definition act_eqB (w w': siso) := forall a, CoIn a (actC w) <-> CoIn a (actC w'). *)

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
(*   | _sref_in : forall w w' p l s s',
                      subsort s' s -> 
                      seq w w' ->
                      refinementR seq (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])

  | _sref_out: forall w w' p l s s',
                      subsort s s' ->
                      seq w w' ->
                      refinementR seq (st_send p [(l,s,w)]) (st_send p [(l,s',w')]) *)

  | _sref_a  : forall w w' p l s s' a n,
                      subsort s s' ->
                      seq w (merge_ap_contn p a w' n)  ->
                      act_eq w (merge_ap_contn p a w' n) ->
                      refinementR seq (st_receive p [(l,s',w)]) (merge_ap_contn p a (st_receive p [(l,s,w')]) n)

  | _sref_b  : forall w w' p l s s' b n,
                      subsort s s' ->
                      seq w (merge_bp_contn p b w' n) ->
                      act_eq w (merge_bp_contn p b w' n) ->
                      refinementR seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | _sref_end: refinementR seq st_end st_end.

(* rewriting issues *)
#[export]
Declare Instance Equivalence_seq_genR (r: st -> st -> Prop): Equivalence r -> Equivalence (refinementR r).

Definition refinement: st -> st -> Prop := fun s1 s2 => paco2 refinementR bot2 s1 s2.

Notation "x '~<' y" := (refinement x y) (at level 50, left associativity).

Lemma refinementR_mon: monotone2 refinementR.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
(*        - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0. *)
       - specialize(_sref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.

(* rewriting issues *)
#[export]
Declare Instance Equivalence_ref_eqi: Equivalence refinement.


Inductive refinementRC (seq: st -> st -> Prop): st -> st -> Prop :=
  | _sref_inC : forall w w' p l s s',
                       subsort s' s -> 
                       seq w w' ->
                       refinementRC seq (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])

  | _sref_outC: forall w w' p l s s',
                       subsort s s' ->
                       seq w w' ->
                       refinementRC seq (st_send p [(l,s,w)]) (st_send p [(l,s',w')])

  | _sref_aC  : forall w w' p l s s' c n,
                       subsort s' s ->
                       seq w (merge_cp_contn p c w' n)  ->
                       act_eq w (merge_cp_contn p c w' n) ->
                       refinementRC seq (st_receive p [(l,s',w)]) (merge_cp_contn p c (st_receive p [(l,s,w')]) n)

  | _sref_bC  : forall w w' p l s s' b n,
                       subsort s s' ->
                       seq w (merge_bp_contn p b w' n) ->
                       act_eq w (merge_bp_contn p b w' n) ->
                       refinementRC seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)

(*   | _sref_cC  : forall w w' p l s s' c n,
                       subsort s' s ->
                       seq w (merge_cp_contn p c w' n) ->
                       act_eq w (merge_cp_contn p c w' n) ->
                       refinementRC seq (st_send p [(l,s,w)]) (merge_cp_contn p c (st_send p [(l,s',w')]) n) *)

  | _sref_endC: refinementRC seq st_end st_end.

(* rewriting issues *)
#[export]
Declare Instance Equivalence_seq_genRC (r: st -> st -> Prop): Equivalence r -> Equivalence (refinementRC r).

Definition refinementC: st -> st -> Prop := fun s1 s2 => paco2 refinementRC bot2 s1 s2.

Notation "x '~~<' y" := (refinementC x y) (at level 50, left associativity).

Lemma refinementRC_mon: monotone2 refinementRC.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0.
       - specialize(_sref_aC r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_bC r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
(*        - specialize(_sref_cC r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0. *)
       - constructor.
Qed.

(* rewriting issues *)
#[export]
Declare Instance Equivalence_ref_eqic: Equivalence refinementC.


Inductive refinementRN (seq: siso -> siso -> Prop): siso -> siso -> Prop :=
  | _sref_inN : forall w w' p l s s' P Q,
                       subsort s' s -> 
                       seq w w' ->
                       refinementRN seq 
                       (mk_siso (st_receive p [(l,s,(@und w))]) P) (mk_siso (st_receive p [(l,s',(@und w'))]) Q)
  | _sref_outN: forall w w' p l s s' P Q,
                       subsort s s' ->
                       seq w w' ->
                       refinementRN seq (mk_siso (st_send p [(l,s,(@und w))]) P) (mk_siso (st_send p [(l,s',(@und w'))]) Q)
  | _sref_aN  : forall w w' p l s s' a n P Q R,
                       subsort s s' ->
                       seq w (mk_siso (merge_ap_contn p a (@und w') n) P)  ->
                       act_eq (@und w) (merge_ap_contn p a (@und w') n) ->
                       refinementRN seq (mk_siso (st_receive p [(l,s',(@und w))]) Q)
                                        (mk_siso (merge_ap_contn p a (st_receive p [(l,s,(@und w'))]) n) R)
  | _sref_bN  : forall w w' p l s s' b n P Q R ,
                       subsort s s' ->
                       seq w (mk_siso (merge_bp_contn p b (@und w') n) P) ->
                       act_eq (@und w) (merge_bp_contn p b (@und w') n) ->
                       refinementRN seq (mk_siso (st_send p [(l,s,(@und w))]) Q)
                                        (mk_siso (merge_bp_contn p b (st_send p [(l,s',(@und w'))]) n) R)
  | _sref_endA: forall P, refinementRN seq (mk_siso st_end P) (mk_siso st_end P).

Definition refinementN s1 s2 := paco2 refinementRN bot2 s1 s2.


Lemma refinementRN_mon: monotone2 refinementRN.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0.
       - specialize(_sref_aN r'); intro Ha. eapply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_bN r'); intro Ha. eapply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.

(* Lemma sisoE: forall W W', refinementN W W' -> (@und W) ~< (@und W').
Proof. intros (W, Pw) (W', Pw').
       revert W W' Pw Pw'.
       simpl.
       pcofix CIH.
       intros  W W' Pw Pw' H.
       punfold H.
       inversion H.
       destruct w as (w, Pww).
       destruct w' as (w', Pww').
       simpl in *.
       pfold.
       apply _sref_in. easy.
       right. simpl in *.
       apply (CIH w w' Pww Pww').
       pfold. simpl.
       unfold upaco2 in H3.
       destruct H3.
       punfold H3.
       apply refinementRN_mon.
       easy.
       destruct w as (w, Pww).
       destruct w' as (w', Pww').
       simpl in *.
       pfold.
       apply _sref_out. easy.
       right. simpl in *.
       apply (CIH w w' Pww Pww').
       pfold. simpl.
       unfold upaco2 in H3.
       destruct H3.
       punfold H3.
       apply refinementRN_mon.
       easy.
       destruct w as (w, Pww).
       destruct w' as (w', Pww').
       simpl in *.
       pfold. simpl.
       apply _sref_a. easy.
       right.
       apply (CIH w (merge_ap_contn p a w' n) Pww P).
       pfold. simpl.
       unfold upaco2 in H3.
       destruct H3.
       punfold H3. 
       apply refinementRN_mon.
       easy.
       easy.
       destruct w as (w, Pww).
       destruct w' as (w', Pww').
       simpl in *.
       pfold. simpl.
       apply _sref_b. easy.
       right.
       apply (CIH w (merge_bp_contn p b w' n) Pww P).
       pfold. simpl.
       unfold upaco2 in H3.
       destruct H3.
       punfold H3. 
       apply refinementRN_mon.
       easy. 
       easy.
       pfold. constructor.
       apply refinementRN_mon.
Qed. *)

(*
forall w w' p l s s' a n,
                      subsort s s' ->
                      seq w (merge_ap_contn p a w' n)  ->
                      (exists L,
                         cosetIncLC (act w) L /\
                         cosetIncLC (act (merge_ap_contn p a w' n)) L /\
                         cosetIncR L (act w) /\
                         cosetIncR L (act (merge_ap_contn p a w' n))
                      ) ->
                      refinementR seq (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)

 forall w w' p l s s' b n,
                      subsort s s' ->
                      seq w (merge_bp_contn p b w' n) ->
                      (exists L, 
                         cosetIncLC (act w) L /\
                         cosetIncLC (act (merge_bp_contn p b w' n)) L /\
                         cosetIncR L (act w) /\
                         cosetIncR L (act (merge_bp_contn p b w' n))
                      ) ->
                      refinementR seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)

 forall w w' p l s s' b n,
                      subsort s s' ->
                      seq w (merge_bp_contn p b w' n) ->
                      act_eq w (merge_bp_contn p b w' n) ->
                      refinementR seq (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
*)

(* Inductive refinementRA (seq: siso -> siso -> Prop): siso -> siso -> Prop :=
  | _sref_inA : forall w w' p l s s',
                       subsort s' s -> 
                       seq w w' ->
                       refinementRA seq (siso_receive p (l,s,w)) (siso_receive p (l,s',w'))

  | _sref_outA: forall w w' p l s s',
                       subsort s s' ->
                       seq w w' ->
                       refinementRA seq (siso_send p (l,s,w)) (siso_send p (l,s',w'))

  | _sref_aA  : forall w w' p l s s' a n,
                       subsort s s' ->
                       seq w (merge_ap_contnB p a w' n)  ->
                       act_eqB w (merge_ap_contnB p a w' n) ->
                       refinementRA seq (siso_receive p (l,s',w)) (merge_ap_contnB p a (siso_receive p (l,s,w')) n)

  | _sref_bA  : forall w w' p l s s' b n,
                      subsort s s' ->
                      seq w (merge_bp_contnB p b w' n) ->
                      act_eqB w (merge_bp_contnB p b w' n) ->
                      refinementRA seq (siso_send p (l,s,w)) (merge_bp_contnB p b (siso_send p (l,s',w')) n)
  | _sref_endA: refinementRA seq siso_end siso_end.

Definition refinementRAC: siso -> siso -> Prop := fun s1 s2 => paco2 refinementRA bot2 s1 s2.

Notation "x '~<A' y" := (refinementRAC x y) (at level 50, left associativity). *)


(* Lemma mergeeqB2: forall n p a w,
  merge_ap_cont2 p (Apn2 p a n) w = merge_ap_contn2 p a w n.
Proof. intros.
       unfold merge_ap_contn2. easy.
Qed.

Lemma merge_eqB2: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont2 p a1 (p & [(l1, s1, w1)]) =
  merge_ap_cont2 p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a.
       induction a; intros.
       simpl.
       case_eq a2; intros.
       subst. 
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q n s s0) (p & [(l1, s1, w1)]))) in H.
       rewrite(siso_eq(merge_ap_cont2 p (ap_merge2 q0 n0 s3 s4 a) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. subst. *)

(* Lemma merge_eqB2: forall p a1 a2 l1 l2 s1 s2 w1 w2,
  merge_ap_cont2 p a1 (p & [(l1, s1, w1)]) =
  merge_ap_cont2 p a2 (p & [(l2, s2, w2)]) -> (p & [(l1, s1, w1)]) = (p & [(l2, s2, w2)]).
Proof. intros p a1.
       induction a1; intros.
       simpl.
       case_eq a2; intros.  
       subst. 
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       rewrite(siso_eq(merge_ap_cont2 p (ap_merge2 q0 n0 s3 s4 a) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       subst.
       case_eq a; intros.
       subst.
       inversion H.
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q n1 s s0) (p & [(l2, s2, w2)]))) in H1.
       simpl in H1. inversion H1. subst. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont2 p (ap_merge2 q n1 s s0 a0) (p & [(l2, s2, w2)]))) in H4.
       simpl in H4. inversion H4. subst. easy.
       
       rewrite(siso_eq(merge_ap_cont2 p (ap_merge2 q n s s0 a1) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont2 p (ap_receive2 q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. subst.
       rewrite H4.
       specialize(IHa ((ap_receive2 q0 n0 s3 s4)) l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       
       subst. rewrite apend_an in H. inversion H. subst. easy.
       subst. rewrite apend_an in H.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l1, s1, w1)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a) (p & [(l1, s1, w1)]))) in H.
       simpl in H.
       case_eq a2; intros. subst.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q0 n0 s3 s4) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H. rewrite H4.
       specialize(IHa (ap_end) l1 l2 s1 s2 w1 w2).
       apply IHa.
       rewrite apend_an. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q0 n0 s3 s4 a0) (p & [(l2, s2, w2)]))) in H.
       simpl in H.
       inversion H.
       specialize(IHa a0 l1 l2 s1 s2 w1 w2).
       apply IHa. easy.
       subst.
       rewrite(siso_eq(merge_ap_cont p ap_end (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       destruct a2.
       rewrite(siso_eq(merge_ap_cont p (ap_receive q n s s0) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite(siso_eq(merge_ap_cont p (ap_merge q n s s0 a2) (p & [(l2, s2, w2)]))) in H.
       simpl in H. inversion H. subst. easy.
       rewrite apend_an in H.
       easy.
Qed.
 *)
 

