Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.types.local.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.

Inductive dir: Type := rcv: dir | snd: dir.

Definition direqb (a1 a2: dir): bool :=
  match (a1, a2) with
    | (rcv,rcv)
    | (snd,snd) => true
    | _         => false
  end.

Lemma dir_dec: forall a1 a2, direqb a1 a2 = true \/ direqb a1 a2 = false.
Proof. intros a1 a2.
       case_eq a1; case_eq a2; intros.
       - left. easy.
       - right. easy.
       - right. easy.
       - left. easy.
Qed.

Lemma dir_eqb_eq: forall a1 a2, direqb a1 a2 = true -> a1 = a2.
Proof. intros a1 a2 Ha.
       case_eq a1; case_eq a2; intros; try easy.
       - subst. easy.
       - subst. easy.
Qed.

Lemma dir_neqb_neq: forall a1 a2, direqb a1 a2 = false -> a1 <> a2.
Proof. intros a1 a2 Ha.
       case_eq a1; case_eq a2; intros; try easy.
       - subst. easy.
       - subst. easy.
Qed.

CoFixpoint act (t: st): coseq (participant * dir) :=
  match t with
    | st_receive p [(l,s,w')] => Delay (cocons (p, rcv) (act w'))
    | st_send p [(l,s,w')]    => Delay (cocons (p, snd) (act w'))
    | _                       => Delay conil
  end.

CoFixpoint actls (t: st): coseq (participant * dir * label * local.sort) :=
  match t with
    | st_receive p [(l,s,w')] => Delay (cocons (p, rcv, l, s) (actls w'))
    | st_send p [(l,s,w')]    => Delay (cocons (p, snd, l, s) (actls w'))
    | _                       => Delay conil
  end.

CoFixpoint actl (t: st): coseq (participant * dir * label) :=
  match t with
    | st_receive p [(l,s,w')] => Delay (cocons (p, rcv, l) (actl w'))
    | st_send p [(l,s,w')]    => Delay (cocons (p, snd, l) (actl w'))
    | _                       => Delay conil
  end.
  
(***********************)

(* inductive membership check *)
Inductive coseqIn: (participant * dir) -> coseq (participant * dir) -> Prop :=
  | CoInSplit1 x xs y ys: force xs = cocons y ys -> x = y  -> coseqIn x xs
  | CoInSplit2 x xs y ys: force xs = cocons y ys -> x <> y -> coseqIn x ys -> coseqIn x xs.

Inductive coseqInLS: (participant * dir * label * local.sort) -> coseq (participant * dir * label *local.sort) -> Prop :=
  | CoInSplit1ls x xs y ys: force xs = cocons y ys -> x = y  -> coseqInLS x xs
  | CoInSplit2ls x xs y ys: force xs = cocons y ys -> x <> y -> coseqInLS x ys -> coseqInLS x xs.

Inductive coseqInl: (participant * dir * label) -> coseq (participant * dir * label) -> Prop :=
  | CoInSplit1l x xs y ys: force xs = cocons y ys -> x = y  -> coseqInl x xs
  | CoInSplit2l x xs y ys: force xs = cocons y ys -> x <> y -> coseqInl x ys -> coseqInl x xs.
  
(* alternative coinductive membership check measures *)
Inductive coseqInL (R: coseq (participant * dir) -> list (participant * dir) -> Prop): 
                    coseq (participant * dir) -> list (participant * dir) -> Prop :=
  | c_nil : forall ys, coseqInL R (Delay conil) ys
  | c_incl: forall x xs ys,
            List.In x ys ->
            R xs ys ->
            coseqInL R (Delay (cocons x xs)) ys.

Definition coseqInLC := fun s1 s2 => paco2 (coseqInL) bot2 s1 s2.

Lemma coseqInLC_mon: monotone2 (coseqInL).
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - constructor.
       - specialize (c_incl r'); intro HS.
         apply HS.
         apply H.
         apply LE, H0.
Qed.

Inductive coseqInR: list (participant * dir) -> coseq (participant * dir) -> Prop :=
  | l_nil : forall ys, coseqInR nil ys
  | l_incl: forall x xs ys,
            coseqIn x ys ->
            coseqInR xs ys ->
            coseqInR (x::xs) ys.

Definition act_eq (w w': st) := forall a, coseqIn a (act w) <-> coseqIn a (act w').

Definition act_neq (w w': st) := (exists a, coseqIn a (act w) /\ (coseqIn a (act w') -> False) \/ coseqIn a (act w') /\ (coseqIn a (act w) -> False)).

Lemma act_eq_neq: forall w w', (act_eq w w' -> False) -> act_neq w w'.
Proof. intros.
       unfold act_eq, act_neq in *.
       apply not_all_ex_not in H.
       destruct H as (a, H).
       exists a.
       unfold iff in H.
       apply not_and_or in H.
       destruct H as [H | H].
       apply imply_to_and in H.
       left. easy.
       apply imply_to_and in H.
       right. easy.
Qed.

Lemma listEq: forall {A: Type} (l1 l2: list A), l1 = l2 -> (forall x, List.In x l1 <-> List.In x l2).
Proof. intros. subst. easy. Qed.

(***********************)

CoFixpoint Wtriv := st_send "p" [("l1"%string,I, st_receive "p" [("l2"%string,I, st_send "q" [("l3"%string,I,Wtriv)])])].
Definition Ltriv := ("p"%string, rcv) :: ("p"%string, snd) :: ("q"%string, snd) :: nil. 

Example smallexL: coseqInLC (act Wtriv) Ltriv.
Proof. pcofix CIH.
       pfold.
       rewrite(coseq_eq (act Wtriv)). unfold Ltriv. unfold coseq_id. simpl.
       apply c_incl. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" & [("l2"%string, I, "q" ! [("l3"%string, I, Wtriv)])]))).
       unfold coseq_id. simpl.
       apply c_incl. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("q" ! [("l3"%string, I, Wtriv)]))). unfold coseq_id. simpl.
       apply c_incl. simpl. right. right. left. easy.
       right. exact CIH.
Qed. 

Example smallexR: coseqInR Ltriv (act Wtriv).
Proof. rewrite(coseq_eq (act Wtriv)). unfold Ltriv. unfold coseq_id. simpl.
       apply l_incl. simpl.
       apply CoInSplit2 with (y := ("p"%string, snd)) (ys := (act ("p" & [("l2"%string, I, "q" ! [("l3"%string, I, Wtriv)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" & [("l2"%string, I, "q" ! [("l3"%string, I, Wtriv)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p"%string, rcv)) (ys := (act ("q" ! [("l3"%string, I, Wtriv)]))). simpl. easy. easy.
       apply l_incl. simpl.
       rewrite(coseq_eq(act ("p" & [("l2"%string, I, "q" ! [("l3"%string, I, Wtriv)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p"%string, snd)) (ys := ({| force := cocons ("p"%string, rcv) (act ("q" ! [("l3"%string, I, Wtriv)])) |})). simpl. easy. easy.
       apply l_incl. simpl.
       rewrite(coseq_eq(act ("p" & [("l2"%string, I, "q" ! [("l3"%string, I, Wtriv)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p"%string, snd)) (ys := ({| force := cocons ("p"%string, rcv) (act ("q" ! [("l3"%string, I, Wtriv)])) |})). simpl. easy. easy.
       apply CoInSplit2 with (y := ("p"%string, rcv)) (ys := (act ("q" ! [("l3"%string, I, Wtriv)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("q" ! [("l3"%string, I, Wtriv)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("q"%string, snd)) (ys := (act Wtriv)). simpl. easy. easy.
       apply l_nil.
Qed.
 
(***********************)

Inductive Ap (p: participant): Type :=
  | ap_receive: forall q, p <> q -> label -> local.sort -> Ap p
  | ap_merge  : forall q, p <> q -> label -> local.sort -> Ap p -> Ap p
  | ap_end    : Ap p.

Arguments ap_receive {_} _ _ _ _.
Arguments ap_merge {_} _ _ _ _.
Arguments ap_end {_}.

Inductive Apf: Type :=
  | apf_end    : Apf
  | apf_receive: participant -> label -> local.sort -> Apf -> Apf.

Fixpoint isInA (a: Apf) p: bool :=
  match a with
    | apf_end                => false
    | apf_receive q l' s' a' => eqb p q || isInA a' p
  end.

Definition eqbs s1 s2: bool :=
  match (s1, s2) with
    | (sunit, sunit) => true
    | (sbool, sbool) => true
    | (snat, snat)   => true
    | (sint, sint)   => true
    | _              => false
  end.

Fixpoint isInAsl (a: Apf) p l s: bool :=
  match a with
    | apf_end                => false
    | apf_receive q l' s' a' => (eqb p q && eqb l l' && eqbs s s') || isInAsl a' p l s
  end.

Fixpoint isInAl (a: Apf) p l: bool :=
  match a with
    | apf_end                => false
    | apf_receive q l' s' a' => (eqb p q && eqb l l') || isInAl a' p l
  end.

CoFixpoint merge_apf_cont (a: Apf) (w: st): st :=
  match a with
    | apf_end              => w
    | apf_receive q l s a' => st_receive q [(l,s,(merge_apf_cont a' w))]
  end.

Fixpoint merge_apf_contn (a: Apf) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_apf_cont a (merge_apf_contn a w k)
  end.

Fixpoint Apf_merge (a: Apf) (b: Apf): Apf :=
  match a with
    | apf_receive q l s a' => apf_receive q l s (Apf_merge a' b)
    | apf_end              => b
  end.

Fixpoint Apf_eqb (a: Apf) (b: Apf): bool :=
  match (a, b) with
    | (apf_receive p l s a', apf_receive q l' s' b') => eqb p q && eqb l l' && eqbs s s' && Apf_eqb a' b'
    | (apf_end, apf_end)                             => true
    | _                                              => false
  end.

Fixpoint ApnA3 (a: Apf) (n: nat): Apf :=
  match n with
    | O   => apf_end
    | S O => a
    | S k => Apf_merge a (ApnA3 a k)
  end.

Inductive Bpf: Type :=
  | bpf_receive: participant -> label -> local.sort -> Bpf -> Bpf
  | bpf_send   : participant -> label -> local.sort -> Bpf -> Bpf
  | bpf_end    : Bpf.

Fixpoint isInB (b: Bpf) p: bool :=
  match b with
    | bpf_receive q l s b' => isInB b' p
    | bpf_send q l s b'    => eqb p q || isInB b' p
    | _                    => false
  end.

CoFixpoint merge_bpf_cont (b: Bpf) (w: st): st :=
  match b with 
    | bpf_end             => w
    | bpf_receive q l s c => st_receive q [(l,s,(merge_bpf_cont c w))]
    | bpf_send q l s c    => st_send q [(l,s,(merge_bpf_cont c w))]
  end.

Fixpoint merge_bpf_contn (b: Bpf) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_bpf_cont b (merge_bpf_contn b w k)
  end.

Fixpoint isBpSend (b: Bpf): bool :=
  match b with
    | bpf_receive q l s c => isBpSend c
    | bpf_send q l s c    => true
    | _                   => false
  end.

Fixpoint Bpf_merge (a: Bpf) (b: Bpf): Bpf :=
  match a with
    | bpf_receive q l s a' => bpf_receive q l s (Bpf_merge a' b)
    | bpf_send q l s a'    => bpf_send q l s (Bpf_merge a' b)
    | bpf_end              => b
  end.

Fixpoint BpnB3 (b: Bpf) (n: nat): Bpf :=
  match n with
    | O   => bpf_end
    | S O => b
    | S k => Bpf_merge b (BpnB3 b k)
  end.

Fixpoint Bpf_eqb (a: Bpf) (b: Bpf): bool :=
  match (a, b) with
    | (bpf_receive p l s a', bpf_receive q l' s' b') => eqb p q && eqb l l' && eqbs s s' && Bpf_eqb a' b'
    | (bpf_send p l s a', bpf_send q l' s' b')       => eqb p q && eqb l l' && eqbs s s' && Bpf_eqb a' b'
    | (bpf_end, bpf_end)                             => true
    | _                                              => false
  end.
  
(* Definition Apre (p: participant) (a: Apf) := isInA a p = false.  *)

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

CoFixpoint fromAp (p: participant) (a: Ap p): st :=
  match a with
    | ap_receive q x l s => st_receive q [(l,s,st_end)]
    | ap_merge q x l s c => st_receive q [(l,s,(fromAp p c))]
    | ap_end             => st_end
  end.

 Fixpoint actA (p: participant) (a: Ap p): list (participant * dir) :=
  match a with
    | ap_receive q x l s => cons (q, rcv) nil
    | ap_merge q x l s c => cons (q, rcv) (actA p c)
    | _                  => nil
  end.

Fixpoint actAn (p: participant) (a: Ap p) (n: nat): list (participant * dir) :=
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
  | bp_receivea: participant -> label -> local.sort -> Bp p
  | bp_send    : forall q: participant, p <> q -> label -> local.sort -> Bp p
  | bp_mergea  : participant -> label -> local.sort -> Bp p -> Bp p
  | bp_merge   : forall q: participant, p <> q -> label -> local.sort -> Bp p -> Bp p
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

Fixpoint actB (p: participant) (b: Bp p): list (participant * dir) :=
  match b with
    | bp_receivea q l s  => cons (q, rcv) nil
    | bp_send q x l s    => cons (q, snd) nil
    | bp_mergea q l s c  => cons (q, rcv) (actB p c)
    | bp_merge q x l s c => cons (q, snd) (actB p c)
    | _                  => nil
  end.

Fixpoint actBn (p: participant) (b: Bp p) (n: nat): list (participant * dir) :=
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

Inductive Cp (p: participant): Type :=
  | cp_receive: forall q, p <> q -> label -> local.sort -> Cp p
  | cp_mergea : forall q, p <> q -> label -> local.sort -> Cp p -> Cp p
  | cp_send   : participant -> label -> local.sort -> Cp p
  | cp_merge  : participant -> label -> local.sort -> Cp p -> Cp p
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

Fixpoint actC (p: participant) (c: Cp p): list (participant * dir) :=
  match c with
    | cp_receive q x l s  => cons (q, rcv) nil
    | cp_mergea q x l s c => cons (q, rcv) (actC p c)
    | cp_send q l s       => cons (q, snd) nil
    | cp_merge q l s c    => cons (q, snd) (actC p c)
    | _                   => nil
  end.

Fixpoint actCn (p: participant) (c: Cp p) (n: nat): list (participant * dir) :=
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

Fixpoint isInCp (p: participant) (c: Cp p): bool :=
  match c with
    | cp_send q l s       => true
    | cp_merge q l s c    => true
    | cp_mergea q H l s c => isInCp p c
    | _                   => false
  end.

Lemma Cp2Ap: forall p c w,
  isInCp p c = false ->
  exists a, merge_cp_cont p c w = merge_ap_cont p a w.
Proof. intros p c.
       induction c; intros.
       - simpl in *. 
         exists (ap_receive q n s s0).
         rewrite(st_eq(merge_cp_cont p (cp_receive q n s s0) w)).
         rewrite(st_eq(merge_ap_cont p (ap_receive q n s s0) w)).
         simpl. easy.
       - simpl in *.
         specialize(IHc w H).
         destruct IHc as (a,IHc).
         exists(ap_merge q n s s0 a).
         rewrite(st_eq(merge_cp_cont p (cp_mergea q n s s0 c) w)).
         rewrite(st_eq(merge_ap_cont p (ap_merge q n s s0 a) w)).
         simpl.
         rewrite IHc. easy.
       - simpl in *. easy.
       - simpl in *. easy.
       - simpl in *. exists ap_end. 
         rewrite(st_eq( merge_ap_cont p ap_end w)).
         rewrite(st_eq(merge_cp_cont p cp_end w )).
         simpl. easy.
Qed.

Inductive Dp: Type :=
  | dp_receive: participant -> label -> local.sort -> Dp
  | dp_send   : participant -> label -> local.sort -> Dp
  | dp_mergea : participant -> label -> local.sort -> Dp -> Dp
  | dp_merge  : participant -> label -> local.sort -> Dp -> Dp
  | dp_end    : Dp.

Inductive Dpf: Type :=
  | dpf_receive: participant -> label -> local.sort -> Dpf -> Dpf
  | dpf_send   : participant -> label -> local.sort -> Dpf -> Dpf
  | dpf_end    : Dpf.

(* Arguments dp_merge {_}  _ _ _.
Arguments dp_mergea {_} _ _ _. *)
(* Arguments dp_receive _ _ _.
Arguments dp_send _ _ _. *)


CoFixpoint merge_dp_cont (d: Dp) (w: st): st :=
  match d with 
    | dp_receive q l s  => st_receive q [(l,s,w)]
    | dp_send q l s     => st_send q [(l,s,w)]
    | dp_mergea q l s c => st_receive q [(l,s,(merge_dp_cont c w))]
    | dp_merge q l s c  => st_send q [(l,s,(merge_dp_cont c w))]
    | dp_end            => w
  end.

Fixpoint merge_dp_contn (d: Dp) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_dp_cont d (merge_dp_contn d w k)
  end.

CoFixpoint merge_dpf_cont (d: Dpf) (w: st): st :=
  match d with 
    | dpf_receive q l s c => st_receive q [(l,s,(merge_dpf_cont c w))]
    | dpf_send q l s c    => st_send q [(l,s,(merge_dpf_cont c w))]
    | dpf_end             => w
  end.

Fixpoint merge_dpf_contn (d: Dpf) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_dpf_cont d (merge_dpf_contn d w k)
  end.

Print Dp.

Fixpoint dp2dpf (d: Dp): Dpf :=
 match d with
   | dp_receive p l s   => dpf_receive p l s dpf_end
   | dp_send p l s      => dpf_send p l s dpf_end
   | dp_mergea p l s d' => dpf_receive p l s (dp2dpf d')
   | dp_merge p l s d'  => dpf_send p l s (dp2dpf d')
   | dp_end             => dpf_end
 end.

Fixpoint dpf2dp (d: Dpf): Dp :=
  match d with
    | dpf_receive p l s d' =>
      match d' with
        | dpf_end => dp_receive p l s
        | _       => dp_mergea p l s (dpf2dp d')
      end
    | dpf_send p l s d' =>
      match d' with
        | dpf_end => dp_send p l s
        | _       => dp_merge p l s (dpf2dp d')
      end
    | dpf_end           => dp_end
  end.

Fixpoint Dpf_merge (a: Dpf) (b: Dpf): Dpf :=
  match a with
    | dpf_receive q l s d' => dpf_receive q l s (Dpf_merge d' b)
    | dpf_send q l s d'    => dpf_send q l s (Dpf_merge d' b)
    | dpf_end              => b
  end.

Fixpoint DpnD3 (d: Dpf) (n: nat): Dpf :=
  match n with
    | O   => dpf_end
    | S O => d
    | S k => Dpf_merge d (DpnD3 d k)
  end.

Fixpoint dpList (d: Dp): list (Dp) :=
  match d with
    | dp_receive q l s  => [d]
    | dp_send q l s     => [d]
    | dp_mergea q l s c => dp_receive q l s :: (dpList c)
    | dp_merge q l s c  => dp_send q l s :: (dpList c)
    | dp_end            => nil
  end.

Fixpoint listDp (l: list Dp): Dp :=
  match l with
    | nil   => dp_end
    | x::xs => 
      match x with
        | dp_receive q l s => dp_mergea q l s (listDp xs)
        | dp_send q l s    => dp_merge q l s (listDp xs)
        | _                 => x
      end
  end.

Definition DpnA (d: Dp) (n: nat): Dp :=
  listDp (napp n (dpList d)).

