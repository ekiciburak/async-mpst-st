From ST Require Import stream st so si.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

(* CoInductive so: Type :=
  | so_end    : so 
  | so_receive: participant -> list (label*sort*so) -> so 
  | so_send   : participant -> so -> so.

CoInductive si: Type :=
  | si_end    : si
  | si_receive: participant -> si -> si 
  | si_send   : participant -> list (label*sort*si) -> si.
  
 *)

CoInductive siso: Type :=
  | siso_end    : siso 
  | siso_receive: participant -> (label*st.sort*siso) -> siso 
  | siso_send   : participant -> (label*st.sort*siso) -> siso.

Inductive so2siso (R: so -> siso -> Prop): so -> siso -> Prop :=
  | so2siso_end: so2siso R so_end siso_end
  | so2siso_rcv: forall l s x t xs p,
                 List.In (l,s,x) xs ->
                 R (so_receive p [(l,s,x)]) t ->
                 so2siso R (so_receive p xs) t
  | so2siso_snd: forall x t p,
                 R t (siso_send p x) ->
                 so2siso R t (siso_send p x).

Inductive si2siso (R: si -> siso -> Prop): si -> siso -> Prop :=
  | si2siso_end: si2siso R si_end siso_end
  | si2siso_rcv: forall x t p,
                 R t (siso_receive p x) ->
                 si2siso R t (siso_receive p x)
  | si2siso_snd: forall l s x t xs p,
                 List.In (l,s,x) xs ->
                 R (si_send p [(l,s,x)]) t ->
                 si2siso R (si_send p xs) t.

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
Definition so2sisoC s1 s2 := paco2 (so2siso) bot2 s1 s2.
Definition si2sisoC s1 s2 := paco2 (si2siso) bot2 s1 s2.

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

Definition siso_idA (t: siso): siso :=
  match t with
    | siso_receive p a => siso_receive p a
    | siso_send p a    => siso_send p a
    | siso_end         => siso_end
  end.

Lemma siso_eqA: forall t, t = siso_idA t.
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

CoFixpoint actC (t: siso): coseq (participant * string) :=
  match t with
    | siso_receive p (l,s,w') => Delay (cocons (p, "?"%string) (actC w'))
    | siso_send p (l,s,w')    => Delay (cocons (p, "!"%string) (actC w'))
    | _                       => Delay conil
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

CoFixpoint merge_ap_contB (p: participant) (a: Ap p) (w: siso): siso :=
  match a with
    | ap_receive q H l s  => siso_receive q (l,s,w)
    | ap_merge q H l s w' => siso_receive q (l,s,(merge_ap_contB p w' w))
    | ap_end              => w
  end.

Fixpoint merge_ap_contn (p: participant) (a: Ap p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ap_cont p a (merge_ap_contn p a w k)
  end.

Fixpoint merge_ap_contnB (p: participant) (a: Ap p) (w: siso) (n: nat): siso :=
  match n with
    | O    => w
    | S k  => merge_ap_contB p a (merge_ap_contnB p a w k)
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

CoFixpoint merge_bp_contB (p: participant) (b: Bp p) (w: siso): siso :=
  match b with 
    | bp_receivea q l s  => siso_receive q (l,s,w)
    | bp_send q x l s    => siso_send q (l,s,w)
    | bp_mergea q l s c  => siso_receive q (l,s,(merge_bp_contB p c w))
    | bp_merge q x l s c => siso_send q (l,s,(merge_bp_contB p c w))
    | bp_end             => w
  end.

Fixpoint merge_bp_contn (p: participant) (b: Bp p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_bp_cont p b (merge_bp_contn p b w k)
  end.

Fixpoint merge_bp_contnB (p: participant) (b: Bp p) (w: siso) (n: nat): siso :=
  match n with
    | O    => w
    | S k  => merge_bp_contB p b (merge_bp_contnB p b w k)
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

Lemma hm1: forall p b w, act (merge_bp_cont p b w) = appendL (actB p b) (act w).
Proof. intros p b.
       induction b; intros.
       rewrite(coseq_eq(act (merge_bp_cont p (bp_receivea s s0 s1) w))).
       rewrite(coseq_eq( appendL (actB p (bp_receivea s s0 s1)) (act w))).
       unfold coseq_id.
       simpl. rewrite anl2. easy.

       rewrite(coseq_eq(act (merge_bp_cont p (bp_send q n s s0) w))).
       unfold coseq_id. simpl.
       rewrite(coseq_eq(appendL [(q, "!"%string)] (act w))).
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

Definition merge_bp_contnA (p: participant) (b: Bp p) (w: st) (n: nat): st :=
merge_bp_cont p (Bpn p b n) w.

Inductive cosetIncL (R: coseq (participant * string) -> list (participant * string) -> Prop):
                        coseq (participant * string) -> list (participant * string) -> Prop :=
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

Inductive cosetIncR: list (participant * string) -> coseq (participant * string) -> Prop :=
  | l_nil : forall ys, cosetIncR nil ys
  | l_incl: forall x xs ys,
            CoInR x ys ->
            cosetIncR xs ys ->
            cosetIncR (x::xs) ys.

Definition act_eq (w w': st) := forall a, CoIn a (act w) <-> CoIn a (act w').

Definition act_eqB (w w': siso) := forall a, CoIn a (actC w) <-> CoIn a (actC w').

Inductive refinementR (seq: st -> st -> Prop): st -> st -> Prop :=
  | _sref_in : forall w w' p l s s',
                      subsort s' s -> 
                      seq w w' ->
                      refinementR seq (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])

  | _sref_out: forall w w' p l s s',
                      subsort s s' ->
                      seq w w' ->
                      refinementR seq (st_send p [(l,s,w)]) (st_send p [(l,s',w')])

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
       - constructor. exact H. apply LE. exact H0.
       - constructor. exact H. apply LE. exact H0.
       - specialize(_sref_a r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - specialize(_sref_b r'); intro Ha. apply Ha; try easy.
         apply LE. exact H0.
       - constructor.
Qed.

(* rewriting issues *)
#[export]
Declare Instance Equivalence_ref_eqi: Equivalence refinement.

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

Inductive refinementRA (seq: siso -> siso -> Prop): siso -> siso -> Prop :=
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

Notation "x '~<A' y" := (refinementRAC x y) (at level 50, left associativity).




