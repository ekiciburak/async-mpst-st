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

CoFixpoint fromAp (p: participant) (a: Ap p): st :=
  match a with
    | ap_receive q x l s => st_receive q [(l,s,st_end)]
    | ap_merge q x l s c => st_receive q [(l,s,(fromAp p c))]
    | ap_end             => st_end
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
    | ap_end              => st_end
  end.

Fixpoint merge_ap_contn (p: participant) (a: Ap p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ap_cont p a (merge_ap_contn p a w k)
  end.

Fixpoint merge_ap_contnA (p: participant) (a: Ap p) (w: st) (n: nat): st :=
  match n with
    | O    => w
    | S k  => merge_ap_cont p a (merge_ap_contnA p a w k)
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

(* Parameters (q p: participant) (H: p = q) (b: Bp p).
Check eq_rect p Bp b q H. *)

From Equations Require Import Equations.

(* Equations Bpn (p: participant) (b: Bp p) (n: nat): Bp p :=
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

(* Fixpoint Bpn (p: participant) (b: Bp p) (n: nat): Bp p :=
  match n with
    | O   => bp_end
    | S k =>
      match b with (* as bx in (Bp _) return
         forall q (en : p = q) (ea : eq_rect p Bp b q en = bx), _ with  *)
        | bp_receivea q l s  => bp_mergea q l s (Bpn p b k)
        | bp_send q H l s    => bp_merge q H l s (Bpn p b k)
        | bp_mergea q l s c  => bp_mergea q l s (bp_mergea q l s (Bpn p b k))
        | bp_merge q H l s c => bp_merge q H l s (bp_merge q H l s (Bpn p b k))
        | bp_end             => bp_end
      end 
  end.
 *)

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

Fixpoint actB (p: participant) (b: Bp p): list (participant * string) :=
  match b with
    | bp_receivea q l s  => cons (q, "?"%string) nil
    | bp_send q x l s    => cons (q, "!"%string) nil
    | bp_mergea q l s c  => cons (q, "?"%string) (actB p c)
    | bp_merge q x l s c => cons (q, "!"%string) (actB p c)
    | _                  => nil
  end.

(* Fixpoint actBn (p: participant) (b: Bp p) (n: nat): coseq (participant * string) :=
  match n with
    | O   => Delay conil
    | S k => appendC (actB p b) (actBn p b k) 
  end.
 *)

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

Lemma mcomm: forall n p b w,
             merge_bp_contn p b (merge_bp_cont p b w) n =
             merge_bp_cont p b (merge_bp_contn p b w n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
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

Lemma hm2: forall n p, actBn p bp_end n = [].
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

(* Definition cosetIncRC := fun s1 s2 => paco2 cosetIncR bot2 s1 s2. *)

Definition act_eq (w w': st) := forall a, CoIn a (act w) <-> CoIn a (act w').

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
                      (exists L,
                         cosetIncLC (act w) L /\
                         cosetIncLC (act (merge_ap_contn p a w' n)) L /\
                         cosetIncR L (act w) /\
                         cosetIncR L (act (merge_ap_contn p a w' n))
                      ) ->
                      refinementR seq (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)

  | _sref_b  :  forall w w' p l s s' b n,
                      subsort s s' ->
                      seq w (merge_bp_contn p b w' n) ->
                      (exists L, 
                         cosetIncLC (act w) L /\
                         cosetIncLC (act (merge_bp_contn p b w' n)) L /\
                         cosetIncR L (act w) /\
                         cosetIncR L (act (merge_bp_contn p b w' n))
                      ) ->
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
