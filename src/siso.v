Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.types.local ST.src.reordering.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

Inductive singletonI (R: st -> Prop): st -> Prop :=
  | ends : singletonI R st_end
  | sends: forall p l s w, R w -> singletonI R (st_send p (cocons (l,s,w) conil))
  | recvs: forall p l s w, R w -> singletonI R (st_receive p (cocons (l,s,w) conil)).

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

(* direct st -> siso -- omits the middle men so and si decompositions *)

Inductive st2siso (R: st -> st -> Prop): st -> st -> Prop :=
  | st2siso_end: st2siso R st_end st_end
  | st2siso_rcv: forall l s x xs y p,
                 R x y ->
                 copathsel l s xs y ->
                 st2siso R (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2siso_snd: forall l s x xs y p,
                 R x y ->
                 copathsel l s xs y ->
                 st2siso R (st_send p (cocons (l,s,x) conil)) (st_send p xs).

Definition st2sisoC s1 s2 := paco2 (st2siso) bot2 s1 s2.

Lemma st2siso_mon: monotone2 st2siso.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2siso_end.
       - specialize (st2siso_rcv r'); intro HS.
         apply HS with (y := y).
         apply LE, H. easy.
       - specialize (st2siso_snd r'); intro HS.
         apply HS with (y := y).
         apply LE, H. easy.
Qed.

Local Open Scope string_scope.
Import CoListNotations.
(*
CoFixpoint exst := st_send "C" [| ("add", I, st_receive "A" [| ("add", I, exst); ("X",I,st_send "C" [| ("Y",I,exst); ("Z",I,exst) |]) |]); 
                                ("sub", I, st_receive "A" [| ("add", I, exst) |]);
                                ("mul", I, st_receive "A" [| ("add", I, exst) |]);
                                ("div", I, "A" & [| ("X", I, exst) |]); 
                                ("X", I, exst) |].

CoFixpoint exsiso := st_send "C" [("add", I, st_receive "A" [("X", I, (st_send "C" [("Y",I,exsiso)]))])].

Lemma example_ns: st2sisoC exsiso exst.
Proof. pcofix CIH. pfold.
       rewrite(st_eq exst). rewrite(st_eq exsiso). simpl.
       apply st2siso_snd. simpl. left. pfold.
       apply st2siso_rcv. simpl. left. pfold.
       apply st2siso_snd. simpl. 
       right. exact CIH.
Qed.

CoFixpoint exsiso2 := st_send "C" [("add", I, st_receive "A" [("X", I, (st_send "C" [("Y",I, st_send "C" [("sub", I, st_receive "A" [("add", I, exsiso2)])])]))])].

Lemma example_ns2: st2sisoC exsiso2 exst.
Proof. pcofix CIH. pfold.
       rewrite(st_eq exst). rewrite(st_eq exsiso2). simpl.
       apply st2siso_snd. simpl. left. pfold.
       apply st2siso_rcv. simpl. left. pfold.
       apply st2siso_snd. simpl. left. pfold.
       rewrite(st_eq exst). simpl.
       apply st2siso_snd. simpl. left. pfold.
       apply st2siso_rcv. simpl.
       right. exact CIH.
Qed. *)

(**)

Lemma exts: forall {p l s} w, singleton w -> singleton (st_send p (cocons (l,s,w) conil)).
Proof. intros p l s w H.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Defined.

Lemma extsR: forall {p l s} w, singleton (st_send p (cocons (l,s,w) conil)) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.

Lemma extr: forall {p l s} w, singleton w -> singleton (st_receive p (cocons (l,s,w) conil)).
Proof. intros.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Defined.

Lemma extrR: forall {p l s} w, singleton (st_receive p (cocons (l,s,w) conil)) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.


