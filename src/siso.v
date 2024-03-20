Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

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

(* direct st -> siso -- omits the middle men so and si decompositions *)

Fixpoint pathsel (u: label) (l: list (label*st.sort*st)): st :=
  match l with
    | (lbl,s,x)::xs => if eqb u lbl then x else pathsel u xs
    | nil           => st_end
  end.

Inductive st2siso (R: st -> st -> Prop): st -> st -> Prop :=
  | st2siso_end: st2siso R st_end st_end
  | st2siso_rcv: forall l s x xs p,
                  R x (pathsel l xs) ->
                  st2siso R (st_receive p [(l,s,x)]) (st_receive p xs) 
  | st2siso_snd: forall l s x xs p,
                  R x (pathsel l xs) ->
                  st2siso R (st_send p [(l,s,x)]) (st_send p xs) .

Definition st2sisoC s1 s2 := paco2 (st2siso) bot2 s1 s2.

Lemma st2siso_mon: monotone2 st2siso.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2siso_end.
       - specialize (st2siso_rcv r'); intro HS.
         apply HS.
         apply LE, H.
       - specialize (st2siso_snd r'); intro HS.
         apply HS.
         apply LE, H.
Qed.

Local Open Scope string_scope.

CoFixpoint exst := st_send "C" [("add", I, st_receive "A" [("add", I, exst); ("X",I,st_send "C" [("Y",I,exst);("Z",I,exst)])]); 
                                ("sub", I, st_receive "A" [("add", I, exst)]);
                                ("mul", I, st_receive "A" [("add", I, exst)]);
                                ("div", I, "A" & [("X", I, exst)]); 
                                ("X", I, exst)].

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
Qed.

(**)

Lemma exts: forall {p l s} w, singleton w -> singleton (st_send p [(l,s,w)]).
Proof. intros p l s w H.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Defined.

Lemma extsR: forall {p l s} w, singleton (st_send p [(l,s,w)]) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.

Lemma extr: forall {p l s} w, singleton w -> singleton (st_receive p [(l,s,w)]).
Proof. intros.
       pfold. constructor. left.
       punfold H.
       apply sI_mon.
Defined.

Lemma extrR: forall {p l s} w, singleton (st_receive p [(l,s,w)]) -> singleton w .
Proof. intros.
       punfold H.
       inversion H.
       subst.
       unfold upaco1 in H1. destruct H1; easy.
       apply sI_mon.
Qed.