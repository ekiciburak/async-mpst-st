From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.src.st ST.types.local.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

CoInductive so: Type :=
  | so_end    : so 
  | so_receive: participant -> (label -> option (sort*so)) -> so 
  | so_send   : participant -> (label*sort*so)             -> so.

Definition so_id (s: so): so :=
  match s with
    | so_end            => so_end
    | so_receive p l    => so_receive p l
    | so_send p (l,s,t) => so_send p (l,s,t)
  end.

Lemma so_eq: forall (s: so), s = so_id s.
Proof. intro s; destruct s; simpl; try easy. destruct p as ((l,srt),t). easy. Defined.

(* Inductive st2so (R: so -> st -> Prop): so -> st -> Prop :=
  | st2so_end: st2so R so_end st_end
  | st2so_snd: forall l s x xs p,
               R x (pathsel l s xs) ->
               st2so R (so_send p (l,s,x)) (st_send p xs)
  | st2so_rcv: forall p l s xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip ys xs) ->
               st2so R (so_receive p (zip (zip l s) ys)) (st_receive p (zip (zip l s) xs)).

Definition st2soC s1 s2 := paco2 (st2so) bot2 s1 s2. *)

(* Inductive st2so (R: st -> st -> Prop): st -> st -> Prop :=
  | st2so_end: st2so R st_end st_end
  | st2so_snd: forall l s x s' y f p,
               f l = Some(s',y) ->
               s = s' ->
               R x y ->
               st2so R (st_send p (sfun l s x)) (st_send p f)
  | st2so_rcv: forall p f g,
               (forall l, 
                match (f l, g l) with
                 | (Some (s1, t1), Some (s2, t2)) => s1 = s2 /\ R t1 t2
                 | (None, None)                   => True
                 | _                              => False
                end
               ) ->
               st2so R (st_receive p f) (st_receive p g). *)

(* Inductive st2so (R: st -> st -> Prop): st -> st -> Prop :=
  | st2so_end: st2so R st_end st_end
  | st2so_snd: forall l s x xs y p,
               R x y ->
               copathsel l s xs y ->
               st2so R (st_send p (cocons (l,s,x) conil)) (st_send p xs)
  | st2so_rcv: forall p l s xs ys,
               colen_eqC xs ys ->
               Forall2C (fun u v => R u v) ys xs ->
               st2so R (st_receive p (cozip (cozip l s) ys)) (st_receive p (cozip (cozip l s) xs)).
 *)

Inductive st2so (R: st -> st -> Prop): st -> st -> Prop :=
  | st2so_end: st2so R st_end st_end
  | st2so_snd: forall l s x xs y p,
               R x y ->
               copathsel l s xs y ->
               st2so R (st_send p (cocons (l,s,x) conil)) (st_send p xs)
  | st2so_rcv: forall p xs ys,
(*             colen_eqC xs ys -> *)
               Forall2C (fun u v => exists l s t l' s' t', u = (l,s,t) /\ v = (l',s',t') /\ R t t') ys xs ->
               st2so R (st_receive p ys) (st_receive p xs).

Definition st2soC s1 s2 := paco2 (st2so) bot2 s1 s2.

Lemma monH: forall ys xs r r',
  Forall2C (fun u : st => [eta r u]) ys xs ->
  (forall x0 x1 : st, r x0 x1 -> r' x0 x1) ->
  Forall2C (fun u : st => [eta r' u]) ys xs.
Proof. intros. revert xs ys H. pcofix CIH.
       intros.
       pfold.
       pinversion H1. subst.
       constructor. subst.
       constructor. apply H0; easy. 
       right.
       apply CIH.
       easy. 
       unfold monotone2.
       intros.
       induction IN; intros.
       constructor.
       constructor. easy. apply LE. easy.
Qed.

Lemma st2so_mon: monotone2 st2so.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2so_end.
       - specialize (st2so_snd r'); intro HS.
         apply HS with (l := l) (s := s) (x := x) (y := y).
         apply LE; easy. easy.
       - specialize (st2so_rcv r'); intro HS.
         apply HS. (* easy. *)
         apply monH2 with (r := r); easy.
Qed.

(*example so decomposition*)
CoFixpoint Et1 := st_receive "q" (cocons ("l7", sint, Et1) conil).
CoFixpoint Et2 := st_send "q" (cocons ("l8", sint, Et2) conil).

CoFixpoint Et1so := st_receive "q" (cocons ("l7", sint, Et1so) conil).
CoFixpoint Et2so := st_send "q" (cocons ("l8", sint, Et2so) conil).

Check (cocons("l4",sint,st_end) 
                                                    (cocons ("l5",sint,st_end) 
                                                    (cocons("l6",sint,st_end) 
                                                    conil))).

CoFixpoint eT1 := st_receive "p" (cocons ("l1",sint,st_send "p" (cocons("l4",sint,Et1) 
                                                                (cocons ("l5",sint,Et2) 
                                                                (cocons("l6",sint,eT1) 
                                                                conil)))) 
                                 (cocons ("l2",sint,st_send "q" (cocons ("l9",sint,eT1) conil))
                                 (cocons ("l3",sint,st_receive "q" (cocons ("l10",sint,eT1) conil)) conil))).

CoFixpoint eT2 := st_receive "p" (cocons ("l1",sint,st_send "p" (cocons("l4",sint,Et1so) conil)) 
                                 (cocons ("l2",sint,st_send "q" (cocons ("l9",sint,eT2) conil))
                                 (cocons ("l3",sint,st_receive "q" (cocons ("l10",sint,eT2) conil)) conil))).

Lemma T1soT2: st2soC eT2 eT1.
Proof. pcofix CIH.
       rewrite(st_eq eT1); rewrite(st_eq eT2); simpl.
       pfold.
       apply st2so_rcv.
       pfold. constructor.
(*        left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       pfold.
       constructor. *)
       exists "l1". exists (I). exists ("p" ! cocons ("l4", I, Et1so) conil).
       exists "l1". exists (I). exists ("p" ! cocons ("l4", I, Et1) (cocons ("l5", I, Et2) (cocons ("l6", I, eT1) conil))).
       split. easy. split. easy.
       left.
       pfold.
       apply st2so_snd with (y := Et1).
       left.
       pcofix CIH2.
       rewrite(st_eq Et1). simpl. rewrite(st_eq Et1so). simpl.
       pfold. apply st2so_rcv.
       pfold. constructor.
(*        left. pfold. constructor.
       pfold. constructor. *)
       exists "l7". exists (I). exists (Et1so).
       exists "l7". exists (I). exists (Et1).
       split. easy. split. easy. right. easy.
       left. pfold. constructor.
       constructor.

       left.
       pfold.
       constructor.
       exists "l2". exists (I). exists ("q" ! cocons ("l9", I, eT2) conil).
       exists "l2". exists (I). exists ("q" ! cocons ("l9", I, eT1) conil).
       split. easy. split. easy.
       left. pfold. apply st2so_snd with (y := eT1).
       right. easy.
       constructor.
       
       left.
       pfold.
       constructor.
       exists "l3". exists (I). exists ("q" & cocons ("l10", I, eT2) conil).
       exists "l3". exists (I). exists ("q" & cocons ("l10", I, eT1) conil).
       split. easy. split. easy.
       left. pfold. apply st2so_rcv.
       pfold. constructor.
(*        left. pfold. constructor.
       pfold. constructor. *)
       exists "l10". exists (I). exists (eT2).
       exists "l10". exists (I). exists (eT1).
       split. easy. split. easy. right. easy.
       
       left. pfold. constructor.
       left. pfold. constructor.
Qed.








