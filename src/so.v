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

Inductive st2so (R: st -> st -> Prop): st -> st -> Prop :=
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
               st2so R (st_receive p f) (st_receive p g).

Definition st2soC s1 s2 := paco2 (st2so) bot2 s1 s2.

Lemma st2so_mon: monotone2 st2so.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2so_end.
       - specialize (st2so_snd r'); intro HS.
         apply HS with (l := l) (s := s) (x := x) (s' := s') (y := y).
         easy. easy. apply LE; easy.
       - specialize (st2so_rcv r'); intro HS.
         apply HS. intro l.
         specialize(H l).
         destruct (f l).
         destruct (g l).
         destruct p0, p1. split. easy.
         apply LE. easy. easy.
         easy.
Qed.

(*example so decomposition*)
CoFixpoint Et1 := st_receive "q" (sfun "l7" sint Et1).
CoFixpoint Et2 := st_send "q" (sfun "l8" sint Et2).

CoFixpoint Et1so := st_receive "q" (sfun "l7" sint Et1so).
CoFixpoint Et2so := st_send "q" (sfun "l8" sint Et2so).


CoFixpoint eT1 := st_receive "p" (fun l => if eqb l "l1" then Some(sint, (st_send "p" (fun l => if eqb l "l4" then Some(sint,Et1)
                                                                                                else if eqb l "l5" then Some(sint,Et2)
                                                                                                else if eqb l "l6" then Some(sint,eT1)
                                                                                                else None)))
                                           else if eqb l "l2" then Some(sint, st_send "q" (sfun "l9" sint eT1))
                                           else if eqb l "l3" then Some(sint, st_receive "q" (sfun "l10" sint eT1))
                                           else None
                                 ).


CoFixpoint eT2 := st_receive "p" (fun l => if eqb l "l1" then Some(sint, st_send "p" (sfun "l4" sint Et1so))
                                           else if eqb l "l2" then Some(sint, st_send "q" (sfun "l9" sint eT2))
                                           else if eqb l "l3" then Some(sint, st_receive "q" (sfun "l10" sint eT2))
                                           else None
                                 ).

Lemma T1soT2: st2soC eT2 eT1.
Proof. pcofix CIH.
       rewrite(st_eq eT1); rewrite(st_eq eT2); simpl.
       pfold.
       apply st2so_rcv. intro l.
       case_eq(eqb l "l1"); intros.
       + split. easy.
         left. pfold.
         apply st2so_snd with (s' := I) (y := Et1). easy. easy.
         left.
         pcofix CIH2.
         pfold. rewrite(st_eq Et1). simpl. rewrite(st_eq Et1so). simpl.
         apply st2so_rcv. intro l'.
         unfold sfun.
         case_eq(eqb "l7" l'); intros.
         ++ split. easy. right. easy. easy.
       + case_eq(eqb l "l2"); intros.
         ++ split. easy. left.
            pfold. apply st2so_snd with (s' := I) (y := eT1). unfold sfun. rewrite String.eqb_refl. easy. easy.
            right. easy. 
         ++ case_eq(eqb l "l3"); intros.
            * split. easy. left.
              pfold. apply st2so_rcv.
              intro l'. unfold sfun.
              case_eq(eqb "l10" l'); intros.
              ** split. easy. right. easy.
              ** easy.
            * easy.
Qed.








