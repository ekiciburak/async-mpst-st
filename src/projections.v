Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering 
ST.src.reorderingfacts ST.src.acteqfacts ST.src.siso ST.src.inversion ST.types.local ST.subtyping.refinement ST.types.typenv.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Morphisms JMeq.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.
Require Import ProofIrrelevance.

Inductive projS (R: st -> participant -> st -> Prop): st -> participant -> st -> Prop :=
  | pjs_end : forall p, projS R st_end p st_end
  | pjs_snde: forall p l s w' w, R w' p w -> projS R (st_send p [|(l,s,w')|]) p (st_send p [|(l,s,w)|])
  | pjs_sndI: forall q l s w' p w, p <> q -> coseqIn (p, snd) (act w') -> R w' p w -> projS R (st_send q [|(l,s,w')|]) p w
  | pjs_sndN: forall q l s w' p, p <> q -> (coseqIn (p, snd) (act w') -> False) -> projS R (st_send q [|(l,s,w')|]) p st_end
  | pjs_rcvI: forall q l s w' p w, coseqIn (p, snd) (act w') -> R w' p w -> projS R (st_receive q [|(l,s,w')|]) p w
  | pjs_rcvN: forall q l s w' p, (coseqIn (p, snd) (act w') -> False) -> projS R (st_receive q [|(l,s,w')|]) p st_end.

Definition projSC w1 p w2 := paco3 projS bot3 w1 p w2.

Inductive projR (R: st -> participant -> st -> Prop): st -> participant -> st -> Prop :=
  | pjr_end : forall p, projR R st_end p st_end
  | pjr_rcve: forall p l s w' w, R w' p w -> projR R (st_receive p [|(l,s,w')|]) p (st_receive p [|(l,s,w)|])
  | pjr_rcvI: forall q l s w' p w, p <> q -> coseqIn (p, snd) (act w') -> R w' p w -> projR R (st_receive q [|(l,s,w')|]) p w
  | pjr_rcvN: forall q l s w' p, p <> q -> (coseqIn (p, snd) (act w') -> False) -> projR R (st_receive q [|(l,s,w')|]) p st_end
  | pjr_sndI: forall q l s w' p w, coseqIn (p, snd) (act w') -> R w' p w -> projR R (st_send q [|(l,s,w')|]) p w
  | pjr_sndN: forall q l s w' p, (coseqIn (p, snd) (act w') -> False) -> projR R (st_send q [|(l,s,w')|]) p st_end.

Definition projRC w1 p w2 := paco3 projR bot3 w1 p w2.

Inductive sRefinementR (R: st -> st -> Prop): st -> st -> Prop :=
  | sref_a  : forall w w' p l s s', subsort s' s ->
                                    R w w' ->
                                    sRefinementR R (st_receive p [|(l,s,w)|]) (st_receive p [|(l,s',w')|])
  | sref_b  : forall w w' p l s s', subsort s s' ->
                                    R w w' ->
                                    sRefinementR R (st_send p [|(l,s,w)|]) (st_send p [|(l,s',w')|])
  | sref_end: sRefinementR R st_end st_end.

Definition sRefinement w1 w2 := paco2 sRefinementR bot2 w1 w2.

Lemma _B_7: forall w w' p w1 w2, refinement4 (@und w) (@und w') -> projSC (@und w) p (@und w1) -> projSC (@und w') p (@und w2) -> sRefinement (@und w1) (@und w2).
Proof. destruct w as (w, Pw).
       destruct w' as (w', Pw').
       destruct w1 as (w1, Pw1).
       destruct w2 as (w2, Pw2).
       generalize dependent w.
       generalize dependent w'.
       generalize dependent w1.
       generalize dependent w2.
       revert p.
       pcofix CIH. simpl.
       intros.
       specialize(sinv w1 Pw1); intros Hpw1.
       destruct Hpw1 as [Hpw1 | [Hpw1 | Hpw1]].
       - destruct Hpw1 as (q1, (l1, (s1, (wa, (Heq1, Hs1))))).
         specialize(sinv w2 Pw2); intros Hpw2.
         destruct Hpw2 as [Hpw2 | [Hpw2 | Hpw2]].
         + destruct Hpw2 as (q2, (l2, (s2, (wb, (Heq2, Hs2))))).
           subst.
Admitted.


