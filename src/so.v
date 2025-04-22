From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.src.st ST.types.local.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import ST.processes.axioms.

CoFixpoint st2soH (t: st): st :=
  match t with
    | st_send p xs    =>
      match xs with
        | cocons (l,s,t') ys => st_send p (cocons (l,s,st2soH t') conil) 
        | conil              => st_send p conil
      end
    | st_receive p xs => 
       let cofix next xs :=
        match xs with
          | cocons (l,s,t') ys => cocons (l,s,st2soH t') (next ys)
          | conil              => conil
        end 
      in st_receive p (next xs) 
    | _               => st_end
  end.

CoFixpoint st2soF (t: st): coseq st :=
  match t with
    | st_send p xs => 
      match xs with
        | cocons(l,s,t') ys => cocons (st_send p (cocons (l,s,st2soH t') conil)) (st2soF (st_send p ys))
        | conil             => conil
      end
    | _            => (cocons (st2soH t) conil)
  end.

Inductive st2so (R: st -> st -> Prop): st -> st -> Prop :=
  | st2so_end: st2so R st_end st_end
  | st2so_snd: forall l s x xs y p,
               R x y ->
               copathsel l s xs y ->
               st2so R (st_send p (cocons (l,s,x) conil)) (st_send p xs)
  | st2so_rcv: forall p xs ys,
               Forall2Co (fun u v => exists l s t t', u = (l,s,t) /\ v = (l,s,t') /\ R t t') ys xs ->
               st2so R (st_receive p ys) (st_receive p xs).

Definition st2soC s1 s2 := paco2 (st2so) bot2 s1 s2.

Lemma st2so_mon: monotone2 st2so.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2so_end.
       - specialize (st2so_snd r'); intro HS.
         apply HS with (l := l) (s := s) (x := x) (y := y).
         apply LE; easy. easy.
       - specialize (st2so_rcv r'); intro HS.
         apply HS.
         apply monHo2 with (r := r); easy.
Qed.

CoFixpoint next (xs: coseq(label*sort*st)) :=
  match xs with
    | cocons (l,s,t') ys => cocons (l,s,st2soH t') (next ys)
    | conil              => conil
  end.

Lemma next_eq: forall xs, next xs = comap (prod_map (prod_map id id) (st2soH)) xs.
Proof. intros.
       apply cext.
       revert xs.
       pcofix CIH.
       intros.
       pfold.
       destruct xs.
       - rewrite(coseq_eq(comap (prod_map (prod_map id id) st2soH) [||])). simpl.
         rewrite(coseq_eq( (next [||]))). simpl. constructor.
       - rewrite(coseq_eq(next (cocons p xs))).
         rewrite(coseq_eq(comap (prod_map (prod_map id id) st2soH) (cocons p xs))). simpl.
         destruct p as ((l1,s1),t1).
         constructor.
         right. apply CIH.
         simpl. easy.
Qed.

Lemma st2soE: forall T, wfC T -> st2soC (st2soH T) T.
Proof. pcofix CIH.
       intros T Hwf.
       case_eq T; intros.
       - pfold. rewrite(st_eq (st2soH (end))). simpl. constructor.
       - rewrite(st_eq( (st2soH (s & c)))). simpl.
         fold next.
         rewrite next_eq.
         rewrite(coseq_eq(comap (prod_map (prod_map id id) st2soH) c)). simpl.
         destruct c. pfold. constructor. pfold. constructor.
         destruct p as ((l1,s1),t1). simpl.
         pfold. constructor. pfold.
         constructor.
         exists l1. exists s1. exists (st2soH t1). exists t1.
         split. easy. split. easy. right. apply CIH.
         subst.
         pinversion Hwf. subst.
         pinversion H2. subst.
         pfold. destruct H3 as (l2,(s2,(t2,(Ha,Hb)))).
         inversion Ha. subst.
         destruct Hb. pinversion H.
         apply mon_wfH. easy.
         apply mon_fHo.
         apply mon_wfH.
         left. subst.
         revert c Hwf.
         pcofix CIH2. intros.
         case_eq c; intros.
         rewrite(coseq_eq (comap (prod_map (prod_map id id) st2soH) [||])). simpl.
         simpl. pfold. constructor.
         pfold. 
         rewrite(coseq_eq(comap (prod_map (prod_map id id) st2soH) (cocons p c0))). simpl.
         constructor.
         destruct p as ((l2,s2),t2). simpl.
         exists l2. exists s2. exists (st2soH t2). exists t2.
         split. easy. split. easy. right. apply CIH.
         subst. pinversion Hwf. subst.
         pinversion H2. subst.
         pfold.
         destruct H3 as (l3,(s3,(t3,(Hc,Hd)))).
         pinversion H4. subst.
         destruct H3 as (l4,(s4,(t4,(He,Hf)))).
         inversion He. subst.
         destruct Hf. pinversion H.
         apply mon_wfH. easy.
         apply mon_fHo. apply mon_fHo.
         apply mon_wfH.
         right. apply CIH2.
         subst.
         pinversion Hwf. subst.
         pinversion H2. subst.
         pfold.
         constructor. easy. pfold.
         constructor.
         destruct H3 as (l2,(s2,(t2,(Ha,Hb)))).
         inversion Ha. subst.
         exists l2. exists s2. exists t2.
         split. easy. easy.
         pinversion H4.
         subst.
         left. easy.
         apply mon_fHo.
         apply mon_fHo.
         apply mon_wfH.
       - rewrite(st_eq( (st2soH (s ! c)))). simpl.
         destruct c. pfold.
         subst. pinversion Hwf. easy.
         apply mon_wfH.
         subst. 
         destruct p. destruct p.
         pfold. apply st2so_snd with (y := s0). right. apply CIH.
         pinversion Hwf. subst. pinversion H2. subst.
         destruct H3 as (l3,(s3,(t3,(Ha,Hb)))).
         inversion Ha. subst.
         pfold.
         destruct Hb. pinversion H. apply mon_wfH. easy.
         apply mon_fHo.
         apply mon_wfH.
         constructor.
Qed.

(*example so decomposition*)
CoFixpoint Et1 := st_receive "q" (cocons ("l7", sint, Et1) conil).
CoFixpoint Et2 := st_send "q" (cocons ("l8", sint, Et2) conil).

CoFixpoint Et1so := st_receive "q" (cocons ("l7", sint, Et1so) conil).
CoFixpoint Et2so := st_send "q" (cocons ("l8", sint, Et2so) conil).

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
       apply st2so_rcv. pfold.
       constructor.

       exists "l1". exists (I). exists ("p" ! cocons ("l4", I, Et1so) conil).
       exists ("p" ! cocons ("l4", I, Et1) (cocons ("l5", I, Et2) (cocons ("l6", I, eT1) conil))).
       split. easy. split. easy.
       left.
       pfold.
       apply st2so_snd with (y := Et1).
       left.
       pcofix CIH2.
       rewrite(st_eq Et1). simpl. rewrite(st_eq Et1so). simpl.
       pfold. apply st2so_rcv. pfold.
       constructor.
       exists "l7". exists (I). exists (Et1so). exists (Et1).
       split. easy. split. easy. right. easy.
       constructor. pfold.
       constructor. 

       constructor. left. pfold. constructor.
       exists "l2". exists (I). exists ("q" ! cocons ("l9", I, eT2) conil). exists ("q" ! cocons ("l9", I, eT1) conil).
       split. easy. split. easy.
       left. pfold. apply st2so_snd with (y := eT1).
       right. easy.
       constructor.

       constructor. pfold. constructor.
       exists "l3". exists (I). exists ("q" & cocons ("l10", I, eT2) conil). exists ("q" & cocons ("l10", I, eT1) conil).
       split. easy. split. easy.
       left. pfold. apply st2so_rcv. pfold.
       constructor. 

       exists "l10". exists (I). exists (eT2). exists (eT1).
       split. easy. split. easy. right. easy.

       constructor. pfold.
       constructor.
       left. pfold. constructor.
Qed.


