Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering 
               ST.src.siso ST.types.local ST.subtyping.refinement ST.src.reorderingfacts.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type Coq.Logic.ClassicalFacts Coq.Logic.Classical_Prop.
Require Import ProofIrrelevance.

Fixpoint listSisoPRef (l: list (siso*siso)): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => (exists d1, exists d2, (forall n, refinement (merge_dpf_contn d1 (@und W) n) (merge_dpf_contn d2 (@und W') n))) /\ listSisoPRef xs
  end.

Fixpoint decomposeL (l: list (siso*siso)) (s: st) (s': st): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => st2sisoC (@und W) s /\ st2sisoC (@und W') s' /\ decomposeL xs s s'
  end.

Definition subtype (T T': st): Prop := exists (l: list (siso*siso)), decomposeL l T T' /\ listSisoPRef l.

Fixpoint listSisoPRef2 (l: list (siso*siso)): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => (exists d1, exists d2, (forall n, (merge_dpf_contn d1 (@und W) n) ~<  (merge_dpf_contn d2 (@und W') n))) /\ listSisoPRef2 xs
  end.

Definition subtype2 (T T': st): Prop := exists (l: list (siso*siso)), decomposeL l T T' /\ listSisoPRef2 l.

(* Fixpoint listSisoPRef3A (l: list (siso*siso)): Prop :=
  match l with
    | nil            => True
    | cons (W,W') xs => (exists b1, exists b2, (forall n, refinement3 (merge_bpf_contn b1 (@und W) n)  (merge_bpf_contn b2 (@und W') n))) /\ listSisoPRef3A xs
  end.

Definition subtype3A (T T': st): Prop := exists (l: list (siso*siso)), decomposeL l T T' /\ listSisoPRef3A l. *)

Definition subltype (T T': local) := subtype (lt2st T) (lt2st T').

(* Definition subltype2 (T T': local) (T1 T2: st) (P: lt2stC T T1) (Q: lt2stC T' T2) := subtype2 T1 T2. *)

Lemma pahselExt: forall ys xs l s y,
  copathsel l s ys y ->
  (Forall2Co (fun u v : string * local.sort * st =>exists (l : string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2so bot2 t t') ys xs) ->
  exists u, copathsel l s xs u /\ st2soC y u.
Proof. intros.
       revert xs H0.
       induction H; intros.
       - pinversion H0. subst.
         destruct H2 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         exists t2. split. constructor. destruct H8c; easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H4 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         constructor. easy. easy. easy.
         apply mon_f2Ho.
       - pinversion H1.
         subst.
         destruct H4 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8a. subst.
         apply IHcopathsel in H6.
         destruct H6 as (u,(H6a,H6b)).
         exists u. split.
         apply pselneqs. easy. easy. easy.
         apply mon_f2Ho.
Qed.

Lemma so_siDec: forall x y z, st2soC x y -> st2siC z x -> st2sisoC z y.
Proof. pcofix CIH.
       intros.
       pinversion H0.
       - subst. pinversion H1.
         subst. pfold. constructor.
         apply st2si_mon.
       - subst. pinversion H1.
         subst.
         pinversion H5. subst.
         destruct H7 as (l1,(s1,(t1,(t2,(H8a,(H8b,H8c)))))).
         inversion H8b. subst.
         pinversion H8. subst.
         pfold. apply st2siso_snd with (y := y0).
         right. apply CIH with (x := t2). easy. easy. easy.
         apply mon_f2Ho.
         apply mon_f2Ho.
         apply st2si_mon.
       - subst.
         pinversion H1.
         subst.
         assert (exists u, copathsel l s xs u /\ st2soC y u).
         { apply pahselExt with (xs := xs) in H6. easy. easy. }
         destruct H2 as (u,(H3a,H3b)).
         pfold.
         apply st2siso_rcv with (y := u).
         right. apply CIH with (x := y).
         easy. easy.
         easy.
         apply st2si_mon.
         apply st2so_mon.
Qed.

Lemma so_sisoDec: forall x y, wfC y -> st2soC x y -> st2sisoC (st2siH x) y.
Proof. pcofix CIH.
       intros.
       pinversion H1. 
       - subst. pfold. rewrite(st_eq(st2siH (end))). simpl.
         constructor.
       - subst. rewrite(st_eq(st2siH (p ! cocons (l, s, x0) conil))). simpl.
         fold si.next.
         rewrite(coseq_eq(si.next (cocons (l, s, x0) conil))). simpl.
         rewrite(coseq_eq(si.next conil)). simpl.
         pfold. apply st2siso_snd with (y := y0).
         right.
         apply CIH. admit. easy. easy.
       - subst.
         pinversion H. subst.
         rewrite(st_eq(st2siH (p & conil))). simpl.
         pfold. pinversion H0. subst.
         easy.
         apply mon_wfH.
         subst.
         destruct H2 as (l1,(s1,(t1,(t2,(H1a,(H1b,H1c)))))).
         subst.
         rewrite(st_eq(st2siH (p & cocons (l1, s1, t1) l))). simpl.
         pfold. apply st2siso_rcv with (y := t2).
         right. apply CIH.
         pinversion H0. subst.
         pinversion H6. subst.
         destruct H7 as (l3,(s3,(t3,(H7a,H7b)))). inversion H7a. subst.
         destruct H7b; easy.
         apply mon_fHo.
         apply mon_wfH.
         destruct H1c; easy.
         constructor.
         apply mon_f2Ho.
         apply st2so_mon.
Admitted.

Lemma si_sisoDec: forall x y, wfC y -> st2siC x y -> st2sisoC (st2soH x) y.
Admitted.

Lemma _3_15: forall T U V, wfC T -> st2soC U T -> st2siC V T -> exists W, st2siC W U /\ st2soC W V.
Proof. intros.
       apply so_sisoDec in H0; try easy.
       apply si_sisoDec in H1; try easy.
       exists (st2siH U). split. admit.
Admitted.
