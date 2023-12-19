From ST Require Import stream st so si siso norefined.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts.

Local Open Scope string_scope.

(* Definition subtypeA (T T': st): Prop :=
  forall U,  st2soCA T U /\
  forall V', st2siCA T' V' /\
  exists W,  so2sisoC U W /\
  exists W', si2sisoC V' W' /\ W ~<A W'. *)

Definition subtype (T T': st): Prop :=
  forall U, st2soC T U /\ 
  forall V', st2siC T' V' /\
  exists (W: siso), st2sisoC U  (@und W) /\
  exists (W':siso), st2sisoC V' (@und W') /\ (@und W) ~< (@und W').

Definition subtypeA (T T': st): Prop :=
  forall U, st2soC T U /\ 
  forall V', st2siC T' V' /\
  exists (W: siso), st2sisoC U  (@und W) /\
  exists (W':siso), st2sisoC V' (@und W') /\ refinementN W W'.

Lemma equivLeft: forall T T', subtypeA T T' -> subtype T T'.
Proof. unfold subtype, subtypeA.
       intros.
       split.
       specialize(H U).
       destruct H as (H1, H).
       exact H1.
       intro V'.
       split.
       specialize(H U).
       destruct H as (H1, H).
       specialize(H V').
       destruct H as (H2, H).
       exact H2.
       specialize(H U).
       destruct H as (H1, H).
       specialize(H V').
       destruct H as (H2, H).
       destruct H as (W, (H4, (W', (H5, H6)))).
       exists W. split. exact H4. exists W'. split. exact H5.
       simpl.
       apply sisoE in H6.
       easy.
Qed.

Definition nsubtype (T T': st): Prop :=
  exists U,  st2soC T U /\
  exists V', st2siC T' V' /\
  forall W, st2sisoC U (@und W) /\ 
  forall W', st2sisoC V' (@und W') /\ nRefinementN W W'.

Lemma subneqL: forall T T', subtype T T' -> nsubtype T T' -> False.
Proof. intros.
       unfold subtype, nsubtype in *.
       destruct H0 as (U, (Ha, (V', (Hb, H0)))).
       specialize(H U).
       destruct H as (Ha1, H).
       destruct (H V') as (Hb1, (W, (Hc, (W', (Hd, He))))).
       specialize(H0 W).
       destruct H0 as (Hc1, H0).
       destruct (H0 W') as (Hd', He').
       apply nrefNLS in He. easy. easy.
Qed.

Definition T': st :=
  st_send "q" [
               ("cont",sint ,st_receive "p" [("success",sint,st_end);("error",sbool,st_end)]);
               ("stop",sunit,st_receive "p" [("success",sint,st_end);("error",sbool,st_end)])
              ].

Definition T: st :=
  st_receive "p" [
                  ("success",sint ,st_send "q" [("cont",sint,st_end);("stop",sunit,st_end)]);
                  ("error",  sbool,st_send "q" [("cont",sint,st_end);("stop",sunit,st_end)])
                 ].

Definition ListT := [("q","!");("p","?")]. 

Definition TW  := st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))].
Definition TW' := st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))].

Lemma TWEqList: cosetIncLC (act TW) ListT.
Proof. pfold.
       unfold TW, ListT.
       simpl.
       rewrite(coseq_eq(act ("p" & [("success", I, "q" ! [("cont", I, st_end)])]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.
       
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq(act ("q" ! [("cont", I, end)]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.
       
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq (act (st_end))).
       unfold coseq_id.
       simpl.
       constructor.
Qed.

Lemma TW'EqList: cosetIncLC (act TW') ListT.
Proof. pfold.
       unfold TW', ListT.
       simpl.
       rewrite(coseq_eq(act ("q" ! [("cont", I, "p" & [("success", I, end)])]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq (act (st_end))).
       unfold coseq_id.
       simpl.
       constructor.
Qed.

Lemma TWEqListR: cosetIncR ListT (act TW).
Proof. rewrite(coseq_eq(act TW)).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit2 ("q", "!")
       (Delay(cocons ("p", "?") (act ("q" ! [("cont", I, end)]))))
       ("p", "?") (act ("q" ! [("cont", I, end)]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("q" ! [("cont", I, end)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("q", "!")
       (Delay(cocons ("q", "!") (act (end))))
       ("q", "!") (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       specialize(CoInSplit1 ("p", "?")
       (Delay(cocons ("p", "?") (act ("q" ! [("cont", I, end)]))))
       ("p", "?") (act ("q" ! [("cont", I, end)]))
       ); intro Hb.
       constructor.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma TWEqListR': cosetIncR ListT (act TW').
Proof. rewrite(coseq_eq(act TW')).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("q", "!")
       (Delay(cocons ("q", "!") (act ("p" & [("success", I, end)]))))
       ("q", "!") (act ("p" & [("success", I, end)]))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("p", "?")
       (Delay(cocons ("q", "!")(act ("p" & [("success", I, end)]))))
       ("q", "!") (act ("p" & [("success", I, end)]))
       ); intro Ha. 
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", "?")
       (Delay(cocons ("p", "?") (act (end))))
       ("p", "?") (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma st1: subtype T' T.
Proof. unfold subtype, T, T'.
       intros U.
       split.
       pcofix H.
       pfold.
       specialize (st2so_snd (upaco2 st2so r)
                             "cont" 
                             sint
                             (st_receive "p" [("success", sint, st_end); ("error", sbool, st_end)])
                             U
                             ([("cont", sint,  st_receive "p" [("success", sint, st_end); ("error", sbool, st_end)]);
                               ("stop", sunit, st_receive "p" [("success", sint, st_end); ("error", sbool, st_end)])])
                             "q"); intro HS.
       apply HS.
       simpl. left. easy.
       unfold upaco2.
       left.
       pcofix H1.
       pfold.
       specialize(st2so_snd (upaco2 st2so r0) 
                            "cont" 
                            sint 
                            (st_receive "p" [("success", sint, st_end); ("error", sbool, st_end)])
                            U
                            [("cont", sint, st_receive "p" [("success", sint, st_end); ("error", sbool, st_end)])]); intro H2.
       apply H2.
       simpl. left. easy.
       unfold upaco2.
       right. easy.

       split.
       pcofix H.
       pfold.
       specialize (st2si_rcv (upaco2 st2si r)
                             "success" 
                             sint
                             (st_send "q" [("cont", sint, st_end); ("stop", sunit, st_end)])
                             V'
                             ([("success", sint,  st_send "q" [("cont", sint, st_end); ("stop", sunit, st_end)]);
                               ("error",   sbool, st_send "q" [("cont", sint, st_end); ("stop", sunit, st_end)])])
                             "p"); intro HS.
       apply HS.
       simpl. left. easy.
       unfold upaco2.
       left.
       pcofix H1.
       pfold.
       specialize (st2si_rcv (upaco2 st2si r0) 
                             "success"
                             sint 
                             (st_send "q" [("cont", sint, st_end); ("stop", sunit, st_end)])
                             V'
                             [("success", sint, st_send "q" [("cont", sint, st_end); ("stop", sunit, st_end)])]); intro H2.
       apply H2.
       simpl. left. easy.
       unfold upaco2.
       right. easy.

       assert(singleton(st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))])) as Hs1.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       
       exists(mk_siso (st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))]) Hs1).
       split.
(*        symmetry. *)
       pcofix H.
       pfold.
       simpl in *.
       specialize(st2siso_snd (upaco2 st2siso r) "cont" sint 
                              (st_receive "p" [("success", sint, st_end)])
                              U
                              [("cont", sint, st_receive "p" [("success", sint, st_end)])]
                              "q"); intro H2.

       apply H2.
       simpl. left. easy.
       unfold upaco2.
       right. easy.

       assert(singleton(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))])) as Hs2.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       exists(mk_siso(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))]) (Hs2)).

       split.
(*        symmetry. *)
       pcofix H.
       pfold.
       specialize(st2siso_rcv (upaco2 st2siso r) "success" sint 
                              (st_send "q" [("cont", sint, st_end)])
                              V'
                              [("success", sint, st_send "q" [("cont", sint, st_end)])]
                              "p"); intro H2.
       apply H2.
       simpl. left. easy.
       unfold upaco2.
       right. easy.

       pcofix CIH.
       pfold.
       specialize (_sref_b (upaco2 refinementR r)
                           (st_receive "p" [("success", sint, st_end)])
                           st_end
                           "q" "cont" sint sint
                           (bp_receivea "p" "success" sint) 1
                           ); intro H.
       simpl in H.
      
       rewrite(siso_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) ("q" ! [("cont", I, end)])))) in H.
       simpl in H.
       apply H.

       apply srefl. (*subsort*)

       rewrite (siso_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end)))).
       simpl.
       unfold upaco2.
       left.
       pfold.
       apply _sref_in.

       apply srefl. (*subsort*)

       unfold upaco2.
       left.
       pfold.
       apply _sref_end.

       unfold act_eq.
       intros (p, s).
       split.
       intro Ha.
       unfold CoIn in Ha.
       punfold Ha.
       inversion Ha.
       subst.
       simpl in H0.
       inversion H0.
       rewrite(coseq_eq(act (merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end)))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act (end))). simpl. easy.
       subst.
       simpl in H0.
       inversion H0.
       subst.
       unfold upaco2 in H2.
       destruct H2.
       punfold H2.
       inversion H2.
       subst. simpl in H3. easy.
       simpl in *.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.

       intro Ha.
       unfold CoIn in Ha.
       punfold Ha.
       inversion Ha.
       subst.
       simpl in H0.
       inversion H0.
       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act (end))). simpl. easy.
       subst.
       simpl in H0.
       inversion H0.
       subst.
       unfold upaco2 in H2.
       destruct H2.
       punfold H2.
       inversion H2.
       subst. simpl in H3. easy.
       simpl in *.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

CoFixpoint TS: st :=
  st_send "p" [("l3",sint,TS)].

CoFixpoint TSso: so :=
  so_send "p" ("l3",sint,TSso).

CoFixpoint TB: st :=
  st_receive "p"
  [
   ("l1",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,TB)])])]);
   ("l2",sint,TS)
  ].


CoFixpoint TB': st :=
  st_receive "p"
  [
   ("l1",sint,st_send "p" [("l3",sint,TB')]);
   ("l2",sint,TS)
  ].


CoFixpoint W3: st :=
  st_receive "p" [("l1",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,W3)])])])].

Lemma w3singleton: singleton W3.
Proof. pcofix CIH.
       pfold. 
       rewrite(siso_eq W3). simpl.
       constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.

Definition W4_gen (cont: st): st :=
  st_receive "p" [("l1",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,(cont))])])])].

CoFixpoint W4 := W4_gen W4.

Lemma W4eq: W4 = W4_gen W4.
Proof. setoid_rewrite(siso_eq W4) at 1. simpl.
       unfold W4_gen. easy.
Qed.

Lemma W4eq2: W4_gen W4 = st_receive "p" [("l1",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,(W4))])])])].
Proof. easy. Qed.

Let EqW4 := (W4eq, W4eq2).

CoFixpoint W1: st := st_receive "p" [("l1",sint,st_send "p" [("l3",sint,W1)])].

Lemma w1singleton: singleton W1.
Proof. pcofix CIH. pfold. 
       rewrite(siso_eq W1). simpl.
       constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.

CoFixpoint W1so: so := so_receive "p" [("l1",sint,so_send "p" ("l3",sint,W1so))].

(* CoFixpoint W1siso: siso := siso_receive "p" ("l1",sint,siso_send "p" ("l3",sint,W1siso)). *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS: forall n : nat, ev n -> ev (S (S n)).

Definition listW3 := [("p","?"); ("p","!")].

Lemma W3EqList: cosetIncLC (act W3) listW3.
Proof. pcofix CIH.
       pfold.
(*        rewrite 2! EqW4. *)
       simpl.
       rewrite(siso_eq W3).
       simpl.
       rewrite(coseq_eq ((act ("p" & [("l1", I, "p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right.
       apply CIH.
Qed.

Lemma W3EqList2: forall r, paco2 cosetIncL r (act W3) listW3.
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(siso_eq W3).
       simpl.
       rewrite(coseq_eq ((act ("p" & [("l1", I, "p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right.
       apply CIH.
Qed.

Lemma W1EqList: cosetIncLC (act W1) listW3.
Proof. pcofix CIH.
       pfold.
       rewrite(siso_eq W1).
       simpl.
       rewrite(coseq_eq ((act ("p" & [("l1", I, "p" ! [("l3", I, W1)])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq ((act ("p" ! [("l3", I, W1)])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right. 
       apply CIH.
Qed.

Lemma W1EqList2: forall r, paco2 cosetIncL r (act W1) listW3.
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(siso_eq W1).
       simpl.
       rewrite(coseq_eq ((act ("p" & [("l1", I, "p" ! [("l3", I, W1)])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq ((act ("p" ! [("l3", I, W1)])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right. 
       apply CIH.
Qed.

Lemma W1EqList3: forall n r, paco2 cosetIncL r (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)) listW3.
Proof. pcofix CIH.
       intros n.
       induction n; intros.
       simpl. apply W1EqList2.
       simpl.
       rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
       simpl. 
       rewrite(coseq_eq((act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])))).
       unfold coseq_id. simpl.
       pfold. constructor.
       simpl. left. easy.
       unfold upaco2. left.
       apply IHn.
Qed.

Lemma W3EqListR: cosetIncR listW3 (act W3).
Proof. rewrite(coseq_eq (act W3)).
       unfold coseq_id. simpl.
       constructor.
       simpl.

       specialize(CoInSplit1 ("p", "?")
       (Delay (cocons ("p", "?") (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
       ("p", "?") (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
       ); intro Ha.
       apply Ha.
       simpl. easy.
       easy.

       simpl.
       constructor.
       simpl.
       specialize(CoInSplit2 ("p", "!")
       (Delay(cocons ("p", "?") (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
       ("p", "?") (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
       ); intro Ha.
       simpl in Ha.
       simpl.
       apply Ha.
       easy.
       easy.
       rewrite(coseq_eq((act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])))).
       unfold coseq_id.
       simpl.

       specialize(CoInSplit1 ("p", "!")
       (Delay (cocons ("p", "!") (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))))
       ("p", "!") (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))
       ); intro Hb.
       simpl in Hb.
       apply Hb.
       easy.
       easy.
       constructor.
Qed.

Lemma W1EqListR: cosetIncR listW3 (act W1).
Proof. rewrite(coseq_eq (act W1)).
       unfold coseq_id. simpl.
       constructor.
       specialize(CoInSplit1 ("p", "?")
       (Delay(cocons ("p", "?") (act ("p" ! [("l3", I, W1)]))))
       ("p", "?") (act ("p" ! [("l3", I, W1)]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       specialize(CoInSplit2 ("p", "!")
       (Delay(cocons ("p", "?") (act ("p" ! [("l3", I, W1)]))))
       ("p", "?") (act ("p" ! [("l3", I, W1)]))
       ); intro Ha.
       constructor.
       simpl in Ha.
       apply Ha.
       easy. easy.

       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", "!")
       (Delay(cocons ("p", "!") (act W1)))
       ("p", "!") (act W1)
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma inW1ns: forall n l s, CoInR ("p", "!") (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq (act W1)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("p", "!")
       (Delay(cocons ("p", "?") (act ("p" ! [("l3", I, W1)]))))
       ("p", "?") (act ("p" ! [("l3", I, W1)]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", "!")
       (Delay(cocons ("p", "!") (act W1)))
       ("p", "!") (act W1)
       ); intro Ha'.
       apply Ha'. simpl. easy. easy.

       simpl.
       rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" l s) (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)))).
       simpl.
       rewrite(coseq_eq(act ("p" & [(l, s, merge_bp_contn "p" (bp_receivea "p" l s) W1 n)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("p", "!")
       (Delay(cocons ("p", "?") (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n))))
       ("p", "?") (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       apply IHn.
Qed.

Lemma inW1nsA: forall n r l s, paco2 CoInRA r ("p", "!") (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq (act W1)).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id.
       simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act W1)). simpl. easy.

       simpl.
       rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" l s) (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)))).
       simpl.
       rewrite(coseq_eq(act ("p" & [(l, s, merge_bp_contn "p" (bp_receivea "p" l s) W1 n)]))).
       unfold coseq_id.
       simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n))). simpl. easy. easy.
       unfold upaco2. left. 
       unfold CoIn in IHn.
       apply IHn.
Qed.

Lemma inW1nsA2: forall n l s, CoIn ("p", "!") (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq (act W1)).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id.
       simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act W1)). simpl. easy.

       simpl.
       rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" l s) (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)))).
       simpl.
       rewrite(coseq_eq(act ("p" & [(l, s, merge_bp_contn "p" (bp_receivea "p" l s) W1 n)]))).
       unfold coseq_id.
       simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n))). simpl. easy. easy.
       unfold upaco2. left. 
       unfold CoIn in IHn.
       apply IHn.
Qed.

Lemma helper3: forall n W,
("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) n)])])
=
("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" & [("l1", I, "p" ! [("l3", I, W)])]) n)]).
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) n))).
       simpl.
       rewrite IHn.
       rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" & [("l1", I, "p" ! [("l3", I, W)])]) n))).
       simpl. easy.
Qed.

Lemma acteq1: act_eq W3 (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
Proof. unfold act_eq.
       destruct a as (p, s).
       split.
       { intro Hp.
         unfold CoIn in Hp.
         punfold Hp.
         inversion Hp.
         { subst.
           simpl in H. inversion H.
           rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
           unfold coseq_id. simpl.
           pfold.
           apply CoInSplit1A with (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
           simpl. easy.
         }
         { subst.
           simpl in H.
           inversion H.
           subst; clear H.
           unfold upaco2 in H1.
           destruct H1.
           { punfold H.
             inversion H. subst.
             inversion H1. subst.
             rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
             unfold coseq_id. simpl.
             pfold.
             apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
             simpl. easy. easy.
             unfold upaco2. left. pfold.
             rewrite(coseq_eq (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
             unfold coseq_id. simpl.
             apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)).
             simpl. easy. easy.
             unfold upaco2. left. pfold.
             rewrite(coseq_eq(act W1)).
             unfold coseq_id. simpl.
             apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))).
             simpl. easy. easy.
             unfold upaco2. left. pfold.
             simpl. rewrite(coseq_eq (act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
             apply CoInSplit1A with (ys := (act W1)). simpl. easy.
             subst.
             simpl in H1. inversion H1. subst.
             clear H1.
             pfold.
             rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
             unfold coseq_id. simpl.
             apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
             simpl. easy. easy.
             unfold upaco2. left. pfold.
             rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
             unfold coseq_id. simpl.
             apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)).
             simpl. easy. easy.
             unfold upaco2. left.
             pcofix CIH.
             pfold.
             rewrite(coseq_eq(act W1)).
             unfold coseq_id. simpl.
             apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))).
             simpl. easy. easy.
             unfold upaco2. left. pfold.
             rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
             unfold coseq_id. simpl.
             apply CoInSplit2A with (y := ("p", "!")) (ys := (act W1)). simpl. easy. easy.
             unfold upaco2. right. exact CIH.
             apply CoIn_mon.
           }
           { easy.
           }
         }
         { apply CoIn_mon.
         }
       }
       { intro Hp.
         pcofix CIH.
         punfold Hp.
         inversion Hp.
         { subst. simpl in H.
           inversion H.
           rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
           pfold.
           apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy.
         }
         { subst. simpl in H.
           unfold upaco2 in H1.
           destruct H1.
           { inversion H.
             subst. clear H.
             punfold H1.
             inversion H1.
             subst.
             simpl in H. inversion H.
             rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
             pfold.
             apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy.
             subst.
             simpl in H. inversion H. subst. clear H.
             unfold upaco2 in H3.
             destruct H3.
             { punfold H.
               pfold.
               inversion H.
               { simpl in H3.
                 inversion H3. subst. clear H3.
                 rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
                 apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy.
               }
               { subst. simpl in H3. inversion H3. subst.
                 clear H3.
                 unfold upaco2 in H5.
                 destruct H5.
                 { punfold H3.
                   inversion H3.
                   subst. simpl in H5. inversion H5. subst. clear H5.
                   rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
                   apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
                   unfold upaco2. left. pfold.
                   rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
                   unfold coseq_id. simpl.
                   apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy.
                   subst. simpl in H5. inversion H5. subst. clear H5.
                   rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
                   apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
                   unfold upaco2. left. pfold.
                   rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
                   unfold coseq_id. simpl.
                   apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy. easy.
                   unfold upaco2. left. pfold.
                   rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
                   apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
                   unfold upaco2. left. pfold.
                   rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
                   apply CoInSplit2A with (y := ("p", "!")) (ys := act W3). simpl. easy. easy.
                   unfold upaco2. right. apply CIH.
                   apply CoIn_mon.
                 }
                 { easy. }
               }
               apply CoIn_mon.
             }
             { easy.
             }
             { apply CoIn_mon.
             }
          }
          { easy.
          }
        }
          { apply CoIn_mon.
          }
       }
Qed.

Lemma acteq2:
act_eq ("p" ! [("l3", I, W3)]) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1).
Proof. unfold act_eq.
       intros (p,s).
       split.
       intro Hp.
       punfold Hp. inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)). simpl. easy. easy.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act W1)). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act W1)). simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1.
       pfold.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)). simpl. easy. easy.
       unfold upaco2. left.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq (act W1)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W1)). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       
       intro Hp.
       punfold Hp. inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       pfold.
       rewrite(coseq_eq (act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. easy.
       subst. simpl in H1. inversion H1. subst. clear H2 H1.
       unfold upaco2 in H3. destruct H3. punfold H1. inversion H1. subst. simpl in H2. inversion H2. subst. clear H2.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act W3)). simpl. easy.
       subst. simpl in H2. inversion H2. subst. clear H2.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

Lemma acteq3: forall n,
act_eq W3
  (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
     (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
Proof. intro n.
       unfold act_eq.
       intros (p,s).
       split. intros Hp.
       unfold CoIn.
       revert p s Hp.
       induction n; intros.
       simpl. 
       pfold.
       rewrite(coseq_eq((act
        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))))).
       unfold coseq_id. simpl.
       punfold Hp.
       inversion Hp.
       subst. simpl in H. inversion H. subst. clear H.
       apply CoInSplit1A with (ys := (act
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                 (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1.
       destruct H1.
       punfold H.
       inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys :=(act
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       simpl. easy. easy.
       rewrite(coseq_eq((act
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act W1)).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act W1)).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act ("p" ! [("l3", I, W1)]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys :=  (act W1)). simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       simpl. easy. easy.
       rewrite(coseq_eq((act
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       simpl. easy. easy.
       rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)).
       simpl. easy. easy.
       unfold upaco2. left.
       pcofix CIH.
       pfold. 
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))).
       simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W1)).
       simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       simpl.
       rewrite(coseq_eq(act
       (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                 (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                    (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))))).
       unfold coseq_id. simpl.
       punfold Hp.
       inversion Hp.
       simpl in H. inversion H. subst. clear H.
       pfold.
       apply CoInSplit1A with (ys := (act
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                 (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                    (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                       (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))).
       simpl. easy.

       subst. 
       simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1.
       destruct H1.
       punfold H.
       inversion H. subst. simpl in H1. inversion H1. subst.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := act
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
             (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                   (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))). simpl. easy. easy.
       unfold upaco2. left. apply IHn.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := act
         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                  (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                     (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))). simpl. easy. easy.
       unfold upaco2. left. apply IHn.
       unfold CoIn. pfold. exact Hp.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       (*middle*)
       revert p s.
       induction n; intros.
       simpl in *.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       punfold H.
       inversion H. simpl in H0. subst. inversion H0. subst. clear H0.
       pfold. 
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       simpl. easy.

       subst. simpl in H0. inversion H0. subst. clear H0.
       unfold upaco2 in H2.
       destruct H2. punfold H0.
       inversion H0. subst. simpl in H2. inversion H2. subst. clear H2. easy.
       subst. simpl in H2. simpl in H2. inversion H2. subst. clear H2.
       unfold upaco2 in H4.
       destruct H4. punfold H2.
       inversion H2. subst. simpl in H4. inversion H4. subst. clear H4. easy.
       subst. simpl in H4. simpl in H4. inversion H4. subst. clear H4.
       unfold upaco2 in H6.
       destruct H6. punfold H4.
       inversion H4. subst. simpl in H6. inversion H6. subst. clear H6. easy.
       subst. simpl in H6. simpl in H6. inversion H6. subst. clear H6.
       unfold upaco2 in H8.
       destruct H8. punfold H6.
       inversion H6. subst. simpl in H8. inversion H8. subst. clear H8. easy.
       subst. simpl in H8. inversion H8. subst. clear H8.
       unfold upaco2 in H10.
       destruct H10. punfold H8. inversion H8. subst. simpl in H10. 
       inversion H10. subst. 
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold. 
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))).
       simpl. easy. 
       subst. simpl in H10. inversion H10. subst. clear H10.
       pcofix CIH.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys :=(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)).
       simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       simpl in H.
       punfold H.
       inversion H. subst.
       simpl in H0.
       inversion H0. 
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       simpl. easy.
       simpl in H0. inversion H0. subst. clear H0.
       unfold upaco2 in H2.
       destruct H2.
       apply IHn.
       unfold CoIn.
       apply H0. easy.
       apply CoIn_mon.
Qed.

Lemma acteq4: forall n,
act_eq ("p" ! [("l3", I, W3)])
  (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
     (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
Proof. intro n.
       unfold act_eq.
       intros (p,s).
       split. intros Hp.
       revert p s Hp.
       induction n; intros.
       simpl.

       punfold Hp.
       inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)). simpl. easy. easy.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq (act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act W1)). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       
       unfold upaco2 in H1. destruct H1.
       punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))). simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       unfold coseq_id. simpl. unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
       unfold coseq_id. simpl. unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)). simpl. easy. easy.
       unfold upaco2. left.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys :=  (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W1)). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       
       simpl. apply acteq3.
       punfold Hp.
       inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq (act W3)). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])) ).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H.
       unfold CoIn. pfold. exact H.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       (*middle*)
       revert p s.
       induction n; intros.
       simpl in *.

       punfold H.
       inversion H. subst. simpl in H0. inversion H0. subst. clear H0.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy.
       subst.  simpl in H0. inversion H0. subst. clear H0.
       inversion H. subst. simpl in H0. inversion H0. subst. easy.
       subst. simpl in H0. inversion H0. subst. clear H0 H3 H4.

       unfold upaco2 in H2. destruct H2. punfold H0. inversion H0. subst. simpl in H2.
       inversion H2. subst. easy.
       subst. simpl in H2. inversion H2. subst. clear H0 H2 H3.
       unfold upaco2 in H4. destruct H4. punfold H0. inversion H0. subst. simpl in H2.
       inversion H2. subst. easy.
       subst. simpl in H2. inversion H2. subst. clear H0 H2 H3.
       unfold upaco2 in H4. destruct H4. punfold H0. inversion H0. subst. simpl in H2.
       inversion H2. subst. easy.
       subst. simpl in H2. inversion H2. subst. clear H0 H2 H3.
       unfold upaco2 in H4. destruct H4. punfold H0. inversion H0. subst. simpl in H2.
       inversion H2. subst.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act W3)). simpl. easy.
       subst. simpl in H2. inversion H2. subst. clear H0 H2.

       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       rewrite(coseq_eq (act W3)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.

       simpl in H.
       apply acteq3 in H.
       punfold H. inversion H. subst.
       simpl in H0. inversion H0. subst. clear H0.
       rewrite (coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). 
       simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])) ). 
       simpl. easy.
       subst. simpl in H0. inversion H0. subst. clear H0.
       pfold.
       unfold upaco2 in H2. destruct H2. punfold H0. inversion H0.
       subst. simpl in H2. inversion H2. subst. clear H2.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act W3) ). simpl. easy.
       subst. simpl in H2. inversion H2. subst. clear H2.
       unfold upaco2 in H4. destruct H4. punfold H2. inversion H2.
       subst. simpl in H4. inversion H4. subst. clear H4.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act W3) ). simpl. easy.
       subst. simpl in H4. inversion H4. subst. clear H4.
       unfold upaco2 in H6. destruct H6. punfold H4.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

Lemma acteq5: forall n,
act_eq ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
  (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
     (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
Proof. intro n.
       unfold act_eq.
       intros (p,s).
       split. intros Hp.
       revert p s Hp.
       induction n; intros.
       simpl.
       
       punfold Hp.
       inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)). simpl. easy. easy.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act W1)). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H2.
       unfold upaco2 in H3. destruct H3. punfold H1. inversion H1. subst. simpl in H2. inversion H2. subst. clear H2.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)) ). simpl. easy.
       subst. simpl in H2. inversion H2. subst. clear H2.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act W1)). simpl. easy. easy.
       unfold upaco2.
       left.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W1)). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.

       simpl. apply acteq4.
       punfold Hp.
       inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act W3) ). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1.
       unfold CoIn. exact H.
       easy.
       apply CoIn_mon.
       (*middle*)
       revert p s.
       induction n; intros.
       simpl in *.

       punfold H. inversion H. subst. simpl in H0. inversion H0. subst. clear H0.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq (act W3)). unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy.
       subst. simpl in H0. inversion H0. subst. clear H0.
       unfold upaco2 in H2. destruct H2. punfold H0. inversion H0. subst. simpl in H2. inversion H2. subst. easy.
       subst. simpl in H2. inversion H2. subst. clear H0 H3 H2.
       unfold upaco2 in H4. destruct H4.  punfold H0. inversion H0. subst. simpl in H2. inversion H2. subst. easy.
       subst. simpl in H2. inversion H2. subst. clear H0 H3 H2.
       unfold upaco2 in H4. destruct H4.  punfold H0. inversion H0. subst. simpl in H2. inversion H2. subst.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy.
       subst. simpl in H2. inversion H2. subst. clear H2.
       pcofix CIH.
       pfold. 
       rewrite(coseq_eq (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.

       simpl in H. apply acteq4 in H.
       punfold H. inversion H. subst. simpl in H0. inversion H0. subst. clear H0.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy.
       subst. simpl in H0. inversion H0. subst. clear H0.
       unfold upaco2 in H2. destruct H2. punfold H0. inversion H0. subst. simpl in H2.
       inversion H2. subst. clear H2.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       unfold upaco2. left. pfold. exact H0.
       subst. simpl in H2. inversion H2. subst. clear H2.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3)). simpl. easy. easy.
       unfold upaco2. left.
       pcofix CIH.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("p", "?")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act ("p" ! [("l3", I, W3)])) ). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("p", "!")) (ys := (act W3) ). simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

Lemma W1W3UnfVar4R: forall n,
  ev n ->
  W3 ~<  merge_bp_contn "p" (bp_receivea "p" "l1" sint) W1 n.
Proof. intros.
       generalize dependent n.
       pcofix CIH.
       intros.
       induction H0; intros.
       simpl.

         rewrite(siso_eq (W1)).
         simpl.
         pfold.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         apply _sref_out.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                   ); intro Hb.
         simpl in Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq W1).
         simpl.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                   ); intro Hc.
        simpl in Hc.
        rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]))))) in Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
        simpl.
        rewrite(siso_eq W1).
        simpl.
        apply Hc.
        apply srefl.
        rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
        simpl.
        unfold upaco2.
        right.
        specialize(CIH 2).
        simpl in CIH.
        rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))) in CIH.
        simpl in CIH.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)) in CIH.
        simpl in CIH.
        apply CIH.
        constructor.
        constructor.
        apply acteq1.
        apply acteq2.

        rename CIH into Hn.
        simpl. simpl in Hn.

        rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
        simpl.

        pfold.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq W1).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
                   ); intro Hb.
         simpl in Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))))
         in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))) in Hb.
         simpl in Hb.
         rewrite helper3 in Hb.

         apply Hb.
         apply srefl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.

         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
                   ); intro Hc.
         simpl in Hc.
         rewrite(siso_eq W1).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
             (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         rewrite helper3 in Hc.
         apply Hc.
         apply srefl.

         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+4)
                   ); intro Hd.
         simpl in Hd.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
             (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                   (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))))))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                  (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                 (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))) in Hd.
         simpl in Hd.
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite helper3 in Hd.
         rewrite(siso_eq W1).
         simpl.
         apply Hd.
         apply srefl.
         unfold upaco2.
         right.
         specialize(Hn (n.+4)).
         simpl in Hn.
         apply Hn.
         constructor.
         constructor.
         easy.
         apply acteq3.
         apply acteq4.
         apply acteq5.
Qed.

Lemma st2: forall n: nat, subtype TB TB'.
Proof. unfold subtype.
       intros n U.
       split.
       pcofix CIH.
       pfold.
       rewrite (siso_eq TB).
       simpl.
       specialize (st2so_rcv (upaco2 st2so r) "p"
                             (["l1";"l2"])
                             ([sint;sint])
                             U
                             ([st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, TB)])])]; TS])
                             [(st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, TB)])])]); TS ] 
       ); intro H.
       simpl in H.
       apply H.
       apply Forall_forall.
       intros (x,y).
       simpl. intro Ha.
       destruct Ha as [Ha | Ha].
       inversion Ha.

       unfold upaco2.
       left.
       pcofix CIH2.
       pfold.
       specialize (st2so_snd (upaco2 st2so r0) 
                             "l3" sint
                             (st_send "p" [("l3", sint, st_send "p" [("l3", sint, TB)])])
                             (st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, TB)])])])
                             [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, TB)])])]
                             "p"
       ); intro Hb.
       simpl in Hb.
       apply Hb.
       left. easy.
       unfold upaco2.
       right. easy.
       destruct Ha as [Ha | Ha].
       inversion Ha.
       rewrite (siso_eq TS).
       simpl.
       unfold upaco2.
       left.
       pcofix CIH2.
       specialize (st2so_snd (upaco2 st2so r0) "l3" sint
                             TS
                             TS
                             ([("l3", sint, TS)])
                             "p"
       ); intro Hb.
       setoid_rewrite (siso_eq TS) at 6 in Hb.
       simpl in Hb.
       pfold.
       apply Hb.
       left. easy.
       unfold upaco2.
       right.
       setoid_rewrite (siso_eq TS) at 2.
       simpl. easy.

       easy.
       setoid_rewrite (siso_eq TB) in CIH.
       simpl in CIH.
       unfold upaco2.
       right.
       apply CIH.

       intro V'.
       split.
       pcofix CIH.
       pfold.
       rewrite (siso_eq TB').
       simpl.
       specialize (st2si_rcv (upaco2 st2si r) "l1" sint
       (st_send "p" [("l3", sint, TB')])
       V'
       ([("l1", sint, st_send "p" [("l3", sint, TB')]); ("l2", sint, TS)])
       "p"
       ); intro H.
       apply H.
       simpl. left. easy.

       unfold upaco2.
       left.
       pcofix CIH2.
       pfold.
       specialize (st2si_rcv (upaco2 st2si r0) "l1" sint
       (st_send "p" [("l3", sint, TB')])
       V'
       [("l1", sint, st_send "p" [("l3", sint, TB')])]
       ); intro Ha.
       simpl in H.
       apply Ha. 
       simpl. left. easy.

       unfold upaco2.
       right. easy.

       exists (mk_siso W3 (w3singleton)).
       split.
(*        symmetry. *)
       pcofix CIH.
       pfold. simpl.
       rewrite (siso_eq W3).
       simpl.
       specialize (st2siso_rcv (upaco2 st2siso r) "l1" sint
       (st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])])
       U
       [("l1", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])])]
       "p"
       ); intro H.
       simpl in H.
       apply H.
       left. easy.

       unfold upaco2.
       right. simpl in CIH.
       rewrite (siso_eq W3) in CIH.
       simpl in CIH.
       easy.

       exists (mk_siso W1 (w1singleton)).
       split.
(*        symmetry. *)
       pcofix CIH.
       pfold. simpl.
       rewrite (siso_eq W1).
       simpl.
       specialize (st2siso_rcv (upaco2 st2siso r) "l1" sint
       (st_send "p" [("l3", sint, W1)])
       V'
       ([("l1", sint, st_send "p" [("l3", sint, W1)])])
       "p"
       ); intro H.
       apply H. left. easy.

       unfold upaco2.
       right. simpl in CIH.
       rewrite (siso_eq W1) in CIH.
       simpl in CIH.
       easy.

       specialize(W1W3UnfVar4R 0); intros.
       rewrite(siso_eq(merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 0)) in H.
       simpl in H. simpl.
       rewrite(siso_eq W1).
       simpl.
       apply H.
       constructor.
Qed.
