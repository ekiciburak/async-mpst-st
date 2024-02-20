Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.refinement ST.src.reorderingfacts.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition subtype (T T': st): Prop :=
  forall U,  st2soC T U /\
  forall V', st2siC T' V' /\
  exists W,  st2sisoC U W /\
  exists W', st2sisoC V' W' /\ W ~< W'.

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

Definition ListT := [("q",snd);("p",rcv)]. 

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
       specialize(CoInSplit2 ("q", snd)
       (Delay(cocons ("p", rcv) (act ("q" ! [("cont", I, end)]))))
       ("p", rcv) (act ("q" ! [("cont", I, end)]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("q" ! [("cont", I, end)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("q", snd)
       (Delay(cocons ("q", snd) (act (end))))
       ("q", snd) (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       specialize(CoInSplit1 ("p", rcv)
       (Delay(cocons ("p", rcv) (act ("q" ! [("cont", I, end)]))))
       ("p", rcv) (act ("q" ! [("cont", I, end)]))
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
       specialize(CoInSplit1 ("q", snd)
       (Delay(cocons ("q", snd) (act ("p" & [("success", I, end)]))))
       ("q", snd) (act ("p" & [("success", I, end)]))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("p", rcv)
       (Delay(cocons ("q", snd)(act ("p" & [("success", I, end)]))))
       ("q", snd) (act ("p" & [("success", I, end)]))
       ); intro Ha. 
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", rcv)
       (Delay(cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
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

       exists(st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))]).
       split.
(*        symmetry. *)
       pcofix H.
       pfold.
       specialize(st2siso_snd (upaco2 st2siso r) "cont" sint 
                              (st_receive "p" [("success", sint, st_end)])
                              U
                              [("cont", sint, st_receive "p" [("success", sint, st_end)])]
                              "q"); intro H2.
       apply H2.
       simpl. left. easy.
       unfold upaco2.
       right. easy.

       exists(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))]).
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
                           [("p",rcv)]
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

       specialize(_sref_a (upaco2 refinementR r)  (end) (end) "p" "success" (I) (I) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA with (L := []).
       
(*        apply _sref_in. *)

       apply srefl. (*subsort*)

       unfold upaco2.
       left.
       pfold.
       apply _sref_end.
       
       pfold.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       pfold.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       
       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       rewrite(coseq_eq(act (end))).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.

       pfold.
       rewrite(coseq_eq(act (merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end)))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       rewrite(coseq_eq(act (end))).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.

       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       (Delay(cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor.

       rewrite(siso_eq(merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end))).
       simpl.
       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       (Delay(cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor.
Qed.

CoFixpoint TS: st :=
  st_send "p" [("l3",sint,TS)].

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

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS: forall n : nat, ev n -> ev (S (S n)).

Definition listW3 := [("p",rcv); ("p",snd)].

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

       specialize(CoInSplit1 ("p", rcv)
       (Delay (cocons ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
       ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
       ); intro Ha.
       apply Ha.
       simpl. easy.
       easy.

       simpl.
       constructor.
       simpl.
       specialize(CoInSplit2 ("p", snd)
       (Delay(cocons ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
       ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
       ); intro Ha.
       simpl in Ha.
       simpl.
       apply Ha.
       easy.
       easy.
       rewrite(coseq_eq((act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])))).
       unfold coseq_id.
       simpl.

       specialize(CoInSplit1 ("p", snd)
       (Delay (cocons ("p", snd) (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))))
       ("p", snd) (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))
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
       specialize(CoInSplit1 ("p", rcv)
       (Delay(cocons ("p", rcv) (act ("p" ! [("l3", I, W1)]))))
       ("p", rcv) (act ("p" ! [("l3", I, W1)]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       specialize(CoInSplit2 ("p", snd)
       (Delay(cocons ("p", rcv) (act ("p" ! [("l3", I, W1)]))))
       ("p", rcv) (act ("p" ! [("l3", I, W1)]))
       ); intro Ha.
       constructor.
       simpl in Ha.
       apply Ha.
       easy. easy.

       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", snd)
       (Delay(cocons ("p", snd) (act W1)))
       ("p", snd) (act W1)
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma inW1ns: forall n l s, CoInR ("p", snd) (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq (act W1)).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("p", snd)
       (Delay(cocons ("p", rcv) (act ("p" ! [("l3", I, W1)]))))
       ("p", rcv) (act ("p" ! [("l3", I, W1)]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", snd)
       (Delay(cocons ("p", snd) (act W1)))
       ("p", snd) (act W1)
       ); intro Ha'.
       apply Ha'. simpl. easy. easy.

       simpl.
       rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" l s) (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)))).
       simpl.
       rewrite(coseq_eq(act ("p" & [(l, s, merge_bp_contn "p" (bp_receivea "p" l s) W1 n)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("p", snd)
       (Delay(cocons ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n))))
       ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       apply IHn.
Qed.

Lemma helper: forall n W,
  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" & [("l1", I, "p" ! [("l3", I, W)])])
                 =
  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) (S n)) ("p" ! [("l3", I, W)]).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W)]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" & [("l1", I, "p" ! [("l3", I, W)])]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W)]))).
       simpl.
       easy.

       simpl in *.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" & [("l1", I, "p" ! [("l3", I, W)])]))).
       simpl.
       rewrite IHn.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) ("p" ! [("l3", I, W)]))).
       simpl.
       easy.
Qed.

Lemma helper2: forall n W,
         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) n.+1)
         = 
         ("p" & [("l1", I, merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" ! [("l3", I, W)]))]).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W)]))).
       simpl. easy.
       simpl in *.
       rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) n)))).
       simpl.
       rewrite IHn.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W)]))).
       simpl.
       easy.
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

Lemma action_eq1: cosetIncLC (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])) listW3.
Proof. unfold listW3.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right.
       exact CIH.
Qed.

Lemma action_eq2: cosetIncLC (act W1) listW3.
Proof. pcofix CIH.
       unfold listW3.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right.
       exact CIH.
Qed.

Lemma action_eq3: cosetIncR listW3 (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])).
Proof. constructor.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W3)). simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq4: cosetIncR listW3 (act W1).
Proof. constructor.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W1)). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq5: cosetIncLC (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])) listW3.
Proof. unfold listW3.
       pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       apply action_eq1.
Qed.

Lemma action_eq6: cosetIncLC (act ("p" ! [("l3", I, W1)])) listW3.
Proof. unfold listW3.
       pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       apply action_eq2.
Qed.

Lemma action_eq7: cosetIncR listW3 (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])).
Proof. constructor.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act ("p" ! [("l3", I, W3)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W3)). simpl. easy. easy.
       rewrite(coseq_eq(act W3)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])) ). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq8: cosetIncR listW3 (act ("p" ! [("l3", I, W1)])).
Proof. constructor.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W1)). simpl. easy. easy.
       rewrite(coseq_eq(act W1)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W1)). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq9: forall n, cosetIncLC (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])) listW3.
Proof. intro n.
       induction n; intros.
       - simpl. pfold. 
         rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left. apply action_eq2.
       - simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])]))).
         unfold coseq_id. simpl. unfold listW3.
         pfold. constructor. simpl. left. easy.
         left. exact IHn.
Qed.

Lemma action_eq10: forall n, cosetIncR listW3 (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])).
Proof. intro n.
       induction n; intros.
       - simpl. constructor.
         rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W1)). simpl. easy. easy.
         rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))). unfold coseq_id. simpl.
         constructor.
         apply CoInSplit2 with (y := ("p", rcv)) (ys := (act W1)). simpl. easy. easy.
         rewrite(coseq_eq(act W1)). unfold coseq_id. simpl. 
         apply CoInSplit2 with (y := ("p", rcv)) (ys := (act ("p" ! [("l3", I, W1)]))). simpl. easy. easy.
         rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", snd)) (ys := (act W1)). simpl. easy. easy.
         constructor.
       - simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         constructor.
         rewrite(coseq_eq(act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])]))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))). simpl. easy. easy.
         constructor.
         inversion IHn.
         subst.
         inversion H3. subst.
         rewrite(coseq_eq(act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])]))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("p", rcv)) (ys := (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))). simpl. easy. easy.
         exact H2.
         constructor.
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


         specialize(_sref_a (upaco2 refinementR r) ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])  
                                                   ("p" ! [("l3", I, W1)]) "p" "l1" (I) (I) (ap_end) 1); intros HSA.
         simpl in HSA.
         rewrite apend_an in HSA.
         rewrite apend_an in HSA.
         apply HSA with (L := listW3).
         
(*          apply _sref_in. *)
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         
         
(*          apply _sref_out. *)

         specialize(_sref_b (upaco2 refinementR r) ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])  
                                                   (W1) "p" "l3" (I) (I) (bp_end) 1); intros HSB.
         simpl in HSB.
         rewrite bpend_an in HSB.
         rewrite bpend_an in HSB.
         apply HSB  with (L := listW3).
         
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
                            listW3
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
                            listW3
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
        apply W3EqList.
        

        pfold.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
        unfold coseq_id. simpl.
        constructor.
        simpl. left. easy.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
        unfold coseq_id, upaco2.
        simpl. left. pfold. constructor.
        simpl. left. easy.
        unfold upaco2. left.
        apply W1EqList2.

        apply W3EqListR.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
        simpl.
        unfold listW3.
        rewrite(coseq_eq(act ("p" & [("l1", I, "p" & [("l1", I, W1)])]))).
        unfold coseq_id.
        simpl.
        constructor.
        specialize(CoInSplit1 ("p", rcv)
        (Delay (cocons ("p", rcv) (act ("p" & [("l1", I, W1)]))))
        ("p", rcv) (act ("p" & [("l1", I, W1)]))
        ); intro Ha.
        apply Ha.
        simpl. easy. easy.

        specialize(CoInSplit2 ("p", snd)
        (Delay (cocons ("p", rcv) (act ("p" & [("l1", I, W1)]))))
        ("p", rcv) (act ("p" & [("l1", I, W1)]))
        ); intro Ha.
        constructor.
        apply Ha.
        simpl. easy. easy.

        rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))).
        unfold coseq_id. simpl.
        specialize(CoInSplit2 ("p", snd)
        (Delay (cocons ("p", rcv) (act W1)))
        ("p", rcv) (act W1)
        ); intro Ha'.
        apply Ha'.
        simpl. easy. easy.

        rewrite(coseq_eq (act W1)).
        unfold coseq_id.
        simpl.
        specialize(CoInSplit2 ("p", snd)
        (Delay (cocons ("p", rcv) (act ("p" ! [("l3", I, W1)]))))
        ("p", rcv) (act ("p" ! [("l3", I, W1)]))
        ); intro Ha''.
        apply Ha''.
        simpl. easy. easy.
        rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
        unfold coseq_id. simpl.

        specialize(CoInSplit1 ("p", snd)
        (Delay ( cocons ("p", snd) (act W1)))
        ("p", snd) (act W1)
        ); intro Ha'''.
        apply Ha'''.
        simpl. easy. easy.
        constructor.

        pfold.
        rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])))).
        unfold coseq_id.
        simpl. constructor.
        simpl. right. left. easy.
        unfold upaco2. left.
        apply W3EqList2.

        pfold.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
        unfold coseq_id.
        simpl. constructor.
        simpl. left. easy.
        unfold upaco2. left.
        apply W1EqList2.

        unfold listW3.
        rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))).
        unfold coseq_id.
        simpl.
        constructor.
        specialize(CoInSplit2 ("p", rcv)
        (Delay (cocons ("p", snd) (act W3) ))
        ("p", snd) (act W3)
        ); intro Ha.
        apply Ha.
        simpl. easy. easy.
        rewrite(coseq_eq(act W3)).
        unfold coseq_id. simpl.
        specialize(CoInSplit1 ("p", rcv)
        (Delay (cocons ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
        ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
        ); intro Ha'.
        apply Ha'.
        simpl. easy. easy.
        specialize(CoInSplit1 ("p", snd)
        (Delay (cocons ("p", snd) (act W3)))
        ("p", snd) (act W3)
        ); intro Ha''.
        constructor.
        apply Ha''.
        simpl. easy. easy.
        constructor.

        unfold listW3.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
        simpl.
        constructor.
        rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))).
        unfold coseq_id.
        simpl.
        specialize(CoInSplit1 ("p", rcv)
        (Delay (cocons ("p", rcv) (act W1)))
        ("p", rcv) (act W1)
        ); intro Ha.
        apply Ha.
        simpl. easy. easy.
        rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))).
        unfold coseq_id. simpl.
        specialize(CoInSplit2 ("p", snd)
        (Delay (cocons ("p", rcv) (act W1)))
        ("p", rcv) (act W1)
        ); intro Ha.
        constructor.
        apply Ha.
        simpl. easy. easy.
        rewrite(coseq_eq (act W1)).
        unfold coseq_id.
        simpl.
        specialize(CoInSplit2 ("p", snd)
        (Delay (cocons ("p", rcv) (act ("p" ! [("l3", I, W1)]))))
        ("p", rcv) (act ("p" ! [("l3", I, W1)]))
        ); intro Ha'.
        apply Ha'.
        simpl. easy. easy.
        rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))).
        unfold coseq_id. simpl.
        specialize(CoInSplit1 ("p", snd)
        (Delay (cocons ("p", snd) (act W1)))
        ("p", snd) (act W1)
        ); intro Ha'''.
        apply Ha'''.
        simpl. easy. easy.
        constructor.

apply action_eq1.
apply action_eq2.
apply action_eq3.
apply action_eq4.
apply action_eq5.
apply action_eq6.
apply action_eq7.
apply action_eq8.

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
(*          apply _sref_in. *)
        specialize(_sref_a (upaco2 refinementR r) ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])  
                                                  ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]) "p" "l1" (I) (I) (ap_end) 1); intros HSA.
        simpl in HSA.
        rewrite apend_an in HSA.
        rewrite apend_an in HSA.
        apply HSA with (L := listW3).
        
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
                            listW3
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
                            listW3
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
                            listW3
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
         apply W3EqList.
         
         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         pfold.
         rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])])])])))).
         unfold coseq_id.
         simpl. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply W1EqList3.

         apply W3EqListR.
         unfold listW3.
         rewrite(coseq_eq (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                               (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) 
                               (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))).
         unfold coseq_id.
         simpl.
         constructor.
         
         specialize(CoInSplit1 ("p", rcv)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))
         ); intro Ha.
         apply Ha. simpl. easy. easy.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))
         ); intro Ha.
         constructor.
         apply Ha. simpl. easy. easy.
         (*repeated?*)
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(coseq_eq((act ("p" & [("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))])))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))
         ); intro Ha'.
         apply Ha'.
         simpl. easy. easy.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))
         ); intro Ha''.
         apply Ha''.
         simpl. easy. easy.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))
         ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))
         ); intro Ha'''.
         apply Ha'''.
         simpl. easy. easy.
         apply inW1ns.
         constructor.

         pfold.
         rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])))).
         unfold coseq_id. simpl. constructor.
         simpl. right. left. easy.
         unfold upaco2. left.
         apply W3EqList2.

         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         pfold.
         rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])])])))).
         unfold coseq_id.
         simpl. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply W1EqList3.

         unfold listW3.
         rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))).
         unfold coseq_id.
         simpl.
         constructor.
         specialize(CoInSplit2 ("p", rcv)
         (Delay (cocons ("p", snd) (act W3)))
         ("p", snd) (act W3)
         ); intro Ha. 
         apply Ha. simpl. easy. easy.
         rewrite(coseq_eq(act W3)).
         unfold coseq_id. simpl.
         specialize(CoInSplit1 ("p", rcv)
         (Delay (cocons ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
         ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
         ); intro Ha'.
         apply Ha'. simpl. easy. easy.
         constructor.
         specialize(CoInSplit1 ("p", snd)
         (Delay(cocons ("p", snd) (act W3)))
         ("p", snd) (act W3)
         ); intro Ha''.
         apply Ha''. simpl. easy. easy.
         constructor.

         unfold listW3.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(coseq_eq((act ("p" & [("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))])))).
         unfold coseq_id.
         simpl.
         constructor.
         
         specialize(CoInSplit1 ("p", rcv)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))
         ); intro Ha.
         apply Ha. simpl. easy. easy.

         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))
         ); intro Ha'.
         constructor.
         apply Ha'.
         simpl. easy. easy.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))
         ); intro Ha''.
         apply Ha''.
         simpl. easy. easy.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv)
                        (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))
         ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))
         ); intro Ha'''.
         apply Ha'''.
         simpl. easy. easy.
         apply inW1ns.
         constructor.

         pfold.
         rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))).
         unfold coseq_id.
         simpl. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])) )).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. right. left. easy.
         unfold upaco2. left.
         apply W3EqList2.

         rewrite(siso_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])])))).
         unfold coseq_id.
         simpl. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])) ).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply W1EqList3.

         unfold listW3.
         rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])]))).
         unfold coseq_id. simpl.
         constructor.
         specialize(CoInSplit2 ("p", rcv)
         (Delay (cocons ("p", snd) (act ("p" ! [("l3", I, W3)]))))
         ("p", snd) (act ("p" ! [("l3", I, W3)]))
         ); intro Ha.
         apply Ha. simpl. easy. easy.
         rewrite(coseq_eq(act ("p" ! [("l3", I, W3)]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", rcv)
         (Delay (cocons ("p", snd) (act W3) ))
         ("p", snd) (act W3) 
         ); intro Ha'.
         apply Ha'. simpl. easy. easy.
         rewrite(coseq_eq(act W3)). 
         unfold coseq_id. simpl.
         specialize(CoInSplit1 ("p", rcv)
         (Delay (cocons ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))))
         ("p", rcv) (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))
         ); intro Ha''.
         apply Ha''. simpl. easy. easy.
         specialize(CoInSplit1 ("p", snd)
         (Delay (cocons ("p", snd) (act ("p" ! [("l3", I, W3)]))))
         ("p", snd) (act ("p" ! [("l3", I, W3)]))
         ); intro Ha'''.
         constructor.
         apply Ha'''. simpl. easy. easy.
         constructor.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))]))).
         unfold coseq_id. simpl.
         constructor.
         specialize(CoInSplit1 ("p", rcv)
         (Delay (cocons ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))
         ); intro Ha.
         apply Ha. simpl. easy. easy.

         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv) (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))))
         ("p", rcv) (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))
         ); intro Ha.
         constructor.
         apply Ha.
         simpl. easy. easy.
         rewrite(coseq_eq(act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]))).
         unfold coseq_id. simpl.
         specialize(CoInSplit2 ("p", snd)
         (Delay (cocons ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))
         ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))
         ); intro Ha'.
         apply Ha'. simpl. easy. easy.
         apply inW1ns.
         constructor.

apply action_eq5.
apply action_eq9.
apply action_eq7.
apply action_eq10.
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

       exists W3.
       split.
(*        symmetry. *)
       pcofix CIH.
       pfold.
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
       right.
       rewrite (siso_eq W3) in CIH.
       simpl in CIH.
       easy.

       exists W1.
       split.
(*        symmetry. *)
       pcofix CIH.
       pfold.
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
       right.
       rewrite (siso_eq W1) in CIH.
       simpl in CIH.
       easy.

       specialize(W1W3UnfVar4R 0); intros.
       rewrite(siso_eq(merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 0)) in H.
       simpl in H.
       rewrite(siso_eq W1).
       simpl.
       apply H.
       constructor.
Qed.
