Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso 
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

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

Lemma w3singleton: singleton W3.
Proof. pcofix CIH.
       pfold. 
       rewrite(st_eq W3). simpl.
       constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.

(* Definition W4_gen (cont: st): st :=
  st_receive "p" [("l1",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,(cont))])])])].

CoFixpoint W4 := W4_gen W4.

Lemma W4eq: W4 = W4_gen W4.
Proof. setoid_rewrite(st_eq W4) at 1. simpl.
       unfold W4_gen. easy.
Qed.

Lemma W4eq2: W4_gen W4 = st_receive "p" [("l1",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,st_send "p" [("l3",sint,(W4))])])])].
Proof. easy. Qed.

Let EqW4 := (W4eq, W4eq2). *)

CoFixpoint W1: st := st_receive "p" [("l1",sint,st_send "p" [("l3",sint,W1)])].

Lemma w1singleton: singleton W1.
Proof. pcofix CIH. pfold. 
       rewrite(st_eq W1). simpl.
       constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.


Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS: forall n : nat, ev n -> ev (S (S n)).

Definition listW3 := [("p",rcv); ("p",snd)].

Lemma W3EqList: coseqInLC (act W3) listW3.
Proof. pcofix CIH.
       pfold.
(*        rewrite 2! EqW4. *)
       simpl.
       rewrite(st_eq W3).
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

Lemma W3EqList2: forall r, paco2 coseqInL r (act W3) listW3.
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(st_eq W3).
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

Lemma W1EqList: coseqInLC (act W1) listW3.
Proof. pcofix CIH.
       pfold.
       rewrite(st_eq W1).
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

Lemma W1EqList2: forall r, paco2 coseqInL r (act W1) listW3.
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(st_eq W1).
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

Lemma W1EqList3: forall n r, paco2 coseqInL r (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)) listW3.
Proof. pcofix CIH.
       intros n.
       induction n; intros.
       simpl. apply W1EqList2.
       simpl.
       rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
       simpl. 
       rewrite(coseq_eq((act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])))).
       unfold coseq_id. simpl.
       pfold. constructor.
       simpl. left. easy.
       unfold upaco2. left.
       apply IHn.
Qed.

Lemma W3EqListR: coseqInR listW3 (act W3).
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

Lemma W1EqListR: coseqInR listW3 (act W1).
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

Lemma inW1ns: forall n l s, coseqIn ("p", snd) (act (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)).
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
       rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" l s) (merge_bp_contn "p" (bp_receivea "p" l s) W1 n)))).
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
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W)]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "p" bp_end ("p" & [("l1", I, "p" ! [("l3", I, W)])]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W)]))).
       simpl.
       easy.

       simpl in *.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" & [("l1", I, "p" ! [("l3", I, W)])]))).
       simpl.
       rewrite IHn.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) ("p" ! [("l3", I, W)]))).
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
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W)]))).
       simpl. easy.
       simpl in *.
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) n)))).
       simpl.
       rewrite IHn.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W)]))).
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
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) n))).
       simpl.
       rewrite IHn.
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" & [("l1", I, "p" ! [("l3", I, W)])]) n))).
       simpl. easy.
Qed.

Lemma action_eq1: coseqInLC (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])) listW3.
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

Lemma action_eq2: coseqInLC (act W1) listW3.
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

Lemma action_eq3: coseqInR listW3 (act ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])).
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

Lemma action_eq4: coseqInR listW3 (act W1).
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

Lemma action_eq5: coseqInLC (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])) listW3.
Proof. unfold listW3.
       pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       apply action_eq1.
Qed.

Lemma action_eq6: coseqInLC (act ("p" ! [("l3", I, W1)])) listW3.
Proof. unfold listW3.
       pfold.
       rewrite(coseq_eq(act ("p" ! [("l3", I, W1)]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       apply action_eq2.
Qed.

Lemma action_eq7: coseqInR listW3 (act ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])).
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

Lemma action_eq8: coseqInR listW3 (act ("p" ! [("l3", I, W1)])).
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

Lemma action_eq9: forall n, coseqInLC (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])) listW3.
Proof. intro n.
       induction n; intros.
       - simpl. pfold. 
         rewrite(coseq_eq(act ("p" & [("l1", I, W1)]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left. apply action_eq2.
       - simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [("l1", I, "p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])]))).
         unfold coseq_id. simpl. unfold listW3.
         pfold. constructor. simpl. left. easy.
         left. exact IHn.
Qed.

Lemma action_eq10: forall n, coseqInR listW3 (act ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)])).
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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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

         rewrite(st_eq (W1)).
         simpl.
         pfold.
         rewrite(st_eq W3).
         simpl.


         specialize(ref_a (upaco2 refinementR r) ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])  
                                                   ("p" ! [("l3", I, W1)]) "p" "l1" (I) (I) (ap_end) 1); intros HSA.
         simpl in HSA.
         rewrite apend_an in HSA.
         rewrite apend_an in HSA.
         apply HSA.
         
(*          apply _sref_in. *)
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         
         
(*          apply _sref_out. *)

         specialize(ref_b (upaco2 refinementR r) ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])  
                                                   (W1) "p" "l3" (I) (I) (bp_end) 1); intros HSB.
         simpl in HSB.
         rewrite bpend_an in HSB.
         rewrite bpend_an in HSB.
         apply HSB.
         
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(ref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
(*                             listW3 *)
                   ); intro Hb.
         simpl in Hb.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(st_eq W1).
         simpl.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(ref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
(*                             listW3 *)
                   ); intro Hc.
        simpl in Hc.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]))))) in Hc.
        simpl in Hc.
        rewrite(st_eq (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
        simpl.
        rewrite(st_eq W1).
        simpl.
        apply Hc.
        apply srefl.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
        simpl.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
        simpl.
        unfold upaco2.
        right.
        specialize(CIH 2).
        simpl in CIH.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))) in CIH.
        simpl in CIH.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)) in CIH.
        simpl in CIH.
        apply CIH.
        constructor.
        constructor.
        exists listW3.
        split.
        apply W3EqList.
        split.

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
        split.

        apply W3EqListR.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
        simpl.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
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
        exists listW3.
        split.

        pfold.
        rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])))).
        unfold coseq_id.
        simpl. constructor.
        simpl. right. left. easy.
        unfold upaco2. left.
        apply W3EqList2.
        split.

        pfold.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
        unfold coseq_id.
        simpl. constructor.
        simpl. left. easy.
        unfold upaco2. left.
        apply W1EqList2.
        split.

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
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
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
        exists listW3.
        split.

apply action_eq1.
split.
apply action_eq2.
split.
apply action_eq3.
apply action_eq4.
exists listW3.
split.
apply action_eq5.
split.
apply action_eq6.
split.
apply action_eq7.
apply action_eq8.

        rename CIH into Hn.
        simpl. simpl in Hn.

        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
        simpl.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
        simpl.

        pfold.
         rewrite(st_eq W3).
         simpl.
(*          apply _sref_in. *)
        specialize(ref_a (upaco2 refinementR r) ("p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, W3)])])])  
                                                  ("p" & [("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)]) "p" "l1" (I) (I) (ap_end) 1); intros HSA.
        simpl in HSA.
        rewrite apend_an in HSA.
        rewrite apend_an in HSA.
        apply HSA.
        
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(st_eq W1).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
(*                             listW3 *)
                   ); intro Hb.
         simpl in Hb.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))))
         in Hb.
         simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))) in Hb.
         simpl in Hb.
         rewrite helper3 in Hb.

         apply Hb.
         apply srefl.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.

         specialize(ref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
(*                             listW3 *)
                   ); intro Hc.
         simpl in Hc.
         rewrite(st_eq W1).
         simpl.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
             (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))))) in Hc.
         simpl in Hc.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))) in Hc.
         simpl in Hc.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         rewrite helper3 in Hc.
         apply Hc.
         apply srefl.

         specialize(ref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+4)
(*                             listW3 *)
                   ); intro Hd.
         simpl in Hd.
         unfold upaco2.
         left.
         pfold.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
             (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                   (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))))))) in Hd.
         simpl in Hd.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                  (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))))) in Hd.
         simpl in Hd.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                 (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n)))) in Hd.
         simpl in Hd.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W1)]) n))) in Hd.
         simpl in Hd.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
         simpl.
         rewrite helper3 in Hd.
         rewrite(st_eq W1).
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
         exists listW3.
         split.
         apply W3EqList.
         split.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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
         split.

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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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
         exists listW3.
         split.

         pfold.
         rewrite(coseq_eq((act ("p" ! [("l3", I, W3)])))).
         unfold coseq_id. simpl. constructor.
         simpl. right. left. easy.
         unfold upaco2. left.
         apply W3EqList2.
         split.

         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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
         split.

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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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
         exists listW3.
         split.

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
         split.

         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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
         split.

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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n)))).
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
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 n))).
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
         exists listW3.
         split.
apply action_eq5.
split.
apply action_eq9.
split.
apply action_eq7.
apply action_eq10.
Qed.

Lemma st2A: subtypeA TB TB'.
Proof. unfold subtypeA.
       exists (mk_siso W3 (w3singleton)).
       split.
       pcofix CIH.
       pfold. simpl.
       rewrite (st_eq W3).
       rewrite (st_eq TB).
       simpl.
       apply st2siso_rcvA. simpl.
       left. pfold.
       apply st2siso_sndA. simpl.
       left. pfold.
       apply st2siso_sndA. simpl.
       left. pfold.
       apply st2siso_sndA. simpl.
       right. exact CIH.

       exists (mk_siso W1 (w1singleton)).
       split.
       pcofix CIH.
       pfold. simpl.
       rewrite (st_eq W1).
       rewrite (st_eq TB').
       simpl.
       apply st2siso_rcvA. simpl.
       left. pfold.
       apply st2siso_sndA. simpl.
       right. exact CIH.

       specialize(W1W3UnfVar4R 0); intros.
       rewrite(st_eq(merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 0)) in H.
       simpl in H. simpl.
       rewrite(st_eq W1).
       simpl.
       apply H.
       constructor.
Qed.

Lemma st2: subtype TB TB'.
Proof. unfold subtype.
       intro U.
       split.
       pcofix CIH.
       pfold.
       rewrite (st_eq TB).
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
       rewrite (st_eq TS).
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
       setoid_rewrite (st_eq TS) at 6 in Hb.
       simpl in Hb.
       pfold.
       apply Hb.
       left. easy.
       unfold upaco2.
       right.
       setoid_rewrite (st_eq TS) at 2.
       simpl. easy.
       easy.

       setoid_rewrite (st_eq TB) in CIH.
       simpl in CIH.
       unfold upaco2.
       right.
       apply CIH.

       intro V'.
       split.

       pfold.
       rewrite (st_eq TB').
       simpl.
       specialize (st2si_rcv (upaco2 st2si bot2) "l1" sint
       (st_send "p" [("l3", sint, TB')])
       V'
       ([("l1", sint, st_send "p" [("l3", sint, TB')]); ("l2", sint, TS)])
       "p"
       ); intro H.
       apply H.
       simpl. left. easy.

       unfold upaco2.
       left.
       pcofix CIH.
       pfold.
       specialize (st2si_rcv (upaco2 st2si r) "l1" sint
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
       pcofix CIH.
       pfold. simpl.
       rewrite (st_eq W3).
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
       rewrite (st_eq W3) in CIH.
       simpl in CIH.
       easy.

       exists (mk_siso W1 (w1singleton)).
       split.

       pcofix CIH.
       pfold. simpl.
       rewrite (st_eq W1).
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
       rewrite (st_eq W1) in CIH.
       simpl in CIH.
       easy.

       specialize(W1W3UnfVar4R 0); intros.
       rewrite(st_eq(merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 0)) in H.
       simpl in H. simpl.
       rewrite(st_eq W1).
       simpl.
       apply H.
       constructor.
Qed.
