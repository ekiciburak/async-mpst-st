Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
Require Import Lia.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition lTS: local :=
  lt_mu (lt_send "p" [("l3",sint,(lt_var 0))]).

Definition lTB: local :=
  lt_mu 
  (lt_receive "p"
  [
   ("l1",sint,lt_send "p" [("l3",sint,lt_send "p" [("l3",sint,lt_send "p" [("l3",sint,(lt_var 0))])])]);
   ("l2",sint,lTS)
  ]).

Definition lTB': local :=
  lt_mu
  (lt_receive "p"
  [
   ("l1",sint,lt_send "p" [("l3",sint,(lt_var 0))]);
   ("l2",sint,lTS)
  ]).

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
         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I, W)]) (S n))
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

Lemma WBRef: forall n,
  ev n ->
  refinement (W3) (merge_bp_contn "p" (bp_receivea "p" "l1" sint) W1 n).
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
         apply srefl.
         unfold upaco2.
         left.
         pfold.
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
        split.
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
        constructor. easy.
        exists listW3.
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
        constructor. split.

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
        constructor. easy.
        exists listW3.
        exists listW3.
        split.

apply action_eq1.
split.
apply action_eq2.
split.
apply action_eq3.
split.
apply action_eq4. easy.
exists listW3.
exists listW3.
split.
apply action_eq5.
split.
apply action_eq6.
split.
apply action_eq7.
split.
apply action_eq8. easy.

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
                           (S (S n))

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
                            (S(S(S n)))
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
                            (S(S(S(S n))))
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
         specialize(Hn (S(S(S(S n))))).
         simpl in Hn.
         apply Hn.
         constructor.
         constructor.
         easy.
         exists listW3.
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
         split.
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
         constructor. easy.
         exists listW3.
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
         constructor. split.

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
         constructor. easy.
         exists listW3.
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
         constructor. split.

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
         constructor. easy.
         exists listW3.
         exists listW3.
         split.
apply action_eq5.
split.
apply action_eq9.
split.
apply action_eq7.
split.
apply action_eq10. easy.
Qed.

CoFixpoint W2C: st := st_send "p" [("l3",sint,W2C)].
Definition W2: st := st_receive "p" [("l2",sint,W2C)].

Definition listW2C := [("p", snd)].

Lemma w2singleton: singleton W2.
Proof. pfold. 
       rewrite(st_eq W2). simpl.
       rewrite(st_eq W2C). simpl.
       constructor.
       left. pfold.
       constructor. left.
       pcofix CIH. pfold.
       rewrite(st_eq W2C). simpl.
       constructor.
       right. exact CIH.
Qed.

Lemma refw2_refl: refinement W2 W2.
Proof. rewrite(st_eq W2). simpl.
       pfold.
       specialize(ref_a (upaco2 refinementR bot2) W2C W2C "p" "l2" (I) (I) (ap_end) 1); intro Ha.
       simpl in Ha.
       rewrite !apend_an in Ha.
       apply Ha. clear Ha.
       constructor.
       left.
       pcofix CIH. pfold.
       rewrite(st_eq W2C). simpl.
       specialize(ref_b (upaco2 refinementR r) W2C W2C "p" "l3" (I) (I) (bp_end) 1); intro Hb.
       simpl in Hb.
       rewrite !bpend_an in Hb.
       apply Hb. clear Ha Hb.
       constructor.
       right. exact CIH.
       clear CIH.

       exists listW2C.
       exists listW2C.
       split. unfold listW2C.
       pcofix CIH.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listW2C.
       pcofix CIH.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listW2C.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       
       split. unfold listW2C.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       easy.

       exists listW2C.
       exists listW2C.
       split. unfold listW2C.
       pcofix CIH.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listW2C.
       pcofix CIH.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listW2C.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       
       split. unfold listW2C.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma dp_comm: forall n d w,
 (merge_dp_cont d (merge_dp_contn d w n)) = 
 (merge_dp_contn d (merge_dp_cont d w) n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma dp_Scomm: forall n d w,
 (merge_dp_cont d (merge_dp_contn d w n)) = 
 (merge_dp_contn d w) (S n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.


Definition pi1: Dp :=
  dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)).

Definition pi3: Dp :=
  dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) 
  (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))).

Lemma act_eqp31_1:
exists L1 L2 : list (participant * dir),
  coseqInLC (act W2C) L1 /\
  coseqInLC (act W2C) L2 /\
  coseqInR L1 (act W2C) /\
  coseqInR L2 (act W2C) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists [("p",snd)].
       exists [("p",snd)].
       split.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqp31_2:
exists L1 L2 : list (participant * dir),
  coseqInLC (act W2) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C)) L2 /\
  coseqInR L1 (act W2) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C)) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split. pfold.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. 
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       unfold listW3.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       
       split. 
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C))). unfold coseq_id. simpl.
       constructor. 
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.    
       easy.
Qed.

Lemma act_eqp31_3:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) W2)) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C)) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_send "p" "l3" (I)) W2)) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C)) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       left. pfold.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. 
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W2)). simpl. easy. easy.
       rewrite(coseq_eq (act W2)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2)). simpl. easy. easy.
       constructor.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqp31_4:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2)) L1 /\
  coseqInLC (act W2) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2)) /\
  coseqInR L2 (act W2) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split. pfold.
       rewrite(coseq_eq (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2)) ). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold. rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pcofix CIH. 
       pfold. rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2))). unfold coseq_id. simpl.
       unfold listW3.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W2)). simpl. easy. easy.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). simpl. easy. easy.
       constructor.
       
       split.
       unfold listW3. rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqp31_5:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2)) L1 /\
  coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) W2)) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2)) /\
  coseqInR L2 (act (merge_dp_cont (dp_send "p" "l3" (I)) W2)) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold. rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold. rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2))).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2)) ). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W2)). simpl. easy. easy.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       rewrite(coseq_eq (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2))). simpl. easy. easy.
       constructor.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act W2)). simpl. easy. easy.
       rewrite(coseq_eq(act W2)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
       constructor.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) W2))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2)). simpl. easy. easy.
       constructor.
       easy.
Qed.


Lemma actp31_B1H1: forall k n, coseqInLC (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)) listW3.
Proof. intro k.
       induction k; intros.
       - simpl. induction n; intros.
         + simpl. 
           rewrite(coseq_eq (act W2)). unfold coseq_id. simpl.
           pfold. constructor. simpl. left. easy.
           left. pcofix CIH.
           pfold. rewrite(coseq_eq(act W2C)). unfold coseq_id. simpl.
           constructor. simpl. right. left. easy.
           right. exact CIH.
         + simpl.
           pfold. rewrite(coseq_eq(act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))). unfold coseq_id. simpl.
           constructor. simpl. left. easy.
           left. pfold.
           rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))). unfold coseq_id. simpl.
           constructor. simpl. right. left. easy.
           left. pfold.
           rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
           unfold coseq_id. simpl. constructor. simpl. right. left. easy.
           left. pfold.
           rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). unfold coseq_id. simpl.
           constructor. simpl. right. left. easy.
           left. unfold coseqInLC in IHn. exact IHn.
        - simpl. unfold pi1 at 1.
          rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
          unfold coseq_id. simpl.
          pfold.
          constructor. simpl. left. easy.
          left. pfold. 
          rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
          unfold coseq_id. simpl.
          constructor. simpl. right. left. easy.
          left. specialize(IHk n). unfold coseqInLC in IHk. exact IHk.
Qed.

Lemma actp31_B1H2: forall k n,
coseqInLC
  (act
     (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
        (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))) listW3.
Proof. intros.
       rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl. pfold.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       specialize(actp31_B1H1 k n); intro Hk.
       unfold coseqInLC in Hk. exact Hk.
Qed.

Lemma actp31_B1H3: forall k n,
coseqInR listW3 (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)).
Proof. intro k.
       induction k; intros.
       - simpl. induction n; intros.
         + simpl. 
           rewrite(coseq_eq (act W2)). unfold coseq_id, listW3. simpl.
           constructor.
           apply CoInSplit1 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
           constructor.
           apply CoInSplit2 with (y := ("p", rcv)) (ys := (act W2C)). simpl. easy. easy.
           rewrite(coseq_eq (act W2C)). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := ("p", snd)) (ys := (act W2C)). simpl. easy. easy.
           constructor.
         + simpl. unfold pi3 at 1.
           inversion IHn. subst.
           rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                                (merge_dp_contn pi3 W2 n)))).
           unfold coseq_id. simpl.
           constructor.
           apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))
                                                          (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
           constructor.
           apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
           simpl. easy. easy.
           rewrite(coseq_eq (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
           constructor.
        - simpl. unfold pi1 at 1.
          rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
          unfold coseq_id, listW3. simpl.
          constructor.
          apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
          simpl. easy. easy.
          constructor.
          apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
          simpl. easy. easy.
          rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
          unfold coseq_id. simpl.
          apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))).
          simpl. easy. easy.
          constructor.
Qed.

Lemma actp31_B1H4: forall k n,
coseqInR listW3 (act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))).
Proof. intros.
       rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       simpl. easy. easy.
       rewrite(coseq_eq (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))).
       simpl. easy. easy.
       constructor.
Qed.

Lemma actp31_B1: forall n k,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k)) k)) L1 /\
  coseqInLC
    (act
       (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
          (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k - 1)) k))) L2 /\
  coseqInR L1 (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k)) k)) /\
  coseqInR L2
    (act
       (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
          (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k - 1)) k))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. intros.
       exists listW3.
       exists listW3.
       split. 
       apply (actp31_B1H1 k (n - S k)).
       split.
       apply (actp31_B1H2 k (n - S k - 1)).
       split.
       apply (actp31_B1H3 k (n - S k)).
       split.
       apply (actp31_B1H4 k (n - S k - 1)).
       easy.
Qed.

Lemma actp31_B2H1: forall k n,
coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))) listW3.
Proof. intros.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left.
       specialize(actp31_B1H1 k n); intros Hk.
       unfold coseqInLC in Hk. exact Hk.
Qed.

Lemma actp31_B2H2: forall k n,
coseqInLC
  (act
     (merge_dp_cont (dp_send "p" "l3" (I))
        (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
           (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))) listW3.
Proof. intros.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))))).
       unfold coseq_id. simpl.
       pfold. constructor.
       simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl.
       left. pfold. constructor. simpl. right. left. easy.
       left.
       specialize(actp31_B1H1 k n); intros Hk.
       unfold coseqInLC in Hk. exact Hk.
Qed.

Lemma actp31_B2H3: forall k n,
coseqInR listW3 (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))).
Proof. intros.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))).
       simpl. easy. easy.
       specialize(actp31_B1H3 k n); intro Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))).
       simpl. easy. easy.
       constructor.
Qed.

Lemma actp31_B2H4: forall k n,
coseqInR listW3
  (act
     (merge_dp_cont (dp_send "p" "l3" (I))
        (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
           (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
Proof. intros.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       simpl. easy. easy.
       rewrite(coseq_eq (act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k))) ).
       simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) k)))).
       simpl. easy. easy.
       constructor.
Qed.

Lemma actp31_B2: forall n k,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k)) k))) L1 /\
  coseqInLC
    (act
       (merge_dp_cont (dp_send "p" "l3" (I))
          (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k - 1)) k)))) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k)) k))) /\
  coseqInR L2
    (act
       (merge_dp_cont (dp_send "p" "l3" (I))
          (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - S k - 1)) k)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. intros.
       exists listW3.
       exists listW3.
       split. 
       apply (actp31_B2H1 k (n - S k)).
       split.
       apply (actp31_B2H2 k (n - S k - 1)).
       split.
       apply (actp31_B2H3 k (n - S k)).
       split.
       apply (actp31_B2H4 k (n - S k - 1)).
       easy.
Qed.

Lemma act_eqpi3B1: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))) L2 /\
  coseqInR L1 (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       unfold pi3 at 1.
       rewrite(coseq_eq(act (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))).
       simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqpi3B2: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act ("p" ! [("l3", I, merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))])) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))) L2 /\
  coseqInR L1 (act ("p" ! [("l3", I, merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))])) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act ("p" ! [("l3", I, merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))]))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. 
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act ("p" ! [("l3", I, merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))]))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))) ).
       simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. 
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqpi3B3: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))) L1 /\
  coseqInLC (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))) /\
  coseqInR L2 (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. exact Hk.
       
       split.
       specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       simpl. easy. easy.
       constructor.
      
       split.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       exact Hk.
       easy.
Qed.

Lemma act_eqpi3B4: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))) L1 /\
  coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))) /\
  coseqInR L2 (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split. 
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl. 
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n))))).
       unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont pi3 (merge_dp_contn pi3 W2 n)))).
       simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma refpi3pi1: forall n, refinement (merge_dp_contn pi3 W2 (S n)) (merge_dp_cont pi1 (merge_dp_contn pi3 W2 n)).
Proof. pcofix CIH.
       intro n.
       induction n; intros.
       - simpl.
         clear CIH.
         pfold. 
         unfold pi3, pi1.
         rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2)).
         rewrite(st_eq  (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) W2)).
         simpl.
         specialize(ref_a (upaco2 refinementR r)
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2)
                          (merge_dp_cont (dp_send "p" "l3" (I)) W2)
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) W2)).
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) W2)).
         simpl. 
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2)
                          W2
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb. simpl in Hb.
         rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) W2)).
         setoid_rewrite(st_eq W2) at 2. simpl.
         rewrite(st_eq W2C). simpl.
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dp_cont (dp_send "p" "l3" (I)) W2)
                          W2C
                          "p" "l3" (I) (I) (bp_receivea "p" "l2" (I)) 1
         ); intro Hb. simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) ("p" ! [("l3", I, W2C)]))) in Hb.
         simpl in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) W2)).
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C)).
         rewrite(st_eq W2C).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          W2
                          W2C
                          "p" "l3" (I) (I) (bp_receivea "p" "l2" (I)) 1
         ); intro Hb. simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) ("p" ! [("l3", I, W2C)]))) in Hb.
         simpl in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq W2). simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) W2C)).
         simpl.
         specialize(ref_a (upaco2 refinementR r)
                          W2C
                          W2C
                          "p" "l2" (I) (I) (ap_end) 1
         ); intro Ha. simpl in Ha.
         rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.

         left. pcofix CIH. pfold.
         rewrite(st_eq W2C). simpl.
         specialize(ref_b (upaco2 refinementR r)
                          W2C
                          W2C
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb. simpl in Hb.
         rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         right. exact CIH.
         apply act_eqp31_1.
         apply act_eqp31_1.
         apply act_eqp31_2.
         apply act_eqp31_3.
         apply act_eqp31_4.
         apply act_eqp31_5.
       - simpl in *.
         unfold pi3, pi1.
         pfold. simpl.
         rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
                      (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         specialize(ref_a (upaco2 refinementR r)
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))
                              (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                              (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))
                          (merge_dp_cont (dp_send "p" "l3" (I))
                              (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                              (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))
                      (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))
                              (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                              (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))
                          (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                              (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))
                      (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I))
                      (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         setoid_rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))) at 2.
         simpl.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) 
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          ("p"! [("l3", I, merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                          (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))])
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))
                              (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))
                          "p" "l3" (I) (I) (bp_receivea "p" "l1" (I)) 1
         ); intro Hb.
         simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [("l3", I,  merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))]))) in Hb.
         simpl in Hb. apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))
                      (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))))
                             (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))
                          (merge_dp_cont (dp_send "p" "l3" (I))
                             (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))
                           "p" "l3" (I) (I) (bp_receivea "p" "l1" (I)) 1
         ); intro Hb.
         simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p"! [("l3", I,
                      merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn (dp_mergea "p" "l1" (I) 
                      (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))]))) in Hb.
         simpl in Hb. apply Hb; clear Hb.
         constructor.
         left.

         unfold pi3, pi1 in IHn.
         rewrite(st_eq  (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n)))).
         simpl.
         rewrite(st_eq (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I)))
           (merge_dp_contn (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) W2 n))) in IHn.
         simpl in IHn.
         apply IHn.
         fold pi1.
         fold pi3.
         apply act_eqpi3B1.
         fold pi1.
         fold pi3.
         apply act_eqpi3B2.
         fold pi3.
         fold pi1.
         apply act_eqpi3B3.
         fold pi3.
         fold pi1.
         apply act_eqpi3B4.
Qed.

Lemma refpi3pi1A: forall (n k: nat), (n - k >= 1) -> refinement (merge_dp_contn pi3 W2 (n-k)) (merge_dp_cont pi1 (merge_dp_contn pi3 W2 (n-k-1))).
Proof. intros.
       specialize(refpi3pi1 (n - k - 1)); intro Ha.
       simpl in Ha.
       rewrite dp_Scomm in Ha. simpl.
       assert(S (n - k - 1) = (n - k)).
       { lia. }
       rewrite H0 in Ha.
       apply Ha.
Qed.

Lemma refpi3pi1A2: forall n, n > 0 -> refinement (merge_dp_contn pi3 W2 n) (merge_dp_cont pi1 (merge_dp_contn pi3 W2 (n-1))).
Proof. intros. 
       specialize(refpi3pi1 (n - 1)); intro Ha.
       assert(S (n - 1) = n).
       { induction n; intros.
         - easy.
         - lia.
       }
       rewrite H0 in Ha.
       apply Ha.
Qed.



Lemma refpi3pi1B: forall k n, (n - k >= 1) -> refinement (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n-k)) k) 
                                                         (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n-k-1)) (S k)).
Proof. intro k.
       induction k; intros.
       - simpl.
         specialize(refpi3pi1 (n-1)); intro Ha.
         assert(S (n - 1) = n).
         { lia. }
         rewrite H0 in Ha.
         assert((n - 0) = n).
         { lia. }
         rewrite H1. apply Ha.
       - simpl. unfold pi1 at 1.
         unfold pi1 at 3.
         pfold.
         rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k))) k))).
         simpl.
         rewrite(st_eq(merge_dp_cont pi1 (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k) - 1)) k)))).
         simpl.
         specialize(ref_a (upaco2 refinementR bot2)
                          (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k))) k))
                          (merge_dp_cont (dp_send "p" "l3" (I))
                            (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k) - 1)) k)))
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.
         
         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k))) k))).
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k) - 1)) k)))).
         simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k))) k)
                          (merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - (S k) - 1)) k))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         left.
         
         specialize(IHk (n - 1)).
         simpl in IHk.
         unfold refinement in IHk.
         assert ((n - 1 - k - 1) = (n - (S k) - 1)).
         { lia. }
         rewrite H0 in IHk.
         assert((n - 1 - k) = (n - (S k)) ).
         { lia. }
         rewrite H1 in IHk.
         apply IHk. simpl. easy.
         apply actp31_B1.
         apply actp31_B2.
Qed.

Lemma act_eqw21: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_contn pi3 W2 n)) L1 /\
  coseqInLC (act (merge_dp_contn pi3 W2 n)) L2 /\
  coseqInR L1 (act (merge_dp_contn pi3 W2 n)) /\
  coseqInR L2 (act (merge_dp_contn pi3 W2 n)) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       exact Hk.
       
       split.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       exact Hk.
       easy.
Qed.

Lemma act_eqw22: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))) L1 /\
  coseqInLC (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))) /\
  coseqInR L2 (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. pfold. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. pfold. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       constructor.

       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqw23: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))) L1 /\
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))) /\
  coseqInR L2 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqw24: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))) L1 /\
  coseqInLC (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))) L2 /\
  coseqInR L1 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))) /\
  coseqInR L2 (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listW3.
       exists listW3.
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.

       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       constructor.

       split.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n)))).
       unfold coseq_id, listW3. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi3 W2 n))). simpl. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n)))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma ref_w2n: forall n, refinement (merge_dp_contn pi3 W2 n) (merge_dp_contn pi3 W2 n).
Proof. intro n.
       induction n; intros.
       - simpl. apply refw2_refl.
       - simpl. 
         unfold pi3 at 1. unfold pi3 at 2.
         rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))))) (merge_dp_contn pi3 W2 n))).
         simpl.
         pfold.
         specialize(ref_a (upaco2 refinementR bot2)
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.
         
         left. pfold.
         rewrite(st_eq (merge_dp_cont (dp_merge "p" "l3" (I) (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I)))) (merge_dp_contn pi3 W2 n))).
         simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))
                          (merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         
         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_merge "p" "l3" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi3 W2 n))). simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))
                          (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         
         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi3 W2 n))). simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dp_contn pi3 W2 n)
                          (merge_dp_contn pi3 W2 n)
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         left. unfold refinement in IHn. exact IHn.
         apply act_eqw21.
         apply act_eqw22.
         apply act_eqw23.
         apply act_eqw24.
Qed.

Lemma ref_transpippi3: forall m n, refinement (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m) 
                                              (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m).
Proof. intro m.
       induction m; intros.
       - simpl. apply ref_w2n.
       - simpl. unfold pi1 at 1. unfold pi1 at 2.
         rewrite(st_eq(merge_dp_cont (dp_mergea "p" "l1" (I) (dp_send "p" "l3" (I))) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))).
         simpl.
         pfold.
         specialize(ref_a (upaco2 refinementR bot2)
                    (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))
                    (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))
                    "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor. 
         
         left. pfold.
         rewrite(st_eq(merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))).
         simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                    (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)
                    (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)
                    "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         left.
         specialize(IHm n). unfold refinement in IHm.
         exact IHm.
         exists listW3.
         exists listW3.
         split.
         apply actp31_B1H1.
         split.
         apply actp31_B1H1.
         split.
         apply actp31_B1H3.
         split.
         apply actp31_B1H3.
         easy.

         exists listW3.
         exists listW3.
         split.
         rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)))).
         unfold coseq_id. simpl.
         pfold. constructor. simpl. right. left. easy.
         left.
         specialize(actp31_B1H1 m n); intro Hk.
         unfold coseqInLC in Hk. exact Hk.
         
         split.
         rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)))).
         unfold coseq_id. simpl.
         pfold. constructor. simpl. right. left. easy.
         left.
         specialize(actp31_B1H1 m n); intro Hk.
         unfold coseqInLC in Hk. exact Hk.
         split.
         constructor.
         rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))).
         simpl. easy. easy.
         specialize(actp31_B1H3 m n); intro Hk.
         inversion Hk. subst. easy.
         constructor.
         rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))).
         simpl. easy. easy.
         constructor.
         
         split.
         constructor.
         rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))).
         simpl. easy. easy.
         specialize(actp31_B1H3 m n); intro Hk.
         inversion Hk. subst. easy.
         constructor.
         rewrite(coseq_eq(act (merge_dp_cont (dp_send "p" "l3" (I)) (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dp_contn pi1 (merge_dp_contn pi3 W2 n) m))).
         simpl. easy. easy.
         constructor.
         easy.
Qed.

Lemma ntrans: forall k n u, (n >= (u+k)) ->
                            refinement (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n-u)) u) 
                                       (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n-u-k)) (u+k)).
Proof. intro k.
       induction k; intros.
       - simpl. 
         assert((n - u - 0) = n - u) by lia.
         assert((u + 0) = u) by lia.
         rewrite H0, H1.
         apply ref_transpippi3.
       - specialize(refpi3pi1B (u+k) n); intros Href.
          assert((n - (u + k)) = (n - u - k)).
         { lia. }
         rewrite H0 in Href.
         assert((n - u - k - 1) = (n - u - (S k))).
         { lia. }
         rewrite H1 in Href.
         assert(u + (S k) = u + k + 1).
         { lia. }
         rewrite H2 in H.
         assert(forall n m, m + 1 <= n -> 0 < n - m).
         { lia. }
         apply H3 in H.
         rewrite H0 in H.
         specialize(Href H).
         assert(u + k <= n).
         { lia. }
         specialize(IHk n u H4).
         assert(S (u + k) = (u + (S k))) by lia.
         rewrite H5 in Href.
         specialize(Ref_Trans (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - u)) u)
                              (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - u - k)) (u + k))
                              (merge_dp_contn pi1 (merge_dp_contn pi3 W2 (n - u - (S k))) (u + (S k)))
                              IHk Href); intro HT.
         apply HT.
Qed.

Lemma all_refs:
forall m : nat, refinement (merge_dp_contn pi3 W2 m) (merge_dp_contn pi1 W2 m).
Proof. intros.
       specialize(ntrans m m 0); intro HN.
       assert((m - 0) = m) by lia.
       rewrite H in HN.
       assert((m - m) = 0) by lia.
       rewrite H0 in HN.
       assert((0 + m) = m) by lia.
       rewrite H1 in HN.
       simpl in HN. apply HN. lia.
Qed.

Lemma st2: subtype TB TB'.
Proof. unfold subtype.
       exists(
       [
        ((mk_siso W3 (w3singleton)),(mk_siso W1 (w1singleton)));
        ((mk_siso W2 (w2singleton)),(mk_siso W2 (w2singleton)));
        ((mk_siso W2 (w2singleton)),(mk_siso W2 (w2singleton)))
        ]
       ).
       simpl.
       split. split. 
       pcofix CIH.
       pfold. simpl.
       rewrite (st_eq W3).
       rewrite (st_eq TB).
       simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.
       split.

       pcofix CIH.
       pfold. simpl.
       rewrite (st_eq W1).
       rewrite (st_eq TB').
       simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.

       split.
       rewrite (st_eq W2).
       rewrite (st_eq TB).
       simpl. pfold.
       apply st2siso_rcv. simpl.
       left. pcofix CIH.
       pfold.
       rewrite (st_eq W2C).
       rewrite (st_eq TS). simpl.
       apply st2siso_snd. simpl.
       right. exact CIH.

       split.
       rewrite (st_eq W2).
       rewrite (st_eq TB').
       simpl. pfold.
       apply st2siso_rcv. simpl.
       left. pcofix CIH.
       pfold.
       rewrite (st_eq W2C).
       rewrite (st_eq TS). simpl.
       apply st2siso_snd. simpl.
       right. exact CIH.
       
       split.
       rewrite (st_eq W2).
       rewrite (st_eq TB).
       simpl. pfold.
       apply st2siso_rcv. simpl.
       left. pcofix CIH.
       pfold.
       rewrite (st_eq W2C).
       rewrite (st_eq TS). simpl.
       apply st2siso_snd. simpl.
       right. exact CIH.

       split.
       rewrite (st_eq W2).
       rewrite (st_eq TB').
       simpl. pfold.
       apply st2siso_rcv. simpl.
       left. pcofix CIH.
       pfold.
       rewrite (st_eq W2C).
       rewrite (st_eq TS). simpl.
       apply st2siso_snd. simpl.
       right. exact CIH.

       easy.
       split.
       exists dp_end. exists dp_end. intro n. rewrite !dpend_ann.

       specialize(WBRef 0); intros.
       rewrite(st_eq(merge_bp_contn "p" (bp_receivea "p" "l1" (I)) W1 0)) in H.
       simpl in H. simpl.
       rewrite(st_eq W1).
       simpl.
       apply H.
       constructor.
       
       split.
       exists dp_end. exists dp_end. intro n. rewrite !dpend_ann.
       apply refw2_refl.
       split.
       
       exists pi3.
       exists pi1.
       intro n.
       apply all_refs.

       easy.
Qed.

Lemma lTB2TB: lt2stC lTB TB.
Proof. pcofix CIH. unfold lTB, lTS.
       rewrite(st_eq TB). simpl. pfold.
       apply lt2st_mu. simpl. unfold unscoped.var_zero.
       specialize(lt2st_rcv (upaco2 lt2st r)
       "p" ["l1";"l2"] [(I);(I)]
       [lt_send "p"
         [("l3", I,
           lt_send "p"
             [("l3", I,
               lt_send "p"
                 [("l3", I,
                   lt_mu
                     (lt_receive "p"
                        [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_var 0)])])]);
                         ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var 0)]))]))])])];
        lt_mu (lt_send "p" [("l3", I, lt_var 0)])]
       ["p" ! [("l3", I, "p" ! [("l3", I, "p" ! [("l3", I, TB)])])]; TS]
       ); intro HR. simpl in HR. apply HR; clear HR.
       easy.
       apply Forall_forall.
       intros (l, s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H.
       left. pfold. simpl.
       specialize(lt2st_snd (upaco2 lt2st r)
       "p" ["l3"] [(I)]
       [lt_send "p"
         [("l3", I,
           lt_send "p"
             [("l3", I,
               lt_mu
                 (lt_receive "p"
                    [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_var 0)])])]);
                     ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var 0)]))]))])]]
       ["p" ! [("l3", I, "p" ! [("l3", I, TB)])]]
       ); intro HS. simpl in HS. apply HS; clear HS.
       easy.
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H.
       left. pfold. simpl.
       specialize(lt2st_snd (upaco2 lt2st r)
       "p" ["l3"] [(I)]
       [lt_send "p"
             [("l3", I,
               lt_mu
                 (lt_receive "p"
                    [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_var 0)])])]);
                     ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var 0)]))]))]]
       ["p" ! [("l3", I, TB)]]
       ); intro HS. simpl in HS. apply HS; clear HS.
       easy. 
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H.
       left. pfold. simpl.
       specialize(lt2st_snd (upaco2 lt2st r)
       "p" ["l3"] [(I)]
       [lt_mu
                 (lt_receive "p"
                    [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_var 0)])])]);
                     ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var 0)]))])]
       [TB]
       ); intro HS. simpl in HS. apply HS; clear HS.
       easy. 
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H.
       right. unfold lTB in CIH. simpl. exact CIH.
       easy.
       easy.
       easy.
       destruct H as [H | H].
       simpl in H. inversion H. subst. clear H.
       simpl. clear CIH.
       left. pcofix CIH. pfold.
       apply lt2st_mu. simpl.
       rewrite(st_eq TS). simpl. 
       specialize(lt2st_snd (upaco2 lt2st r)
       "p" ["l3"] [(I)]
       [lt_mu (lt_send "p" [("l3", I, lt_var 0)])]
       [TS]
       ); intro HS. simpl in HS. apply HS; clear HS.
       easy.
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H.
       simpl. right. exact CIH.
       easy.
       easy.
Qed.

Lemma lTB'2TB': lt2stC lTB' TB'.
Proof. pcofix CIH. unfold lTB', lTS.
       rewrite(st_eq TB'). simpl. pfold.
       apply lt2st_mu. simpl. unfold unscoped.var_zero.
       specialize(lt2st_rcv (upaco2 lt2st r)
       "p" ["l1";"l2"] [(I);(I)]
       [lt_send "p"
         [("l3", I,
           lt_mu
             (lt_receive "p"
                [("l1", I, lt_send "p" [("l3", I, lt_var 0)]);
                 ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var 0)]))]))];
       lt_mu (lt_send "p" [("l3", I, lt_var 0)])]
       ["p" ! [("l3", I, TB')]; TS]
       ); intro HR. simpl in HR. apply HR; clear HR.
       easy.
       apply Forall_forall.
       intros (l, s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H. simpl.
       left. pfold.
       specialize(lt2st_snd (upaco2 lt2st r)
       "p" ["l3"] [(I)]
       [lt_mu
         (lt_receive "p"
            [("l1", I, lt_send "p" [("l3", I, lt_var 0)]);
             ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var 0)]))])]
       [TB']
       ); intro HS. simpl in HS. apply HS; clear HS.
       easy. 
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H. simpl.
       right. unfold lTB', lTS in CIH. exact CIH.
       easy.
       destruct H as [H | H]. inversion H.
       subst. clear H. simpl.
       clear CIH. left. pcofix CIH. pfold.
       rewrite(st_eq TS). simpl.
       apply lt2st_mu. simpl.
       specialize(lt2st_snd (upaco2 lt2st r)
       "p" ["l3"] [(I)]
       [lt_mu (lt_send "p" [("l3", I, lt_var 0)])]
       [TS]
       ); intro HS. simpl in HS. apply HS; clear HS.
       easy. 
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H]. inversion H.
       subst. clear H. simpl.
       right. exact CIH.
       easy.
       easy.
Qed.

Lemma lT'_lT: subltype lTB lTB' TB TB' lTB2TB lTB'2TB'.
Proof. unfold subltype.
       exact st2.
Qed.

