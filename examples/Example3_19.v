Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.nondepro ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
Require Import Lia.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition lTS: local :=
  lt_mu (lt_send "p" [("l3",sint,(lt_var 0))]).

Definition T: local :=
  lt_mu 
  (lt_receive "p"
  [
   ("l1",sint,lt_send "p" [("l3",sint,lt_send "p" [("l3",sint,lt_send "p" [("l3",sint,(lt_var 0))])])]);
   ("l2",sint,lTS)
  ]).

Definition T': local :=
  lt_mu
  (lt_receive "p"
  [
   ("l1",sint,lt_send "p" [("l3",sint,(lt_var 0))]);
   ("l2",sint,lTS)
  ]).

CoFixpoint TS: st :=
  st_send "p" [|("l3",sint,TS)|].

CoFixpoint TB: st :=
  st_receive "p"
  [|
   ("l1",sint,st_send "p" [|("l3",sint,st_send "p" [|("l3",sint,st_send "p" [|("l3",sint,TB)|])|])|]);
   ("l2",sint,TS)
  |].

CoFixpoint TB': st :=
  st_receive "p"
  [|
   ("l1",sint,st_send "p" [|("l3",sint,TB')|]);
   ("l2",sint,TS)
  |].

CoFixpoint WB: st := st_receive "p" [|("l1",sint,st_send "p" [|("l3",sint,st_send "p" [|("l3",sint,st_send "p" [|("l3",sint,WB)|])|])|])|].
CoFixpoint WD: st := st_send "p" [|("l3",sint,WD)|].
Definition WA: st := st_receive "p" [|("l2",sint,WD)|].
CoFixpoint WB': st := st_receive "p" [|("l1",sint,st_send "p" [|("l3",sint,WB')|])|].
Definition pi1: Dpf := dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end).
Definition pi3: Dpf :=  dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))).

Definition listWD := [("p", snd)].

Lemma w2singleton: singleton WA.
Proof. pfold. 
       rewrite(st_eq WA). simpl.
       rewrite(st_eq WD). simpl.
       constructor.
       left. pfold.
       constructor. left.
       pcofix CIH. pfold.
       rewrite(st_eq WD). simpl.
       constructor.
       right. exact CIH.
Qed.

Lemma refwa_refl: refinement WA WA.
Proof. rewrite(st_eq WA). simpl.
       pfold.
       specialize(ref_a (upaco2 refinementR bot2) WD WD "p" "l2" (I) (I) (ap_end) 1); intro Ha.
       simpl in Ha.
       rewrite !apend_an in Ha.
       apply Ha. clear Ha.
       constructor.
       left.
       pcofix CIH. pfold.
       rewrite(st_eq WD). simpl.
       specialize(ref_b (upaco2 refinementR r) WD WD "p" "l3" (I) (I) (bp_end) 1); intro Hb.
       simpl in Hb.
       rewrite !bpend_an in Hb.
       apply Hb. clear Ha Hb.
       constructor.
       right. exact CIH.
       clear CIH.

       exists listWD.
       exists listWD.
       split. unfold listWD.
       pcofix CIH.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listWD.
       pcofix CIH.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listWD.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       
       split. unfold listWD.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       easy.

       exists listWD.
       exists listWD.
       split. unfold listWD.
       pcofix CIH.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listWD.
       pcofix CIH.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split. unfold listWD.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       
       split. unfold listWD.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma w3singleton: singleton WB.
Proof. pcofix CIH.
       pfold. 
       rewrite(st_eq WB). simpl.
       constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.


Lemma w1singleton: singleton WB'.
Proof. pcofix CIH. pfold. 
       rewrite(st_eq WB'). simpl.
       constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.


Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS: forall n : nat, ev n -> ev (S (S n)).

Definition listWB := [("p",rcv); ("p",snd)].

Lemma WBEqList: coseqInLC (act WB) listWB.
Proof. pcofix CIH.
       pfold.
(*        rewrite 2! EqW4. *)
       simpl.
       rewrite(st_eq WB).
       simpl.
       rewrite(coseq_eq ((act ("p" & [|("l1", I, "p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, WB)|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right.
       apply CIH.
Qed.

Lemma WBEqList2: forall r, paco2 coseqInL r (act WB) listWB.
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(st_eq WB).
       simpl.
       rewrite(coseq_eq ((act ("p" & [|("l1", I, "p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, WB)|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right.
       apply CIH.
Qed.

Lemma WB'EqList: coseqInLC (act WB') listWB.
Proof. pcofix CIH.
       pfold.
       rewrite(st_eq WB').
       simpl.
       rewrite(coseq_eq ((act ("p" & [|("l1", I, "p" ! [|("l3", I, WB')|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq ((act ("p" ! [|("l3", I, WB')|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right. 
       apply CIH.
Qed.

Lemma WB'EqList2: forall r, paco2 coseqInL r (act WB') listWB.
Proof. intros.
       pcofix CIH.
       pfold.
       rewrite(st_eq WB').
       simpl.
       rewrite(coseq_eq ((act ("p" & [|("l1", I, "p" ! [|("l3", I, WB')|])|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq ((act ("p" ! [|("l3", I, WB')|])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       right. 
       apply CIH.
Qed.

Lemma WB'EqList3: forall n r, paco2 coseqInL r (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)) listWB.
Proof. pcofix CIH.
       intros n.
       induction n; intros.
       simpl. apply WB'EqList2.
       simpl.
       rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
       simpl. 
       rewrite(coseq_eq((act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])))).
       unfold coseq_id. simpl.
       pfold. constructor.
       simpl. left. easy.
       unfold upaco2. left.
       apply IHn.
Qed.

Lemma WBEqListR: coseqInR listWB (act WB).
Proof. rewrite(coseq_eq (act WB)).
       unfold coseq_id. simpl.
       constructor.
       simpl.

       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))))
       ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))
       ); intro Ha.
       apply Ha.
       simpl. easy.
       easy.

       simpl.
       constructor.
       simpl.
       specialize(CoInSplit2 ("p", snd)
       ((cocons ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))))
       ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))
       ); intro Ha.
       simpl in Ha.
       simpl.
       apply Ha.
       easy.
       easy.
       rewrite(coseq_eq((act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])))).
       unfold coseq_id.
       simpl.

       specialize(CoInSplit1 ("p", snd)
       ((cocons ("p", snd) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))))
       ("p", snd) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))
       ); intro Hb.
       simpl in Hb.
       apply Hb.
       easy.
       easy.
       constructor.
Qed.

Lemma WB'EqListR: coseqInR listWB (act WB').
Proof. rewrite(coseq_eq (act WB')).
       unfold coseq_id. simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))))
       ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       specialize(CoInSplit2 ("p", snd)
       ((cocons ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))))
       ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))
       ); intro Ha.
       constructor.
       simpl in Ha.
       apply Ha.
       easy. easy.

       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", snd)
       ((cocons ("p", snd) (act WB')))
       ("p", snd) (act WB')
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma inWB'ns: forall n l s, coseqIn ("p", snd) (act (merge_bp_contn "p" (bp_receivea "p" l s) WB' n)).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(coseq_eq (act WB')).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("p", snd)
       ((cocons ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))))
       ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", snd)
       ((cocons ("p", snd) (act WB')))
       ("p", snd) (act WB')
       ); intro Ha'.
       apply Ha'. simpl. easy. easy.

       simpl.
       rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" l s) (merge_bp_contn "p" (bp_receivea "p" l s) WB' n)))).
       simpl.
       rewrite(coseq_eq(act ("p" & [|(l, s, merge_bp_contn "p" (bp_receivea "p" l s) WB' n)|]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("p", snd)
       ((cocons ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" l s) WB' n))))
       ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" l s) WB' n))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       apply IHn.
Qed.

Lemma helper: forall n W,
  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" & [|("l1", I, "p" ! [|("l3", I, W)|])|])
                 =
  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) (S n)) ("p" ! [|("l3", I, W)|]).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [|("l3", I, W)|]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "p" bp_end ("p" & [|("l1", I, "p" ! [|("l3", I, W)|])|]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "p" bp_end ("p" ! [|("l3", I, W)|]))).
       simpl.
       easy.

       simpl in *.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" & [|("l1", I, "p" ! [|("l3", I, W)|])|]))).
       simpl.
       rewrite IHn.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) ("p" ! [|("l3", I, W)|]))).
       simpl.
       easy.
Qed.

Lemma helper2: forall n W,
         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, W)|]) (S n))
         = 
         ("p" & [|("l1", I, merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" ! [|("l3", I, W)|]))|]).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, W)|]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "p" bp_end ("p" ! [|("l3", I, W)|]))).
       simpl. easy.
       simpl in *.
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, W)|]) n)))).
       simpl.
       rewrite IHn.
       rewrite(st_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [|("l3", I, W)|]))).
       simpl.
       easy.
Qed.

Lemma helper3: forall n W,
("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, W)|]) n)|])|])
=
("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" & [|("l1", I, "p" ! [|("l3", I, W)|])|]) n)|]).
Proof. intro n.
       induction n; intros.
       simpl. easy.
       simpl.
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, W)|]) n))).
       simpl.
       rewrite IHn.
       rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" & [|("l1", I, "p" ! [|("l3", I, W)|])|]) n))).
       simpl. easy.
Qed.

Lemma action_eq1: coseqInLC (act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])) listWB.
Proof. unfold listWB.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act WB)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right.
       exact CIH.
Qed.

Lemma action_eq2: coseqInLC (act WB') listWB.
Proof. pcofix CIH.
       unfold listWB.
       rewrite(coseq_eq(act WB')). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right.
       exact CIH.
Qed.

Lemma action_eq3: coseqInR listWB (act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])).
Proof. constructor.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act ("p" ! [|("l3", I, WB)|]))). simpl. easy. easy.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WB)). simpl.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]) )). simpl. easy. easy.
       rewrite(coseq_eq(act WB)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act ("p" ! [|("l3", I, WB)|]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq4: coseqInR listWB (act WB').
Proof. constructor.
       rewrite(coseq_eq(act WB')). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [|("l3", I, WB')|]))). simpl. easy. easy.
       rewrite(coseq_eq(act WB')). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act ("p" ! [|("l3", I, WB')|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WB')). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq5: coseqInLC (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])) listWB.
Proof. unfold listWB.
       pfold.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       apply action_eq1.
Qed.

Lemma action_eq6: coseqInLC (act ("p" ! [|("l3", I, WB')|])) listWB.
Proof. unfold listWB.
       pfold.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       apply action_eq2.
Qed.

Lemma action_eq7: coseqInR listWB (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])).
Proof. constructor.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act ("p" ! [|("l3", I, WB)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WB)). simpl. easy. easy.
       rewrite(coseq_eq(act WB)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])) ). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq8: coseqInR listWB (act ("p" ! [|("l3", I, WB')|])).
Proof. constructor.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WB')). simpl. easy. easy.
       rewrite(coseq_eq(act WB')). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" ! [|("l3", I, WB')|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WB')). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq9: forall n, coseqInLC (act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])) listWB.
Proof. intro n.
       induction n; intros.
       - simpl. pfold. 
         rewrite(coseq_eq(act ("p" & [|("l1", I, WB')|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left. apply action_eq2.
       - simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|]))).
         unfold coseq_id. simpl. unfold listWB.
         pfold. constructor. simpl. left. easy.
         left. exact IHn.
Qed.

Lemma action_eq10: forall n, coseqInR listWB (act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])).
Proof. intro n.
       induction n; intros.
       - simpl. constructor.
         rewrite(coseq_eq(act ("p" & [|("l1", I, WB')|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WB')). simpl. easy. easy.
         rewrite(coseq_eq(act ("p" & [|("l1", I, WB')|]))). unfold coseq_id. simpl.
         constructor.
         apply CoInSplit2 with (y := ("p", rcv)) (ys := (act WB')). simpl. easy. easy.
         rewrite(coseq_eq(act WB')). unfold coseq_id. simpl. 
         apply CoInSplit2 with (y := ("p", rcv)) (ys := (act ("p" ! [|("l3", I, WB')|]))). simpl. easy. easy.
         rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", snd)) (ys := (act WB')). simpl. easy. easy.
         constructor.
       - simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         constructor.
         rewrite(coseq_eq(act ("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|]))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", rcv)) (ys := (act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))). simpl. easy. easy.
         constructor.
         inversion IHn.
         subst.
         inversion H3. subst.
         rewrite(coseq_eq(act ("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|]))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("p", rcv)) (ys := (act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))). simpl. easy. easy.
         exact H2.
         constructor.
Qed.

Lemma WBRef: forall n,
  ev n ->
  refinement (WB) (merge_bp_contn "p" (bp_receivea "p" "l1" sint) WB' n).
Proof. intros.
       generalize dependent n.
       pcofix CIH.
       intros.
       induction H0; intros.
       simpl.

         rewrite(st_eq (WB')).
         simpl.
         pfold.
         rewrite(st_eq WB).
         simpl.


         specialize(ref_a (upaco2 refinementR r) ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])  
                                                   ("p" ! [|("l3", I, WB')|]) "p" "l1" (I) (I) (ap_end) 1); intros HSA.
         simpl in HSA.
         rewrite apend_an in HSA.
         rewrite apend_an in HSA.
         apply HSA.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(ref_b (upaco2 refinementR r) ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])  
                                                   (WB') "p" "l3" (I) (I) (bp_end) 1); intros HSB.
         simpl in HSB.
         rewrite bpend_an in HSB.
         rewrite bpend_an in HSB.
         apply HSB.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(ref_b (upaco2 refinementR r)
                            ("p" ! [|("l3", I, WB)|])
                            WB'
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                   ); intro Hb.
         simpl in Hb.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|])))) in Hb.
         simpl in Hb.
         rewrite(st_eq WB').
         simpl.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(ref_b (upaco2 refinementR r)
                            WB
                            WB' 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                   ); intro Hc.
        simpl in Hc.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]))))) in Hc.
        simpl in Hc.
        rewrite(st_eq (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|])))
        in Hc. simpl in Hc.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB'))).
        simpl.
        rewrite(st_eq WB').
        simpl.
        apply Hc.
        apply srefl.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')))).
        simpl.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')).
        simpl.
        unfold upaco2.
        right.
        specialize(CIH 2).
        simpl in CIH.
        rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
           (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')))) in CIH.
        simpl in CIH.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')) in CIH.
        simpl in CIH.
        apply CIH.
        constructor.
        constructor.
        exists listWB.
        exists listWB.
        split.
        apply WBEqList.
        split.

        pfold.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB'))))).
        unfold coseq_id. simpl.
        constructor.
        simpl. left. easy.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')))).
        unfold coseq_id, upaco2.
        simpl. left. pfold. constructor.
        simpl. left. easy.
        unfold upaco2. left.
        apply WB'EqList2.
        split.
        apply WBEqListR.
        split.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB'))).
        simpl.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')).
        simpl.
        unfold listWB.
        rewrite(coseq_eq(act ("p" & [|("l1", I, "p" & [|("l1", I, WB')|])|]))).
        unfold coseq_id.
        simpl.
        constructor.
        specialize(CoInSplit1 ("p", rcv)
        ( (cocons ("p", rcv) (act ("p" & [|("l1", I, WB')|]))))
        ("p", rcv) (act ("p" & [|("l1", I, WB')|]))
        ); intro Ha.
        apply Ha.
        simpl. easy. easy.

        specialize(CoInSplit2 ("p", snd)
        ( (cocons ("p", rcv) (act ("p" & [|("l1", I, WB')|]))))
        ("p", rcv) (act ("p" & [|("l1", I, WB')|]))
        ); intro Ha.
        constructor.
        apply Ha.
        simpl. easy. easy.

        rewrite(coseq_eq(act ("p" & [|("l1", I, WB')|]))).
        unfold coseq_id. simpl.
        specialize(CoInSplit2 ("p", snd)
        ( (cocons ("p", rcv) (act WB')))
        ("p", rcv) (act WB')
        ); intro Ha'.
        apply Ha'.
        simpl. easy. easy.

        rewrite(coseq_eq (act WB')).
        unfold coseq_id.
        simpl.
        specialize(CoInSplit2 ("p", snd)
        ( (cocons ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))))
        ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))
        ); intro Ha''.
        apply Ha''.
        simpl. easy. easy.
        rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))).
        unfold coseq_id. simpl.

        specialize(CoInSplit1 ("p", snd)
        ( ( cocons ("p", snd) (act WB')))
        ("p", snd) (act WB')
        ); intro Ha'''.
        apply Ha'''.
        simpl. easy. easy.
        constructor. easy.
        exists listWB.
        exists listWB.
        split.

        pfold.
        rewrite(coseq_eq((act ("p" ! [|("l3", I, WB)|])))).
        unfold coseq_id.
        simpl. constructor.
        simpl. right. left. easy.
        unfold upaco2. left.
        apply WBEqList2.
        split.

        pfold.
        rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')))).
        unfold coseq_id.
        simpl. constructor.
        simpl. left. easy.
        unfold upaco2. left.
        apply WB'EqList2.
        split.

        unfold listWB.
        rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]))).
        unfold coseq_id.
        simpl.
        constructor.
        specialize(CoInSplit2 ("p", rcv)
        ( (cocons ("p", snd) (act WB) ))
        ("p", snd) (act WB)
        ); intro Ha.
        apply Ha.
        simpl. easy. easy.
        rewrite(coseq_eq(act WB)).
        unfold coseq_id. simpl.
        specialize(CoInSplit1 ("p", rcv)
        ( (cocons ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))))
        ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))
        ); intro Ha'.
        apply Ha'.
        simpl. easy. easy.
        specialize(CoInSplit1 ("p", snd)
        ( (cocons ("p", snd) (act WB)))
        ("p", snd) (act WB)
        ); intro Ha''.
        constructor.
        apply Ha''.
        simpl. easy. easy.
        constructor. split.

        unfold listWB.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) WB')).
        simpl.
        constructor.
        rewrite(coseq_eq(act ("p" & [|("l1", I, WB')|]))).
        unfold coseq_id.
        simpl.
        specialize(CoInSplit1 ("p", rcv)
        ( (cocons ("p", rcv) (act WB')))
        ("p", rcv) (act WB')
        ); intro Ha.
        apply Ha.
        simpl. easy. easy.
        rewrite(coseq_eq(act ("p" & [|("l1", I, WB')|]))).
        unfold coseq_id. simpl.
        specialize(CoInSplit2 ("p", snd)
        ( (cocons ("p", rcv) (act WB')))
        ("p", rcv) (act WB')
        ); intro Ha.
        constructor.
        apply Ha.
        simpl. easy. easy.
        rewrite(coseq_eq (act WB')).
        unfold coseq_id.
        simpl.
        specialize(CoInSplit2 ("p", snd)
        ( (cocons ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))))
        ("p", rcv) (act ("p" ! [|("l3", I, WB')|]))
        ); intro Ha'.
        apply Ha'.
        simpl. easy. easy.
        rewrite(coseq_eq(act ("p" ! [|("l3", I, WB')|]))).
        unfold coseq_id. simpl.
        specialize(CoInSplit1 ("p", snd)
        ( (cocons ("p", snd) (act WB')))
        ("p", snd) (act WB')
        ); intro Ha'''.
        apply Ha'''.
        simpl. easy. easy.
        constructor. easy.
        exists listWB.
        exists listWB.
        split.

apply action_eq1.
split.
apply action_eq2.
split.
apply action_eq3.
split.
apply action_eq4. easy.
exists listWB.
exists listWB.
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
        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))).
        simpl.
        rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
        simpl.

        pfold.
         rewrite(st_eq WB).
         simpl.
        specialize(ref_a (upaco2 refinementR r) ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|])  
                                                  ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]) "p" "l1" (I) (I) (ap_end) 1); intros HSA.
        simpl in HSA.
        rewrite apend_an in HSA.
        rewrite apend_an in HSA.
        apply HSA.

        apply srefl.
        unfold upaco2.
        left.
        pfold.
        rewrite(st_eq WB').
        simpl.
        specialize(ref_b (upaco2 refinementR r)
                           ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])
                           WB'
                           "p"
                           "l3"
                           (I)
                           (I)
                           (bp_receivea "p" "l1" (I)) 
                           (S (S n))

                   ); intro Hb.
         simpl in Hb.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n)))))
         in Hb.
         simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n))) in Hb.
         simpl in Hb.
         rewrite helper3 in Hb.

         apply Hb.
         apply srefl.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.

         specialize(ref_b (upaco2 refinementR r)
                            ("p" ! [|("l3", I, WB)|])
                            WB'
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (S(S(S n)))
                   ); intro Hc.
         simpl in Hc.
         rewrite(st_eq WB').
         simpl.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
          (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
             (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n)))))) in Hc.
         simpl in Hc.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n)))) in Hc.
         simpl in Hc.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         rewrite helper3 in Hc.
         apply Hc.
         apply srefl.

         specialize(ref_b (upaco2 refinementR r)
                            WB
                            WB'
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
                   (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n))))))) in Hd.
         simpl in Hd.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
            (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                  (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n))))) in Hd.
         simpl in Hd.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
              (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                 (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n)))) in Hd.
         simpl in Hd.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I, WB')|]) n))) in Hd.
         simpl in Hd.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         rewrite helper3 in Hd.
         rewrite(st_eq WB').
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
         exists listWB.
         exists listWB.
         split.
         apply WBEqList.
         split.
         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         pfold.
         rewrite(coseq_eq((act ("p" & [|("l1", I, "p" & [|("l1", I, "p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|])|])|])))).
         unfold coseq_id.
         simpl. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [|("l1", I, "p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|])|])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply WB'EqList3.
         split.

         apply WBEqListR.
         split.
         unfold listWB.
         rewrite(coseq_eq (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                               (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                               (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) 
                               (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))))).
         unfold coseq_id.
         simpl.
         constructor.

         specialize(CoInSplit1 ("p", rcv)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))
         ); intro Ha.
         apply Ha. simpl. easy. easy.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))
         ); intro Ha.
         constructor.
         apply Ha. simpl. easy. easy.
         (*repeated?*)
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))).
         simpl.
         rewrite(coseq_eq((act ("p" & [|("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))|])))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))
         ); intro Ha'.
         apply Ha'.
         simpl. easy. easy.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
         simpl.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))|]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))
         ); intro Ha''.
         apply Ha''.
         simpl. easy. easy.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))
         ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))
         ); intro Ha'''.
         apply Ha'''.
         simpl. easy. easy.
         apply inWB'ns.
         constructor. easy.
         exists listWB.
         exists listWB.
         split.

         pfold.
         rewrite(coseq_eq((act ("p" ! [|("l3", I, WB)|])))).
         unfold coseq_id. simpl. constructor.
         simpl. right. left. easy.
         unfold upaco2. left.
         apply WBEqList2.
         split.

         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         pfold.
         rewrite(coseq_eq((act ("p" & [|("l1", I, "p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|])|])))).
         unfold coseq_id.
         simpl. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply WB'EqList3.
         split.

         unfold listWB.
         rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]))).
         unfold coseq_id.
         simpl.
         constructor.
         specialize(CoInSplit2 ("p", rcv)
         ( (cocons ("p", snd) (act WB)))
         ("p", snd) (act WB)
         ); intro Ha. 
         apply Ha. simpl. easy. easy.
         rewrite(coseq_eq(act WB)).
         unfold coseq_id. simpl.
         specialize(CoInSplit1 ("p", rcv)
         ( (cocons ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))))
         ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))
         ); intro Ha'.
         apply Ha'. simpl. easy. easy.
         constructor.
         specialize(CoInSplit1 ("p", snd)
         ((cocons ("p", snd) (act WB)))
         ("p", snd) (act WB)
         ); intro Ha''.
         apply Ha''. simpl. easy. easy.
         constructor. split.

         unfold listWB.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))).
         simpl.
         rewrite(coseq_eq((act ("p" & [|("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))|])))).
         unfold coseq_id.
         simpl.
         constructor.

         specialize(CoInSplit1 ("p", rcv)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))
         ); intro Ha.
         apply Ha. simpl. easy. easy.

         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))
         ); intro Ha'.
         constructor.
         apply Ha'.
         simpl. easy. easy.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
         simpl.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))|]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                         (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))
         ); intro Ha''.
         apply Ha''.
         simpl. easy. easy.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv)
                        (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))
         ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))
         ); intro Ha'''.
         apply Ha'''.
         simpl. easy. easy.
         apply inWB'ns.
         constructor. easy.
         exists listWB.
         exists listWB.
         split.

         pfold.
         rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))).
         unfold coseq_id.
         simpl. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("p" ! [|("l3", I, WB)|])) )).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. right. left. easy.
         unfold upaco2. left.
         apply WBEqList2.
         split.

         rewrite(st_eq((merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))).
         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         rewrite(coseq_eq((act ("p" & [|("l1", I, "p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])|])))).
         unfold coseq_id.
         simpl. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|])) ).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply WB'EqList3.
         split.

         unfold listWB.
         rewrite(coseq_eq(act ("p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|]))).
         unfold coseq_id. simpl.
         constructor.
         specialize(CoInSplit2 ("p", rcv)
         ( (cocons ("p", snd) (act ("p" ! [|("l3", I, WB)|]))))
         ("p", snd) (act ("p" ! [|("l3", I, WB)|]))
         ); intro Ha.
         apply Ha. simpl. easy. easy.
         rewrite(coseq_eq(act ("p" ! [|("l3", I, WB)|]))).
         unfold coseq_id.
         simpl.
         specialize(CoInSplit2 ("p", rcv)
         ( (cocons ("p", snd) (act WB) ))
         ("p", snd) (act WB) 
         ); intro Ha'.
         apply Ha'. simpl. easy. easy.
         rewrite(coseq_eq(act WB)). 
         unfold coseq_id. simpl.
         specialize(CoInSplit1 ("p", rcv)
         ( (cocons ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))))
         ("p", rcv) (act ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, WB)|])|])|]))
         ); intro Ha''.
         apply Ha''. simpl. easy. easy.
         specialize(CoInSplit1 ("p", snd)
         ( (cocons ("p", snd) (act ("p" ! [|("l3", I, WB)|]))))
         ("p", snd) (act ("p" ! [|("l3", I, WB)|]))
         ); intro Ha'''.
         constructor.
         apply Ha'''. simpl. easy. easy.
         constructor. split.

         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))).
         simpl.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))|]))).
         unfold coseq_id. simpl.
         constructor.
         specialize(CoInSplit1 ("p", rcv)
         ( (cocons ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))))
         ("p", rcv) (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)))
         ); intro Ha.
         apply Ha. simpl. easy. easy.

         simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))).
         simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv) (act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))))
         ("p", rcv) (act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))
         ); intro Ha.
         constructor.
         apply Ha.
         simpl. easy. easy.
         rewrite(coseq_eq(act ("p" & [|("l1", I, merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n)|]))).
         unfold coseq_id. simpl.
         specialize(CoInSplit2 ("p", snd)
         ( (cocons ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))))
         ("p", rcv) (act (merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' n))
         ); intro Ha'.
         apply Ha'. simpl. easy. easy.
         apply inWB'ns.
         constructor. easy.
         exists listWB.
         exists listWB.
         split.
apply action_eq5.
split.
apply action_eq9.
split.
apply action_eq7.
split.
apply action_eq10. easy.
Qed.


Lemma dp_comm: forall n d w,
 (merge_dpf_cont d (merge_dpf_contn d w n)) = 
 (merge_dpf_contn d (merge_dpf_cont d w) n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.

Lemma dp_Scomm: forall n d w,
 (merge_dpf_cont d (merge_dpf_contn d w n)) = 
 (merge_dpf_contn d w) (S n).
Proof. intro n.
       induction n; intros.
       - simpl. easy.
       - simpl. rewrite IHn. easy.
Qed.


Lemma act_eqp31_1:
exists L1 L2 : list (participant * dir),
  coseqInLC (act WD) L1 /\
  coseqInLC (act WD) L2 /\
  coseqInR L1 (act WD) /\
  coseqInR L2 (act WD) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists [("p",snd)].
       exists [("p",snd)].
       split.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqp31_2:
exists L1 L2 : list (participant * dir),
  coseqInLC (act WA) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD)) L2 /\
  coseqInR L1 (act WA) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD)) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split. pfold.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. 
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       unfold listWB.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       
       split. 
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD))). unfold coseq_id. simpl.
       constructor. 
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.    
       easy.
Qed.

Lemma act_eqp31_3:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD)) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD)) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       rewrite dpfend_dn.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       left. pfold.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. 
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       rewrite dpfend_dn.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WA)). simpl. easy. easy.
       rewrite(coseq_eq (act WA)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA ))). unfold coseq_id. simpl.
       constructor.
       rewrite dpfend_dn.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WA)). simpl. easy. easy.
       constructor.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqp31_4:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA)) L1 /\
  coseqInLC (act WA) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA)) /\
  coseqInR L2 (act WA) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split. pfold.
       rewrite(coseq_eq (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)) ). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite dpfend_dn.  rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pcofix CIH. 
       pfold. rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA))). unfold coseq_id. simpl.
       unfold listWB.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WA)). simpl.
       rewrite dpfend_dn. easy. easy.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). simpl. easy. easy.
       constructor.
       
       split.
       unfold listWB. rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqp31_5:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA)) L1 /\
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA)) /\
  coseqInR L2 (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite dpfend_dn. rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold. rewrite dpfend_dn. rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pcofix CIH.
       pfold. rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       right. exact CIH.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA))).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA)) ). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WA)). simpl. rewrite dpfend_dn. easy. easy.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       rewrite(coseq_eq (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end) ) WA))). simpl. easy. easy.
       constructor.
       
       split.
       constructor.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act WA)). simpl. rewrite dpfend_dn. easy. easy.
       rewrite(coseq_eq(act WA)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
       constructor.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act WA)). simpl. rewrite dpfend_dn. easy. easy.
       constructor.
       easy.
Qed.


Lemma actp31_B1H1: forall k n, coseqInLC (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)) listWB.
Proof. intro k.
       induction k; intros.
       - simpl. induction n; intros.
         + simpl. 
           rewrite(coseq_eq (act WA)). unfold coseq_id. simpl.
           pfold. constructor. simpl. left. easy.
           left. pcofix CIH.
           pfold. rewrite(coseq_eq(act WD)). unfold coseq_id. simpl.
           constructor. simpl. right. left. easy.
           right. exact CIH.
         + simpl.
           pfold. rewrite(coseq_eq(act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))). unfold coseq_id. simpl.
           constructor. simpl. left. easy.
           left. pfold.
           rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))). unfold coseq_id. simpl.
           constructor. simpl. right. left. easy.
           left. pfold.
           rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
           unfold coseq_id. simpl. constructor. simpl. right. left. easy.
           left. pfold.
           rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). unfold coseq_id. simpl.
           constructor. simpl. right. left. easy.
           left. unfold coseqInLC in IHn.
           rewrite dpfend_dn. exact IHn.
        - simpl. unfold pi1 at 1.
          rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
          unfold coseq_id. simpl.
          pfold.
          constructor. simpl. left. easy.
          left. pfold. 
          rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
          unfold coseq_id. simpl.
          constructor. simpl. right. left. easy.
          left. specialize(IHk n). unfold coseqInLC in IHk.
          rewrite dpfend_dn.
          exact IHk.
Qed.

Lemma actp31_B1H2: forall k n,
coseqInLC
  (act
     (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
        (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))) listWB.
Proof. intros.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl. pfold.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left.
       specialize(actp31_B1H1 k n); intro Hk.
       unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
Qed.

Lemma actp31_B1H3: forall k n,
coseqInR listWB (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)).
Proof. intro k.
       induction k; intros.
       - simpl. induction n; intros.
         + simpl. 
           rewrite(coseq_eq (act WA)). unfold coseq_id, listWB. simpl.
           constructor.
           apply CoInSplit1 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
           constructor.
           apply CoInSplit2 with (y := ("p", rcv)) (ys := (act WD)). simpl. easy. easy.
           rewrite(coseq_eq (act WD)). unfold coseq_id. simpl.
           apply CoInSplit1 with (y := ("p", snd)) (ys := (act WD)). simpl. easy. easy.
           constructor.
         + simpl. unfold pi3 at 1.
           inversion IHn. subst.
           rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                                (merge_dpf_contn pi3 WA n)))).
           unfold coseq_id. simpl.
           constructor.
           apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))
                                                          (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
           constructor.
           apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
           simpl. easy. easy.
           rewrite(coseq_eq (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
           unfold coseq_id. simpl.
           apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
           constructor.
        - simpl. unfold pi1 at 1.
          rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
          unfold coseq_id, listWB. simpl.
          constructor.
          apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
          simpl. easy. easy.
          constructor.
          apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
          simpl. easy. easy.
          rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
          unfold coseq_id. simpl.
          apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))).
          simpl. rewrite dpfend_dn. easy. easy.
          constructor.
Qed.

Lemma actp31_B1H4: forall k n,
coseqInR listWB (act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))).
Proof. intros.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       simpl. easy. easy.
       rewrite(coseq_eq (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))).
       simpl. rewrite dpfend_dn. easy. easy.
       constructor.
Qed.

Lemma actp31_B1: forall n k,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k)) k)) L1 /\
  coseqInLC
    (act
       (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
          (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k - 1)) k))) L2 /\
  coseqInR L1 (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k)) k)) /\
  coseqInR L2
    (act
       (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
          (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k - 1)) k))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. intros.
       exists listWB.
       exists listWB.
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
coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))) listWB.
Proof. intros.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left.
       specialize(actp31_B1H1 k n); intros Hk.
       unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
Qed.

Lemma actp31_B2H2: forall k n,
coseqInLC
  (act
     (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
        (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
           (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))) listWB.
Proof. intros.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))))).
       unfold coseq_id. simpl.
       pfold. constructor.
       simpl. right. left. easy.
       left. pfold.
       rewrite dpfend_dn.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl.
       left. pfold. constructor. simpl. right. left. easy.
       left.
       specialize(actp31_B1H1 k n); intros Hk.
       unfold coseqInLC in Hk.
       rewrite dpfend_dn. exact Hk.
Qed.

Lemma actp31_B2H3: forall k n,
coseqInR listWB (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))).
Proof. intros.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))).
       simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 k n); intro Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))).
       simpl. rewrite dpfend_dn. easy. easy.
       constructor.
Qed.

Lemma actp31_B2H4: forall k n,
coseqInR listWB
  (act
     (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
        (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
           (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
Proof. intros.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       simpl. rewrite dpfend_dn. easy. easy.
       rewrite(coseq_eq (act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k))) ).
       simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) k)))).
       simpl. rewrite dpfend_dn. easy. easy.
       constructor.
Qed.

Lemma actp31_B2: forall n k,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k)) k))) L1 /\
  coseqInLC
    (act
       (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
          (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k - 1)) k)))) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k)) k))) /\
  coseqInR L2
    (act
       (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
          (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - S k - 1)) k)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. intros.
       exists listWB.
       exists listWB.
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
  coseqInLC (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))) L2 /\
  coseqInR L1 (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       unfold pi3 at 1.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))).
       simpl. rewrite dpfend_dn. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqpi3B2: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act ("p" ! [|("l3", I, merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))|])) L1 /\
  coseqInLC (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))) L2 /\
  coseqInR L1 (act ("p" ! [|("l3", I, merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))|])) /\
  coseqInR L2 (act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))|]))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. 
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act ("p" ! [|("l3", I, merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))|]))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))) ).
       simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit1 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("p", rcv)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. 
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqpi3B3: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))) L1 /\
  coseqInLC (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))) /\
  coseqInR L2 (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       simpl. easy. easy.
       constructor.
      
       split.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       exact Hk.
       easy.
Qed.

Lemma act_eqpi3B4: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))) L1 /\
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))) /\
  coseqInR L2 (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split. 
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl. 
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 (S n)); intro Hk.
       simpl in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n))))).
       unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 (S n)); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont pi3 (merge_dpf_contn pi3 WA n)))).
       simpl. rewrite dpfend_dn. easy. easy.
       constructor.
       easy.
Qed.

Lemma refpi3pi1: forall n, refinement (merge_dpf_contn pi3 WA (S n)) (merge_dpf_cont pi1 (merge_dpf_contn pi3 WA n)).
Proof. pcofix CIH.
       intro n.
       induction n; intros.
       - simpl.
         clear CIH.
         pfold. 
         unfold pi3, pi1.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA)).
         rewrite(st_eq  (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) WA)).
         simpl.
         specialize(ref_a (upaco2 refinementR r)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) WA)).
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)).
         simpl. 
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA)
                          WA
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb. simpl in Hb.
         rewrite !bpend_an in Hb.
         rewrite dpfend_dn.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) WA)).
         setoid_rewrite(st_eq WA) at 2. simpl.
         rewrite(st_eq WD). simpl.
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)
                          WD
                          "p" "l3" (I) (I) (bp_receivea "p" "l2" (I)) 1
         ); intro Hb. simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) ("p" ! [|("l3", I, WD)|]))) in Hb.
         simpl in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) WA)).
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD)).
         rewrite(st_eq WD).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          WA
                          WD
                          "p" "l3" (I) (I) (bp_receivea "p" "l2" (I)) 1
         ); intro Hb. simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) ("p" ! [|("l3", I, WD)|]))) in Hb.
         simpl in Hb.
         rewrite dpfend_dn.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq WA). simpl.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l2" (I)) WD)).
         simpl.
         specialize(ref_a (upaco2 refinementR r)
                          WD
                          WD
                          "p" "l2" (I) (I) (ap_end) 1
         ); intro Ha. simpl in Ha.
         rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.

         left. pcofix CIH. pfold.
         rewrite(st_eq WD). simpl.
         specialize(ref_b (upaco2 refinementR r)
                          WD
                          WD
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
         rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
                      (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         specialize(ref_a (upaco2 refinementR r)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))
                              (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                              (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
                              (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                              (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))
                      (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))
                              (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                              (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))
                          (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                              (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         rewrite dpfend_dn.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))
                      (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
                      (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         setoid_rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))) at 2.
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) 
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          ("p"! [|("l3", I, merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                          (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))|])
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))
                              (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))
                          "p" "l3" (I) (I) (bp_receivea "p" "l1" (I)) 1
         ); intro Hb.
         simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p" ! [|("l3", I,  merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))|]))) in Hb.
         simpl in Hb. rewrite dpfend_dn. apply Hb; clear Hb.
         constructor.

         left. pfold.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                      (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))
                      (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))).
         simpl.
         specialize(ref_b (upaco2 refinementR r)
                          (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))))
                             (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
                             (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))
                           "p" "l3" (I) (I) (bp_receivea "p" "l1" (I)) 1
         ); intro Hb.
         simpl in Hb.
         rewrite(st_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) ("p"! [|("l3", I,
                      merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn (dpf_receive "p" "l1" (I) 
                      (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))|]))) in Hb.
         simpl in Hb. apply Hb; clear Hb.
         constructor.
         left.

         unfold pi3, pi1 in IHn.
         rewrite(st_eq  (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n)))).
         simpl.
         rewrite(st_eq (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end))
           (merge_dpf_contn (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) WA n))) in IHn.
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

Lemma refpi3pi1A: forall (n k: nat), (n - k >= 1) -> refinement (merge_dpf_contn pi3 WA (n-k)) (merge_dpf_cont pi1 (merge_dpf_contn pi3 WA (n-k-1))).
Proof. intros.
       specialize(refpi3pi1 (n - k - 1)); intro Ha.
       simpl in Ha.
       rewrite dp_Scomm in Ha. simpl.
       assert(S (n - k - 1) = (n - k)).
       { lia. }
       rewrite H0 in Ha.
       apply Ha.
Qed.

Lemma refpi3pi1A2: forall n, n > 0 -> refinement (merge_dpf_contn pi3 WA n) (merge_dpf_cont pi1 (merge_dpf_contn pi3 WA (n-1))).
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

Lemma refpi3pi1B: forall k n, (n - k >= 1) -> refinement (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n-k)) k) 
                                                         (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n-k-1)) (S k)).
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
         rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k))) k))).
         simpl.
         rewrite(st_eq(merge_dpf_cont pi1 (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k) - 1)) k)))).
         simpl.
         specialize(ref_a (upaco2 refinementR bot2)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k))) k))
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end)
                            (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k) - 1)) k)))
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.
         
         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k))) k))).
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k) - 1)) k)))).
         simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k))) k)
                          (merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - (S k) - 1)) k))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         rewrite !dpfend_dn.
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
  coseqInLC (act (merge_dpf_contn pi3 WA n)) L1 /\
  coseqInLC (act (merge_dpf_contn pi3 WA n)) L2 /\
  coseqInR L1 (act (merge_dpf_contn pi3 WA n)) /\
  coseqInR L2 (act (merge_dpf_contn pi3 WA n)) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
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
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))) L1 /\
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))) /\
  coseqInR L2 (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. pfold. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. rewrite !dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. pfold. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. rewrite !dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       constructor.

       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqw23: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))) L1 /\
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))) /\
  coseqInR L2 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       constructor.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma act_eqw24: forall n,
exists L1 L2 : list (participant * dir),
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))) L1 /\
  coseqInLC (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))) L2 /\
  coseqInR L1 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))) /\
  coseqInR L2 (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))) /\
  (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists listWB.
       exists listWB.
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. rewrite dpfend_dn. exact Hk.

       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl. constructor. simpl. right. left. easy.
       left. specialize(actp31_B1H1 0 n); intro Hk.
       simpl in Hk. rewrite dpfend_dn. exact Hk.
       
       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       constructor.

       split.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n)))).
       unfold coseq_id, listWB. simpl.
       apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi3 WA n))). simpl. rewrite dpfend_dn. easy. easy.
       specialize(actp31_B1H3 0 n); intro Hk. simpl in Hk.
       inversion Hk. subst. easy.
       constructor.
       apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n)))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma ref_w2n: forall n, refinement (merge_dpf_contn pi3 WA n) (merge_dpf_contn pi3 WA n).
Proof. intro n.
       induction n; intros.
       - simpl. apply refwa_refl.
       - simpl. 
         unfold pi3 at 1. unfold pi3 at 2.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)))) (merge_dpf_contn pi3 WA n))).
         simpl.
         pfold.
         specialize(ref_a (upaco2 refinementR bot2)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))
                          "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.
         
         left. pfold.
         rewrite(st_eq (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end))) (merge_dpf_contn pi3 WA n))).
         simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))
                          (merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         
         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi3 WA n))). simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))
                          (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.
         
         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi3 WA n))). simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          (merge_dpf_contn pi3 WA n)
                          (merge_dpf_contn pi3 WA n)
                          "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         rewrite !dpfend_dn.
         apply Hb; clear Hb.
         constructor.
         left. unfold refinement in IHn. exact IHn.
         apply act_eqw21.
         apply act_eqw22.
         apply act_eqw23.
         apply act_eqw24.
Qed.

Lemma ref_transpippi3: forall m n, refinement (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m) 
                                              (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m).
Proof. intro m.
       induction m; intros.
       - simpl. apply ref_w2n.
       - simpl. unfold pi1 at 1. unfold pi1 at 2.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "p" "l1" (I) (dpf_send "p" "l3" (I) dpf_end)) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))).
         simpl.
         pfold.
         specialize(ref_a (upaco2 refinementR bot2)
                    (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))
                    (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))
                    "p" "l1" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor. 
         
         left. pfold.
         rewrite(st_eq(merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))).
         simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                    (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)
                    (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)
                    "p" "l3" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         rewrite !dpfend_dn.
         apply Hb; clear Hb.
         constructor.
         left.
         specialize(IHm n). unfold refinement in IHm.
         exact IHm.
         exists listWB.
         exists listWB.
         split.
         apply actp31_B1H1.
         split.
         apply actp31_B1H1.
         split.
         apply actp31_B1H3.
         split.
         apply actp31_B1H3.
         easy.

         exists listWB.
         exists listWB.
         split.
         rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)))).
         unfold coseq_id. simpl.
         pfold. constructor. simpl. right. left. easy.
         left.
         specialize(actp31_B1H1 m n); intro Hk.
         unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
         
         split.
         rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)))).
         unfold coseq_id. simpl.
         pfold. constructor. simpl. right. left. easy.
         left.
         specialize(actp31_B1H1 m n); intro Hk.
         unfold coseqInLC in Hk. rewrite dpfend_dn. exact Hk.
         split.
         constructor.
         rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))).
         simpl. rewrite dpfend_dn. easy. easy.
         specialize(actp31_B1H3 m n); intro Hk.
         inversion Hk. subst. easy.
         constructor.
         rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))).
         simpl. rewrite dpfend_dn. easy. easy.
         constructor.
         
         split.
         constructor.
         rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))).
         simpl. rewrite dpfend_dn. easy. easy.
         specialize(actp31_B1H3 m n); intro Hk.
         inversion Hk. subst. easy.
         constructor.
         rewrite(coseq_eq(act (merge_dpf_cont (dpf_send "p" "l3" (I) dpf_end) (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m)))).
         unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("p", snd)) (ys := (act (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA n) m))).
         simpl. rewrite dpfend_dn. easy. easy.
         constructor.
         easy.
Qed.

Lemma ntrans: forall k n u, (n >= (u+k)) ->
                            refinement (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n-u)) u) 
                                       (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n-u-k)) (u+k)).
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
         specialize(Ref_Trans (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - u)) u)
                              (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - u - k)) (u + k))
                              (merge_dpf_contn pi1 (merge_dpf_contn pi3 WA (n - u - (S k))) (u + (S k)))
                              IHk Href); intro HT.
         apply HT.
Qed.

Lemma all_refs: forall m : nat, refinement (merge_dpf_contn pi3 WA m) (merge_dpf_contn pi1 WA m).
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

Lemma st: subltype T T'.
Proof. intros. unfold subltype.
       unfold subtype.
       exists(
       [
        ((mk_siso WB (w3singleton)),(mk_siso WB' (w1singleton)));
        ((mk_siso WA (w2singleton)),(mk_siso WA (w2singleton)));
        ((mk_siso WA (w2singleton)),(mk_siso WA (w2singleton)))
        ]
       ).
       simpl.
       split.

       split.
       pcofix CIH. 
       rewrite (st_eq WB). simpl.
       rewrite(st_eq(lt2st T)). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])]);
        ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
         match xs with
         | [] => [||]
         | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
         end) [("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq ((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                match xs with
                | [] => [||]
                | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                end) [("l3", I, lt_send "p" [("l3", I, T)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                   match xs with
                   | [] => [||]
                   | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                   end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, T)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                     match xs with
                     | [] => [||]
                     | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                     end) [("l3", I, T)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                        match xs with
                        | [] => [||]
                        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                        end) [])). simpl.
       pfold.
       apply st2siso_rcv with (y := ("p" ! [|("l3", I, "p" ! [|("l3", I, "p" ! [|("l3", I, lt2st T)|])|])|])).
       simpl.
       left. pfold.
       apply st2siso_snd with (y := ("p" ! [|("l3", I, "p" ! [|("l3", I, lt2st T)|])|])). simpl.
       left. pfold.
       apply st2siso_snd with (y := ("p" ! [|("l3", I, lt2st T)|])). simpl.
       left. pfold.
       apply st2siso_snd with (y := (lt2st T)). simpl.
       right. easy.
       constructor. 
       constructor.
       constructor.
       constructor.

       split.
       pcofix CIH. 
       rewrite (st_eq WB'). simpl.
       rewrite(st_eq(lt2st T')). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
          match xs with
          | [] => [||]
          | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
          end)
         [("l1", I, lt_send "p" [("l3", I, T')]);
          ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq(((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
         match xs with
         | [] => [||]
         | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
         end) [("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, T')]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, T')])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       pfold.
       apply st2siso_rcv with (y := ("p" ! [|("l3", I, lt2st T')|])).
       left. pfold.
       apply st2siso_snd with (y := (lt2st T')).
       right. easy.
       constructor.
       constructor.
       
       split.
       rewrite (st_eq WA). simpl.
       rewrite (st_eq WD). simpl.
       rewrite(st_eq(lt2st T)). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])]);
        ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
         match xs with
         | [] => [||]
         | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
         end) [("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq ((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                match xs with
                | [] => [||]
                | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                end) [("l3", I, lt_send "p" [("l3", I, T)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                   match xs with
                   | [] => [||]
                   | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                   end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, T)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                     match xs with
                     | [] => [||]
                     | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                     end) [("l3", I, T)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                        match xs with
                        | [] => [||]
                        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                        end) [])). simpl.
       pfold.
       apply st2siso_rcv with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))).
       simpl.
       rewrite(st_eq(lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
          coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end)
           [("l3", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
             coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       left. pcofix CIH. 
       pfold.
       apply st2siso_snd with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite (st_eq WD). simpl.

       rewrite(st_eq(lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
          coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end)
           [("l3", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
             coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       right. apply CIH.
       constructor.
       constructor. easy.
       constructor.

       split.
       rewrite (st_eq WA). simpl.
       rewrite(st_eq(lt2st T')). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
          match xs with
          | [] => [||]
          | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
          end)
         [("l1", I, lt_send "p" [("l3", I, T')]);
          ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq(((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
         match xs with
         | [] => [||]
         | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
         end) [("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, T')]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, T')])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       pfold.
       apply st2siso_rcv with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))).
       left. pcofix CIH.
       rewrite (st_eq WD). simpl.

       rewrite(st_eq(lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
          coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end)
           [("l3", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
             coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       pfold.
       apply st2siso_snd with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))).
       right. apply CIH.
       constructor.
       constructor. easy.
       constructor.
       
       split.
       rewrite (st_eq WA). simpl.
       rewrite (st_eq WD). simpl.
       rewrite(st_eq(lt2st T)). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("l1", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])]);
        ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
         match xs with
         | [] => [||]
         | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
         end) [("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq ((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, lt_send "p" [("l3", I, T)])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                match xs with
                | [] => [||]
                | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                end) [("l3", I, lt_send "p" [("l3", I, T)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                   match xs with
                   | [] => [||]
                   | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                   end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, T)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                     match xs with
                     | [] => [||]
                     | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                     end) [("l3", I, T)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                        match xs with
                        | [] => [||]
                        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                        end) [])). simpl.
       pfold.
       apply st2siso_rcv with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))).
       simpl.
       rewrite(st_eq(lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
          coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end)
           [("l3", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
             coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       left. pcofix CIH. 
       pfold.
       apply st2siso_snd with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite (st_eq WD). simpl.

       rewrite(st_eq(lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
          coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end)
           [("l3", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
             coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       right. apply CIH.
       constructor.
       constructor. easy.
       constructor.

       split.
       rewrite (st_eq WA). simpl.
       rewrite(st_eq(lt2st T')). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
          match xs with
          | [] => [||]
          | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
          end)
         [("l1", I, lt_send "p" [("l3", I, T')]);
          ("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq(((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
         match xs with
         | [] => [||]
         | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
         end) [("l2", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l3", I, T')]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, T')])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       pfold.
       apply st2siso_rcv with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))).
       left. pcofix CIH.
       rewrite (st_eq WD). simpl.

       rewrite(st_eq(lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
          coseq (string * sort * st) :=
            match xs with
            | [] => [||]
            | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
            end)
           [("l3", I, lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) :
             coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       pfold.
       apply st2siso_snd with (y := (lt2st (lt_mu (lt_send "p" [("l3", I, lt_var unscoped.var_zero)])))).
       right. apply CIH.
       constructor.
       constructor. easy.
       constructor.
       easy.

       split.
       exists dpf_end. exists dpf_end. intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       specialize(WBRef 0); intros.
       rewrite(st_eq(merge_bp_contn "p" (bp_receivea "p" "l1" (I)) WB' 0)) in H.
       simpl in H. simpl.
       rewrite(st_eq WB').
       simpl.
       apply H.
       constructor.
       
       split.
       exists dpf_end. exists dpf_end. intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       apply refwa_refl.
       split.
       
       exists pi3.
       exists pi1.
       intro n.
       simpl.
       apply all_refs.

       easy.
Qed.

