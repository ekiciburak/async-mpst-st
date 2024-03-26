Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
Require Import Lia.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition type1: st := st_send "p" [("l1",I,st_receive "q" [("l3",I,st_end);("l4",I,end)])].

Definition type2: st := st_send "p" [("l1",I,st_receive "q" [("l3",I,st_end)]);("l2",I,end)].

Definition dec12 := st_send "p" [("l1",I,st_receive "q" [("l3",I,end)])].

Lemma singl12: singleton dec12.
Proof. pfold.
       constructor. 
       left. pfold. constructor.
       left. pfold. constructor.
Qed.

Lemma act_eqt1t21:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (end)) L1 /\
  coseqInLC (act (end)) L2 /\
  coseqInR L1 (act (end)) /\ coseqInR L2 (act (end)) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists nil.
       exists nil.
       split. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. constructor.
       split. constructor.
       easy.
Qed.

Lemma act_eqt1t22:
exists L1 L2 : list (participant * dir),
  coseqInLC (act ("q" & [("l3", I, end)])) L1 /\
  coseqInLC (act ("q" & [("l3", I, end)])) L2 /\
  coseqInR L1 (act ("q" & [("l3", I, end)])) /\
  coseqInR L2 (act ("q" & [("l3", I, end)])) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists [("q",rcv)].
       exists [("q",rcv)].
       split. rewrite(coseq_eq(act ("q" & [("l3", I, end)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. rewrite(coseq_eq(act ("q" & [("l3", I, end)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. constructor. rewrite(coseq_eq(act ("q" & [("l3", I, end)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("q", rcv)) (ys := (act (end))). simpl. easy. easy.
       constructor.
       split. constructor. rewrite(coseq_eq(act ("q" & [("l3", I, end)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("q", rcv)) (ys := (act (end))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma subtypet1t2: subtype type1 type2.
Proof. unfold subtype.
       exists [(mk_siso dec12 singl12, mk_siso dec12 singl12)].
       split.
       - simpl. split.
         + pfold. constructor. simpl.
           left. pfold. constructor. simpl. constructor. pfold. constructor.
         + split. pfold. constructor. simpl.
           left. pfold. constructor. simpl. constructor. pfold. constructor.
           easy.
       - simpl. split. exists dp_end. exists dp_end.
         intro n.
         rewrite dpend_ann.
         pfold. rewrite(st_eq(dec12)). simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          ("q" & [("l3", I, end)])
                          ("q" & [("l3", I, end)])
                          "p" "l1" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         specialize(ref_a (upaco2 refinementR bot2)
                          (end)
                          (end)
                          "q" "l3" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.
         left. pfold. constructor.
         apply act_eqt1t21.
         apply act_eqt1t22.
         easy.
Qed.
