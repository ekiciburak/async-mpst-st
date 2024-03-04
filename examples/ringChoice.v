Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso 
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

CoFixpoint rcp := st_receive "A" [("add", I, st_send "C" [("add", I, rcp);
                                                          ("sub", I, rcp)])].

CoFixpoint rcop := st_send "C" [("add", I, st_receive "A" [("add", I, rcop)]); 
                                ("sub", I, st_receive "A" [("add", I, rcop)])].

CoFixpoint w1 := st_receive "A" [("add", I, st_send "C" [("add", I, w1)])].
CoFixpoint w2 := st_send "C" [("add", I, st_receive "A" [("add", I, w2)])].

Definition actL := [("A",rcv); ("C",snd)].

Lemma acteqr1: coseqInLC (act w2) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. 
       rewrite(coseq_eq(act ("A" & [("add", I, w2)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr2: coseqInLC (act w1) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, w1)])]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. 
       rewrite(coseq_eq(act ("C" ! [("add", I, w1)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr3: coseqInR actL (act w2).
Proof. unfold actL.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("C", snd)) (ys := (act ("A" & [("add", I, w2)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("A" & [("add", I, w2)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w2)). simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [("add", I, w2)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr4: coseqInR actL (act w1).
Proof. unfold actL.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, w1)])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, w1)]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, w1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [("add", I, w1)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w1)). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr5: coseqInLC (act ("A" & [("add", I, w2)])) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act ("A" & [("add", I, w2)]))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr1.
Qed.

Lemma acteqr6: coseqInLC (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr2.
Qed.

Lemma acteqr7: coseqInR actL (act ("A" & [("add", I, w2)])).
Proof. unfold actL.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, "A" & [("add", I, w2)])])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [("add", I, "A" & [("add", I, w2)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [("add", I, w2)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr8: coseqInR actL (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)).
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w1)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act w1)). simpl. easy. easy.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [("add", I, "C" ! [("add", I, w1)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [("add", I, w1)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [("add", I, w1)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w1)). simpl. easy. easy.
       constructor.
Qed.

Lemma st_rcp: subtype rcop rcp.
Proof. unfold subtype.
       intros U. split.
       pfold. rewrite(st_eq rcop). simpl.
       specialize(st2so_snd (upaco2 st2so bot2) "add" (I) ("A" & [("add", I, rcop)]) U
                            ([("add", I, "A" & [("add", I, rcop)]); ("sub", I, "A" & [("add", I, rcop)])])
                            "C"
                            ); intro Hs.
       apply Hs. simpl. left. easy. clear Hs.
       left. pcofix CIH.
       pfold.
       specialize(st2so_snd (upaco2 st2so r) "add" (I) ("A" & [("add", I, rcop)]) U
                            ([("add", I, "A" & [("add", I, rcop)])])
                            "C"
                            ); intro Hs.
       apply Hs. simpl. left. easy.
       right. exact CIH.

       intro V'.
       split. pcofix CIH. pfold.
       rewrite(st_eq rcp). simpl.
       specialize(st2si_rcv (upaco2 st2si r) "add" (I) ("C" ! [("add", I, rcp); ("sub", I, rcp)]) V'
                            ([("add", I, "C" ! [("add", I, rcp); ("sub", I, rcp)])]) "A"); intro Hr.
       apply Hr. simpl. left. easy.
       right. rewrite(st_eq rcp) in CIH. simpl in CIH.
       exact CIH.

       assert (singleton w2) as Hw2.
       { pcofix CIH. rewrite(st_eq w2). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       exists (mk_siso w2 Hw2).
       split. simpl.
       pcofix CIH. pfold.
       rewrite(st_eq w2). simpl.
       specialize(st2siso_snd (upaco2 st2siso r) "add" (I) ("A" & [("add", I, w2)]) U
                              ([("add", I, "A" & [("add", I, w2)])]) "C"); intro Hs.
       apply Hs. simpl. left. easy.
       right. rewrite(st_eq w2) in CIH. simpl in CIH. exact CIH.

       assert (singleton w1) as Hw1.
       { pcofix CIH. rewrite(st_eq w1). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       exists (mk_siso w1 Hw1).
       split. simpl.
       pcofix CIH. pfold. 
       rewrite(st_eq w1). simpl.
       specialize(st2siso_rcv (upaco2 st2siso r) "add" (I) ("C" ! [("add", I, w1)]) V'
                              ([("add", I, "C" ! [("add", I, w1)])]) "A"); intro Hr.
       apply Hr. simpl. left. easy.
       right. rewrite(st_eq w1) in CIH. simpl in CIH. exact CIH.

       simpl.
       pcofix CIH. pfold.
       rewrite(st_eq w2). rewrite(st_eq w1). simpl.
       specialize(_sref_b (upaco2 refinementR r) ("A" & [("add", I, w2)]) (w1)
                          "C" "add" (I) (I) (@bp_receivea "C" "A" "add" (I)) 1
                          ); intro Hb.
       simpl in Hb.
       rewrite(st_eq (merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [("add", I, w1)]))) in Hb. simpl in Hb.
       apply Hb.
       constructor.
       left. pfold.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)). simpl.
       clear Hb.

       specialize(_sref_a (upaco2 refinementR r) (w2) (w1)
                          "A" "add" (I) (I) (ap_end) 1
                          ); intro Ha.
       simpl in Ha.
       rewrite(st_eq(merge_ap_cont "A" ap_end ("A" & [("add", I, w1)]))) in Ha. simpl in Ha.
       apply Ha. constructor.
       rewrite apend_an.
       right. exact CIH.
       clear Ha.

       exists actL.
       split.
       apply acteqr1.
       split. rewrite apend_an.
       apply acteqr2.
       split.
       apply acteqr3.
       rewrite apend_an.
       apply acteqr4.

       clear Hb.
       exists actL.
       split.
       apply acteqr5.
       split.
       apply acteqr6.
       split.
       apply acteqr7.
       apply acteqr8.
Qed.

