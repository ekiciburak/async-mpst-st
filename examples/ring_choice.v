Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition ltB := lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, (lt_var 0));
                                                                 ("sub", I, (lt_var 0))])]).

Definition ltBOp := lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, (lt_var 0))]); 
                                        ("sub", I, lt_receive "A" [("add", I, (lt_var 0))])]).

CoFixpoint rcp := st_receive "A" [("add", I, st_send "C" [("add", I, rcp);
                                                          ("sub", I, rcp)])].

CoFixpoint rcop := st_send "C" [("add", I, st_receive "A" [("add", I, rcop)]); 
                                ("sub", I, st_receive "A" [("add", I, rcop)])].

CoFixpoint w1 := st_receive "A" [("add", I, st_send "C" [("add", I, w1)])].
CoFixpoint w2 := st_send "C" [("add", I, st_receive "A" [("add", I, w2)])].

CoFixpoint w3 := st_receive "A" [("add", I, st_send "C" [("sub", I, w3)])].
CoFixpoint w4 := st_send "C" [("sub", I, st_receive "A" [("add", I, w4)])].

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
       assert (singleton w2) as Hw2.
       { pcofix CIH. rewrite(st_eq w2). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w1) as Hw1.
       { pcofix CIH. rewrite(st_eq w1). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       exists [((mk_siso w2 Hw2),(mk_siso w1 Hw1))].
       simpl.
       split. split.

       pcofix CIH. pfold.
       rewrite(st_eq w2). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd.
       left. pfold. simpl.
       apply st2siso_rcv.
       simpl. right. apply CIH.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w1). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH. easy.
       split.
       exists dp_end. exists dp_end. intro n.
       rewrite !dpend_ann.

       pcofix CIH. pfold.
       rewrite(st_eq w2). rewrite(st_eq w1). simpl.
       specialize(ref_b (upaco2 refinementR r) ("A" & [("add", I, w2)]) (w1)
                          "C" "add" (I) (I) (@bp_receivea "C" "A" "add" (I)) 1
                          ); intro Hb.
       simpl in Hb.
       rewrite(st_eq (merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [("add", I, w1)]))) in Hb. simpl in Hb.
       apply Hb.
       constructor.
       left. pfold.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)). simpl.
       clear Hb.

       specialize(ref_a (upaco2 refinementR r) (w2) (w1)
                          "A" "add" (I) (I) (ap_end) 1
                          ); intro Ha.
       simpl in Ha.
       rewrite(st_eq(merge_ap_cont "A" ap_end ("A" & [("add", I, w1)]))) in Ha. simpl in Ha.
       apply Ha. constructor.
       rewrite apend_an.
       right. exact CIH.
       clear Ha.

       exists actL.
       exists actL.
       split.
       apply acteqr1.
       split. rewrite apend_an.
       apply acteqr2.
       split.
       apply acteqr3.
       rewrite apend_an.
       split.
       apply acteqr4.
       easy.

       clear Hb.
       exists actL.
       exists actL.
       split.
       apply acteqr5.
       split.
       apply acteqr6.
       split.
       apply acteqr7.
       split.
       apply acteqr8.
       easy.
       easy.
Qed.

Lemma ltB_rcp: lt2stC ltB rcp.
Proof. unfold ltB.
       rewrite (st_eq rcp). simpl.
       pcofix CIH.
       pfold.
       apply lt2st_mu. simpl.
       specialize (lt2st_rcv (upaco2 lt2st r)
       "A" ["add"] [(I)]
       [(lt_send "C"
         [("add", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
          ("sub", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))])]
       (["C" ! [("add", I, rcp); ("sub", I, rcp)]])
       ); intro HR.
       apply HR; clear HR. simpl. easy. 
       apply Forall_forall.
       intros (l, s).
       simpl. intros.
       destruct H as [H | H]. inversion H. subst.
       left. pfold.
       specialize (lt2st_snd (upaco2 lt2st r)
       "C" ["add"; "sub"] [(I); (I)]
       [(lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
        (lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))]
       [rcp; rcp]
       ); intro HS. simpl in HS.
       apply HS; clear HS. easy.
       apply Forall_forall.
       intros (l, s). simpl. intro H1.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcp). simpl. exact CIH.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcp). simpl. exact CIH.
       easy.
       easy.
Qed.

Lemma ltBop_rcop: lt2stC ltBOp rcop.
Proof. unfold ltBOp.
       rewrite (st_eq rcop). simpl.
       pcofix CIH.
       pfold. 
       apply lt2st_mu. simpl.
       specialize (lt2st_snd (upaco2 lt2st r)
         "C" ["add"; "sub"] [(I); (I)]
         [(lt_receive "A"
           [("add", I,
             lt_mu
               (lt_send "C"
                  [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
                   ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]);
        (lt_receive "A"
           [("add", I,
             lt_mu
               (lt_send "C"
                  [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
                   ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])]
           [("A" & [("add", I, rcop)]); ("A" & [("add", I, rcop)])]
       ); intro HS. simpl in HS.
       apply HS; clear HS. easy.
       apply Forall_forall.
       intros (l,s) H.
       simpl in H.
       destruct H as [H | H].
       inversion H. subst.
       left. pfold. simpl.
       specialize (lt2st_rcv (upaco2 lt2st r)
       "A" ["add"] [(I)]
       [(lt_mu
         (lt_send "C"
            [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
             ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]
       [rcop]
       ); intro HR. simpl in HR.
       apply HR; clear HR. easy.
       apply Forall_forall.
       intros (l, s) H1.
       simpl in H1.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcop). simpl. exact CIH.
       easy.
       destruct H as [H | H].
       inversion H. subst.
       left. pfold. simpl.
       specialize (lt2st_rcv (upaco2 lt2st r)
       "A" ["add"] [(I)]
       [(lt_mu
         (lt_send "C"
            [("add", I, lt_receive "A" [("add", I, lt_var 0)]);
             ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]
       [rcop]
       ); intro HR. simpl in HR.
       apply HR; clear HR. easy.
       apply Forall_forall.
       intros (l, s) H1.
       simpl in H1.
       destruct H1 as [H1 | H1].
       inversion H1. subst.
       right. rewrite (st_eq rcop). simpl. exact CIH.
       easy.
       easy.
Qed.

Lemma ltB_ltBop: subltype ltBOp ltB rcop rcp ltBop_rcop ltB_rcp.
Proof. unfold subltype.
       exact st_rcp.
Qed. 


