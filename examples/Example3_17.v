Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

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

Lemma TWEqList: coseqInLC (act TW) ListT.
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

Lemma TW'EqList: coseqInLC (act TW') ListT.
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

Lemma TWEqListR: coseqInR ListT (act TW).
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

Lemma TWEqListR': coseqInR ListT (act TW').
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
Proof. unfold subtype.
       assert(singleton(st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))])) as Hs1.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }

       exists(mk_siso (st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))]) Hs1).
       split.

       pcofix H.
       pfold.
       simpl. rewrite(st_eq T'). simpl.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold. constructor.

       assert(singleton(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))])) as Hs2.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       exists(mk_siso(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))]) (Hs2)).
       split.

       pcofix H.
       pfold.
       simpl. rewrite(st_eq T). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold. constructor.

       pcofix CIH.
       pfold.
       specialize (ref_b (upaco2 refinementR r)
                           (st_receive "p" [("success", sint, st_end)])
                           st_end
                           "q" "cont" sint sint
                           (bp_receivea "p" "success" sint) 1
                           ); intro H.
       simpl in H.

       rewrite(st_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) ("q" ! [("cont", I, end)])))) in H.
       simpl in H.
       apply H.

       apply srefl. (*subsort*)

       rewrite (st_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end)))).
       simpl.
       unfold upaco2.
       left.
       pfold.

       specialize(ref_a (upaco2 refinementR r)  (end) (end) "p" "success" (I) (I) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA.

       apply srefl. (*subsort*)

       unfold upaco2.
       left.
       pfold.
       apply ref_end.
       exists nil.
       exists nil.
       split.
       pfold.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       split.
       pfold.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       split.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       constructor. constructor. easy.

       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       exists [("p",rcv)].
       exists [("p",rcv)].
       split.
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

       split.
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

       split.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       (Delay(cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor. split.

       rewrite(st_eq(merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end))).
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
       easy.
Qed.

