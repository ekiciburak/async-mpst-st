Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition lT': local :=
  lt_send "q" [
               ("cont",sint ,lt_receive "p" [("success",sint,lt_end);("error",sbool,lt_end)]);
               ("stop",sunit,lt_receive "p" [("success",sint,lt_end);("error",sbool,lt_end)])
              ].

Definition lT: local :=
  lt_receive "p" [
                  ("success",sint ,lt_send "q" [("cont",sint,lt_end);("stop",sunit,lt_end)]);
                  ("error",  sbool,lt_send "q" [("cont",sint,lt_end);("stop",sunit,lt_end)])
                 ].

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
       assert(singleton(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))])) as Hs2.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       exists([((mk_siso (st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))]) Hs1),
                    (mk_siso(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))]) Hs2))
              ]).
       simpl. split. split.

       pcofix H.
       pfold.
       simpl. rewrite(st_eq T'). simpl.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold. constructor.
       split.

       pcofix H.
       pfold.
       simpl. rewrite(st_eq T). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold. constructor. easy.
       split.
       exists dp_end. exists dp_end. intro n.
       rewrite !dpend_ann.

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
       easy.
Qed.


Lemma lT'2T': lt2stC lT' T'.
Proof. unfold lT'.
       rewrite (st_eq T'). simpl.
       pfold.
       specialize(lt2st_snd (upaco2 lt2st bot2)
       "q" ["cont"; "stop"] [(I); ()]
       [(lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)]);
        (lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)])]
       [("p" & [("success", I, end); ("error", B, end)]);
        ("p" & [("success", I, end); ("error", B, end)])]
       ); intro HS.
       apply HS; clear HS. simpl. easy.
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H].
       left. pfold. inversion H. subst. simpl.
       specialize(lt2st_rcv (upaco2 lt2st bot2)
       "p" ["success";"error"] [(I);(B)]
       [lt_end; lt_end]
       [(end);(end)]
       ); intro HR.
       simpl in HR. apply HR; clear HR.
       easy.
       apply Forall_forall.
       intros (l,s) H1.
       simpl in H1. destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       easy.
       destruct H as [H | H].
       left. pfold. inversion H. subst. simpl.
       specialize(lt2st_rcv (upaco2 lt2st bot2)
       "p" ["success";"error"] [(I);(B)]
       [lt_end; lt_end]
       [(end);(end)]
       ); intro HR.
       simpl in HR. apply HR; clear HR.
       easy.
       apply Forall_forall.
       intros (l,s) H1.
       simpl in H1. destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       easy.
       easy.
Qed.

Lemma lT2T: lt2stC lT T.
Proof. unfold lT.
       rewrite (st_eq T). simpl.
       pfold.
       specialize(lt2st_rcv (upaco2 lt2st bot2)
       "p" ["success";"error"] [(I);(B)]
       [lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)]; 
        lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)]]
       ["q" ! [("cont", I, end); ("stop", (), end)];
        "q" ! [("cont", I, end); ("stop", (), end)]]
       ); intro HR.
       simpl in HR. apply HR; clear HR.
       easy.
       apply Forall_forall.
       intros (l,s) H.
       simpl in H. destruct H as [H | H].
       left. pfold. inversion H. subst. simpl.
       specialize(lt2st_snd (upaco2 lt2st bot2)
       "q" ["cont"; "stop"] [(I); ()]
       [lt_end; lt_end]
       [(end); (end)]
       ); intro HS.
       apply HS; clear HS. simpl. easy.
       apply Forall_forall.
       intros (l,s) H1.
       simpl in H1. destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       easy.
       left. simpl. pfold.
       simpl in H. destruct H as [H | H].
       inversion H. subst. simpl.
       specialize(lt2st_snd (upaco2 lt2st bot2)
       "q" ["cont";"stop"] [(I);()]
       [lt_end; lt_end]
       [(end);(end)]
       ); intro HR.
       simpl in HR. apply HR; clear HR.
       easy.
       apply Forall_forall.
       intros (l,s) H1.
       simpl in H1. destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       destruct H1 as [H1 | H1].
       inversion H1. subst. simpl.
       left. pfold. constructor.
       easy.
       easy.
Qed.

Lemma lT'_lT: subltype lT' lT T' T lT'2T' lT2T.
Proof. unfold subltype.
       exact st1.
Qed. 



