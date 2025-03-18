Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Import CoListNotations.
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
  st_send "q" [|
               ("cont",sint ,st_receive "p" [|("success",sint,st_end);("error",sbool,st_end)|]);
               ("stop",sunit,st_receive "p" [|("success",sint,st_end);("error",sbool,st_end)|])
              |].

Definition T: st :=
  st_receive "p" [|
                  ("success",sint ,st_send "q" [|("cont",sint,st_end);("stop",sunit,st_end)|]);
                  ("error",  sbool,st_send "q" [|("cont",sint,st_end);("stop",sunit,st_end)|])
                 |].

Definition ListT := [("q",snd);("p",rcv)]. 

Definition TW  := st_receive "p" [|("success", sint,(st_send "q" [|("cont", sint, st_end)|]))|].
Definition TW' := st_send "q" [|("cont",sint,(st_receive "p" [|("success",sint,st_end)|]))|].

Lemma TWEqList: coseqInLC (act TW) ListT.
Proof. pfold.
       unfold TW, ListT.
       simpl.
       rewrite(coseq_eq(act ("p" & [|("success", I, "q" ! [|("cont", I, st_end)|])|]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq(act ("q" ! [|("cont", I, end)|]))).
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
       rewrite(coseq_eq(act ("q" ! [|("cont", I, "p" & [|("success", I, end)|])|]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq(act ("p" & [|("success", I, end)|]))).
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
       ((cocons ("p", rcv) (act ("q" ! [|("cont", I, end)|]))))
       ("p", rcv) (act ("q" ! [|("cont", I, end)|]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("q" ! [|("cont", I, end)|]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("q", snd)
       ((cocons ("q", snd) (act (end))))
       ("q", snd) (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act ("q" ! [|("cont", I, end)|]))))
       ("p", rcv) (act ("q" ! [|("cont", I, end)|]))
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
       ((cocons ("q", snd) (act ("p" & [|("success", I, end)|]))))
       ("q", snd) (act ("p" & [|("success", I, end)|]))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("p", rcv)
       ((cocons ("q", snd)(act ("p" & [|("success", I, end)|]))))
       ("q", snd) (act ("p" & [|("success", I, end)|]))
       ); intro Ha. 
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("p" & [|("success", I, end)|]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma st1: subtype T' T.
Proof. unfold subtype.
       assert(singleton(st_send "q" [|("cont",sint,(st_receive "p" [|("success",sint,st_end)|]))|])) as Hs1.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_receive "p" [|("success", sint,(st_send "q" [|("cont", sint, st_end)|]))|])) as Hs2.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_send "q" [|("cont",sint,(st_receive "p" [|("error",sbool,st_end)|]))|])) as Hs3.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_receive "p" [|("error",sbool,(st_send "q" [|("cont",sint,st_end)|]))|])) as Hs4.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_send "q" [|("stop",sunit,(st_receive "p" [|("success",sint,st_end)|]))|])) as Hs5.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_receive "p" [|("success",sint,(st_send "q" [|("stop",sunit,st_end)|]))|])) as Hs6.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_send "q" [|("stop",sunit,(st_receive "p" [|("error",sbool,st_end)|]))|])) as Hs7.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       assert(singleton(st_receive "p" [|("error",sbool,(st_send "q" [|("stop",sunit,st_end)|]))|])) as Hs8.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }

       exists([((mk_siso (st_send "q" [|("cont",sint,(st_receive "p" [|("success",sint,st_end)|]))|]) Hs1),
                    (mk_siso(st_receive "p" [|("success", sint,(st_send "q" [|("cont", sint, st_end)|]))|]) Hs2));
                (mk_siso (st_send "q" [|("cont",sint,(st_receive "p" [|("error",sbool,st_end)|]))|]) Hs3,
                    (mk_siso (st_receive "p" [|("error",sbool,(st_send "q" [|("cont",sint,st_end)|]))|]) Hs4));
                (mk_siso (st_send "q" [|("stop",sunit,(st_receive "p" [|("success",sint,st_end)|]))|]) Hs5, 
                    (mk_siso (st_receive "p" [|("success",sint,(st_send "q" [|("stop",sunit,st_end)|]))|]) Hs6));
                (mk_siso (st_send "q" [|("stop",sunit,(st_receive "p" [|("error",sbool,st_end)|]))|]) Hs7,
                     (mk_siso (st_receive "p" [|("error",sbool,(st_send "q" [|("stop",sunit,st_end)|]))|]) Hs8))
              ]).
       simpl. split. split.
       
       pcofix H.
       pfold.
       simpl. rewrite(st_eq T'). simpl.
       apply st2siso_snd with (y := "p" & [|("success", I, end); ("error", B, end)|]). simpl.
       left. pfold.
       apply st2siso_rcv with (y := end). simpl.
       left. pfold. constructor.
       constructor.
       constructor.
       split.

       pcofix H.
       pfold.
       simpl. rewrite(st_eq T). simpl.
       apply st2siso_rcv with (y :=  "q" ! [|("cont", I, end); ("stop", (), end)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := end). simpl.
       left. pfold. constructor.
       constructor.
       constructor.

       split. 
       pfold. rewrite(st_eq T'). simpl.
       apply st2siso_snd with (y := "p" & [|("success", I, end); ("error", B, end)|]). simpl.
       constructor.
       pfold.
       apply st2siso_rcv with (y := end). simpl.
       constructor. simpl.
       pfold. constructor.
       constructor. easy.
       constructor. 
       constructor.
       
       split.
       pfold. rewrite(st_eq T). simpl.
       apply st2siso_rcv with (y :=  "q" ! [|("cont", I, end); ("stop", (), end)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := end). simpl.
       left. pfold. constructor.
       constructor.
       constructor. easy.
       constructor.

       split. 
       pfold. rewrite(st_eq T'). simpl.
       apply st2siso_snd with (y := "p" & [|("success", I, end); ("error", B, end)|]). simpl.
       constructor.
       pfold.
       apply st2siso_rcv with (y := end). simpl.
       constructor. simpl.
       pfold. constructor.
       constructor.
       constructor. easy.
       constructor. 
       
       split.
       pfold. rewrite(st_eq T). simpl.
       apply st2siso_rcv with (y :=  "q" ! [|("cont", I, end); ("stop", (), end)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := end). simpl.
       left. pfold. constructor.
       constructor. easy.
       constructor. 
       constructor.

       split. 
       pfold. rewrite(st_eq T'). simpl.
       apply st2siso_snd with (y := "p" & [|("success", I, end); ("error", B, end)|]). simpl.
       constructor.
       pfold.
       apply st2siso_rcv with (y := end). simpl.
       constructor. simpl.
       pfold. constructor.
       constructor. easy.
       constructor.
       constructor. easy.
       constructor.

       split.
       pfold. rewrite(st_eq T). simpl.
       apply st2siso_rcv with (y :=  "q" ! [|("cont", I, end); ("stop", (), end)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := end). simpl.
       left. pfold. constructor.
       constructor. easy.
       constructor. 
       constructor. easy.
       constructor. easy.

       split.
       exists dpf_end. exists dpf_end. intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       pcofix CIH.
       pfold.
       specialize (ref_b (upaco2 refinementR r)
                           (st_receive "p" [|("success", sint, st_end)|])
                           st_end
                           "q" "cont" sint sint
                           (bp_receivea "p" "success" sint) 1
                           ); intro H.
       simpl in H.

       rewrite(st_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) ("q" ! [|("cont", I, end)|])))) in H.
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

       rewrite(coseq_eq(act ("p" & [|("success", I, end)|]))).
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
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor. split.

       rewrite(st_eq(merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end))).
       simpl.
       rewrite(coseq_eq(act ("p" & [|("success", I, end)|]))).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor.
       easy.
       
       split.
       exists dpf_end. exists dpf_end. intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       pcofix CIH.
       pfold.
       specialize (ref_b (upaco2 refinementR r)
                           (st_receive "p" [|("error", sbool, st_end)|])
                           st_end
                           "q" "cont" sint sint
                           (bp_receivea "p" "error" sbool) 1
                           ); intro H.
       simpl in H.

       rewrite(st_eq ((merge_bp_cont "q" (bp_receivea "p" "error" (B)) ("q" ! [|("cont", I, end)|])))) in H.
       simpl in H.
       apply H.
       apply srefl. (*subsort*)
       simpl.
       left. pfold.
       rewrite(st_eq  (merge_bp_cont "q" (bp_receivea "p" "error" (B)) (end))).
       simpl. 
       specialize(ref_a (upaco2 refinementR r)  (end) (end) "p" "error" (B) (B) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA.
       constructor.
       left. pfold. constructor.
       
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
       
       exists [("p",rcv)].
       exists [("p",rcv)].
       split.
       pfold.
       rewrite (coseq_eq(act ("p" & [|("error", B, end)|]))). simpl.
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.

       unfold upaco2.
       left.
       rewrite(coseq_eq(act (end))).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.

       split.
       pfold.
       rewrite(coseq_eq(act (merge_bp_cont "q" (bp_receivea "p" "error" (B)) (end)))).
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
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       rewrite(coseq_eq(act ("p" & [|("error", B, end)|]))). unfold coseq_id. simpl.
       apply Ha.
       simpl. easy. easy.
       constructor. split.

       rewrite(st_eq(merge_bp_cont "q" (bp_receivea "p" "error" (B)) (end))).
       simpl.
       rewrite(coseq_eq(act ("p" & [|("error", B, end)|]))).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor.
       easy.
       
       split.
       exists dpf_end. exists dpf_end. intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       pcofix CIH.
       pfold.
       specialize (ref_b (upaco2 refinementR r)
                           (st_receive "p" [|("success", sint, st_end)|])
                           st_end
                           "q" "stop" sunit sunit
                           (bp_receivea "p" "success" sint) 1
                           ); intro H.
       simpl in H.

       rewrite(st_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) ("q" ! [|("stop", (), end)|])))) in H.
       simpl in H.
       apply H.
       apply srefl. (*subsort*)
       simpl.
       left. pfold.
       rewrite(st_eq (merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end))).
       simpl. 
       specialize(ref_a (upaco2 refinementR r)  (end) (end) "p" "success" (I) (I) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA.
       constructor.
       left. pfold. constructor.
       
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
       


       exists [("p",rcv)].
       exists [("p",rcv)].
       split.
       pfold.
       rewrite (coseq_eq(act ("p" & [|("success", I, end)|]))). simpl.
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.

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
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       rewrite(coseq_eq(act ("p" & [|("success", I, end)|]))). unfold coseq_id. simpl.
       apply Ha.
       simpl. easy. easy.
       constructor. split.

       rewrite(st_eq(merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end))).
       simpl.
       rewrite(coseq_eq(act ("p" & [|("success", I, end)|]))).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor.
       easy.

       
       split.
       exists dpf_end. exists dpf_end. intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       pcofix CIH.
       pfold.
       specialize (ref_b (upaco2 refinementR r)
                           (st_receive "p" [|("error", sbool, st_end)|])
                           st_end
                           "q" "stop" sunit sunit
                           (bp_receivea "p" "error" sbool) 1
                           ); intro H.
       simpl in H.

       rewrite(st_eq  (merge_bp_cont "q" (bp_receivea "p" "error" (B)) ("q" ! [|("stop", (), end)|]))) in H.
       simpl in H.
       apply H.
       apply srefl. (*subsort*)
       simpl.
       left. pfold.
       rewrite(st_eq (merge_bp_cont "q" (bp_receivea "p" "error" (B)) (end))).
       simpl. 
       specialize(ref_a (upaco2 refinementR r)  (end) (end) "p" "error" (B) (B) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA.
       constructor.
       left. pfold. constructor.
       
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
       
       exists [("p",rcv)].
       exists [("p",rcv)].
       split.
       pfold.
       rewrite (coseq_eq(act ("p" & [|("error", B, end)|]))). simpl.
       unfold coseq_id. simpl.
       constructor. simpl. left. easy.

       unfold upaco2.
       left.
       rewrite(coseq_eq(act (end))).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.

       split.
       pfold.
       rewrite(coseq_eq(act (merge_bp_cont "q" (bp_receivea "p" "error" (B)) (end)))).
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
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       rewrite(coseq_eq(act ("p" & [|("error", B, end)|]))). unfold coseq_id. simpl.
       apply Ha.
       simpl. easy. easy.
       constructor. split.

       rewrite(st_eq(merge_bp_cont "q" (bp_receivea "p" "error" (B)) (end))).
       simpl.
       rewrite(coseq_eq(act ("p" & [|("error", B, end)|]))).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("p", rcv)
       ((cocons ("p", rcv) (act (end))))
       ("p", rcv) (act (end))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       constructor.
       easy.
       easy.
Qed.

Lemma lT'2T': lt2st lT' = T'.
Proof. apply stExt.
       unfold lT'.
       rewrite (st_eq T'). simpl.
       pfold.
       rewrite(st_eq((lt2st (lt_send "q"
        [("cont", I, lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)]);
         ("stop", (), lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)])])))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                          match xs with
                          | [] => [||]
                          | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                          end)
                         [("cont", I, lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)]);
                          ("stop", (), lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)])])). simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("stop", (), lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)])]))). simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) []))). simpl.
       constructor.
       constructor.
       exists "cont". exists (I). exists (lt2st (lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)])).
       exists "cont". exists (I). exists("p" & [|("success", I, end); ("error", B, end)|]).
       split. easy. split. easy. split. easy. split. easy.
       left.
       pfold.
       rewrite(st_eq(lt2st (lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
          match xs with
          | [] => [||]
          | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
          end) [("success", I, lt_end); ("error", B, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
         match xs with
         | [] => [||]
         | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
         end) [("error", B, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
            match xs with
            | [] => [||]
            | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "success". exists (I). exists(end).
       exists "success". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "error". exists (B). exists(end).
       exists "error". exists (B). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       
       constructor.
       exists "stop". exists (()). exists( lt2st (lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)])).
       exists "stop". exists (()). exists("p" & [|("success", I, end); ("error", B, end)|]).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold.
       rewrite(st_eq(lt2st (lt_receive "p" [("success", I, lt_end); ("error", B, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
            match xs with
            | [] => [||]
            | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
            end) [("success", I, lt_end); ("error", B, lt_end)])). simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("error", B, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
            match xs with
            | [] => [||]
            | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "success". exists (I). exists(end).
       exists "success". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "error". exists (B). exists(end).
       exists "error". exists (B). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
Qed.

Lemma lT2T: lt2st lT = T.
Proof. apply stExt.
       unfold lT.
       rewrite (st_eq T). simpl.
       rewrite(st_eq(lt2st (lt_receive "p"
        [("success", I, lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)]); ("error", B, lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)])]))).
       simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                      match xs with
                      | [] => [||]
                      | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                      end) [("success", I, lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)]); ("error", B, lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
         match xs with
         | [] => [||]
         | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
         end) [("error", B, lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
            match xs with
            | [] => [||]
            | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
            end) [])). simpl.
       pfold. constructor.
       constructor.
       exists "success". exists (I). exists(lt2st (lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)])).
       exists "success". exists (I). exists("q" ! [|("cont", I, end); ("stop", (), end)|]).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold.
       rewrite(st_eq(lt2st (lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
        match xs with
        | [] => [||]
        | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
        end) [("cont", I, lt_end); ("stop", (), lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("stop", (), lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "cont". exists (I). exists(end).
       exists "cont". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "stop". exists (()). exists(end).
       exists "stop". exists (()). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       
       constructor.
       exists "error". exists (B). exists(lt2st (lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)])).
       exists "error". exists (B). exists("q" ! [|("cont", I, end); ("stop", (), end)|]).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold.
       rewrite(st_eq(lt2st (lt_send "q" [("cont", I, lt_end); ("stop", (), lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
        match xs with
        | [] => [||]
        | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
        end) [("cont", I, lt_end); ("stop", (), lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("stop", (), lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "cont". exists (I). exists(end).
       exists "cont". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       rewrite(st_eq(lt2st lt_end)). simpl.
       exists "stop". exists (()). exists(end).
       exists "stop". exists (()). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
Qed.

Lemma lT'_lT: subltype lT' lT.
Proof. unfold subltype.
       rewrite lT'2T' lT2T.
       exact st1.
Qed. 



