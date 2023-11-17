From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
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
       symmetry.
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
       symmetry.
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
                           (bp_receivea "p" "success" sint)); intro H.
       rewrite(siso_eq (merge_bp_cont "q" (bp_receivea "p" "success" sint) (st_send "q" [("cont", sint, st_end)]))) in H.
       simpl in H.
       apply H.

       apply srefl. (*subsort*)

       rewrite (siso_eq (merge_bp_cont "q" (bp_receivea "p" "success" sint) st_end)).
       simpl.
       unfold upaco2.
       left.
       pfold.
       apply _sref_in.

       apply srefl. (*subsort*)

       unfold upaco2.
       left.
       pfold.
       apply _sref_end.

       rewrite (siso_eq (merge_bp_cont "q" (bp_receivea "p" "success" sint) st_end)).
       simpl.

       rewrite (coseq_eq (act (st_receive "p" [("success", sint, st_end)]))).
       unfold coseq_id.
       simpl.

       pfold.
       constructor.
       unfold upaco2.
       left.
       pcofix CIH2.
       rewrite(coseq_eq (act st_end)).
       unfold coseq_id.
       simpl.
       pfold.
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

CoFixpoint W1: st := st_receive "p" [("l1",sint,st_send "p" [("l3",sint,W1)])].
  
Lemma st2: subtype TB TB'.
Proof. unfold subtype.
       intro U.
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
       Search Forall.
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
       symmetry.
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
       symmetry.
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
       
      rewrite (siso_eq W3).
      rewrite (siso_eq W1).
      simpl.
      pcofix CIH.
      pfold.
      specialize (_sref_in (upaco2 refinementR r)
      (st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])])
      (st_send "p" [("l3", sint, W1)])
      "p" "l1" sint sint
      ); intro Ha.
      apply Ha.
      apply srefl.
      
      unfold upaco2.
      left.
      pcofix CIH2.
      pfold.
      specialize (_sref_out (upaco2 refinementR r0)
      (st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])
      W1
      "p" "l3" sint sint
      ); intro Hb.
      apply Hb.
      apply srefl.

      unfold upaco2.
      left.
      pcofix CIH3.
      pfold.
      specialize (_sref_b (upaco2 refinementR r1)
        (st_send "p" [("l3", sint, W3)])
        W1
        "p" "l3" sint sint
        (bp_receivea "p" "l1" sint)
      ); intro H.

       rewrite (siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) 
                                           (st_send "p" [("l3", sint, W1)]))) in H.
       simpl in H.
       rewrite (siso_eq W1).
       simpl.
       apply H.
      apply srefl.

       unfold upaco2.
       left.
       rewrite(siso_eq  (merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
       simpl.

       pfold.
       specialize (_sref_b (upaco2 refinementR r1)
       W3
       W1
       "p" "l3" sint sint
       (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))
       ); intro Hc.
       rewrite (siso_eq 
        (merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)) (st_send "p" [("l3", sint, W1)])))
       in Hc.
       simpl in Hc.
       rewrite (siso_eq
       (merge_bp_cont "p" (bp_receivea "p" "l1" sint) (st_send "p" [("l3", sint, W1)]))) in Hc.
       simpl in Hc.
       rewrite (siso_eq W1).
       simpl.
       apply Hc.
       apply srefl.
       rewrite (siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)) W1)).
       simpl.
       rewrite (siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
       simpl.
       unfold upaco2.
       right.

       rewrite (siso_eq W3).
       simpl.
       apply CIH1, CIH0.
       admit.

       rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)) W1)).
       simpl.
       rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
       simpl.
       pcofix CIH4.
       rewrite(coseq_eq (act W3)).
       rewrite(coseq_eq ((act (st_receive "p" [("l1", sint, st_receive "p" [("l1", sint, W1)])])))).
       unfold coseq_id.
       simpl.
       rewrite(coseq_eq (act W3)) in CIH4.
       rewrite(coseq_eq ((act (st_receive "p" [("l1", sint, st_receive "p" [("l1", sint, W1)])])))) in CIH4.
       unfold coseq_id in CIH4.
       simpl in CIH4.
       pfold.
       constructor.
       unfold upaco2.
       right.
       rewrite(coseq_eq (act (st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])]))).
       rewrite(coseq_eq (  (act (st_receive "p" [("l1", sint, W1)])))).
       unfold coseq_id.
       simpl. 
Admitted.


