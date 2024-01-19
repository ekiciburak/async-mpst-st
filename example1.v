From ST Require Import stream st so si reordering siso refinement reorderingfacts subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Pred_Type  Coq.Logic.ClassicalFacts.

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

Definition ListT := [("q","!");("p","?")]. 

Definition TW  := st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))].
Definition TW' := st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))].

Lemma TWEqList: cosetIncLC (act TW) ListT.
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

Lemma TW'EqList: cosetIncLC (act TW') ListT.
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

Lemma TWEqListR: cosetIncR ListT (act TW).
Proof. rewrite(coseq_eq(act TW)).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit2 ("q", "!")
       (Delay(cocons ("p", "?") (act ("q" ! [("cont", I, end)]))))
       ("p", "?") (act ("q" ! [("cont", I, end)]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("q" ! [("cont", I, end)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("q", "!")
       (Delay(cocons ("q", "!") (act (end))))
       ("q", "!") (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       specialize(CoInSplit1 ("p", "?")
       (Delay(cocons ("p", "?") (act ("q" ! [("cont", I, end)]))))
       ("p", "?") (act ("q" ! [("cont", I, end)]))
       ); intro Hb.
       constructor.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

Lemma TWEqListR': cosetIncR ListT (act TW').
Proof. rewrite(coseq_eq(act TW')).
       unfold coseq_id.
       simpl.
       constructor.
       specialize(CoInSplit1 ("q", "!")
       (Delay(cocons ("q", "!") (act ("p" & [("success", I, end)]))))
       ("q", "!") (act ("p" & [("success", I, end)]))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("p", "?")
       (Delay(cocons ("q", "!")(act ("p" & [("success", I, end)]))))
       ("q", "!") (act ("p" & [("success", I, end)]))
       ); intro Ha. 
       apply Ha.
       simpl. easy. easy.

       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("p", "?")
       (Delay(cocons ("p", "?") (act (end))))
       ("p", "?") (act (end))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       constructor.
Qed.

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

       assert(singleton(st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))])) as Hs1.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       
       exists(mk_siso (st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))]) Hs1).
       split.
(*        symmetry. *)
       pcofix H.
       pfold.
       simpl in *.
       specialize(st2siso_snd (upaco2 st2siso r) "cont" sint 
                              (st_receive "p" [("success", sint, st_end)])
                              U
                              [("cont", sint, st_receive "p" [("success", sint, st_end)])]
                              "q"); intro H2.

       apply H2.
       simpl. left. easy.
       unfold upaco2.
       right. easy.

       assert(singleton(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))])) as Hs2.
       { pfold. constructor. left. pfold. constructor. left. pfold. constructor. }
       exists(mk_siso(st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))]) (Hs2)).

       split.
(*        symmetry. *)
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
                           (bp_receivea "p" "success" sint) 1
                           ); intro H.
       simpl in H.
      
       rewrite(siso_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) ("q" ! [("cont", I, end)])))) in H.
       simpl in H.
       apply H.

       apply srefl. (*subsort*)

       rewrite (siso_eq ((merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end)))).
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

       unfold act_eq.
       intros (p, s).
       split.
       intro Ha.
       unfold CoIn in Ha.
       punfold Ha.
       inversion Ha.
       subst.
       simpl in H0.
       inversion H0.
       rewrite(coseq_eq(act (merge_bp_cont "q" (bp_receivea "p" "success" (I)) (end)))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act (end))). simpl. easy.
       subst.
       simpl in H0.
       inversion H0.
       subst.
       unfold upaco2 in H2.
       destruct H2.
       punfold H2.
       inversion H2.
       subst. simpl in H3. easy.
       simpl in *.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.

       intro Ha.
       unfold CoIn in Ha.
       punfold Ha.
       inversion Ha.
       subst.
       simpl in H0.
       inversion H0.
       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act (end))). simpl. easy.
       subst.
       simpl in H0.
       inversion H0.
       subst.
       unfold upaco2 in H2.
       destruct H2.
       punfold H2.
       inversion H2.
       subst. simpl in H3. easy.
       simpl in *.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.
