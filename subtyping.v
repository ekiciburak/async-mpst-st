From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
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

Definition ListT := [("q","!");("p","?")]. 

Definition TW  := st_receive "p" [("success", sint,(st_send "q" [("cont", sint, st_end)]))].
Definition TW' := st_send "q" [("cont",sint,(st_receive "p" [("success",sint,st_end)]))].

Lemma TWEqList: cosetInclC (act TW) ListT.
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

Lemma TW'EqList: cosetInclC (act TW') ListT.
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
                           (bp_receivea "p" "success" sint) 1
                           [("p","?")]
                           ); intro H.
       rewrite(siso_eq ((merge_bp_cont "q" (Bpn "q" (bp_receivea "p" "success" (I)) 1)
         ("q" ! [("cont", I, end)])))) in H.
       simpl in H.
       rewrite(siso_eq(merge_bp_cont "q" bp_end ("q" ! [("cont", I, end)]))) in H.
       simpl in H.
       apply H.

       apply srefl. (*subsort*)

       rewrite (siso_eq (merge_bp_cont "q" (bp_mergea "p" "success" (I) bp_end) (end))).
       simpl.
       unfold upaco2.
       left.
       pfold.
       apply _sref_in.

       apply srefl. (*subsort*)

       unfold upaco2.
       left.
       pfold.
       rewrite(siso_eq (merge_bp_cont "q" bp_end (end))).
       simpl.
       apply _sref_end.
       
       rewrite(coseq_eq(act ("p" & [("success", I, end)]))).
       unfold coseq_id.
       simpl.
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

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS: forall n : nat, ev n -> ev (S (S n)).

Definition listW3 := [("p","?"); ("p","!")].

Lemma W3EqList: cosetInclC (act W3) listW3.
Proof. pcofix CIH.
       pfold.
       rewrite(siso_eq W3).
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

Lemma W1EqList: cosetInclC (act W1) listW3.
Proof. pcofix CIH.
       pfold.
       rewrite(siso_eq W1).
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

Lemma helper: forall n W,
  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" & [("l1", I, "p" ! [("l3", I, W)])])
                 =
  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) (S n)) ("p" ! [("l3", I, W)]).
Proof. intro n.
       induction n; intros.
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W)]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" & [("l1", I, "p" ! [("l3", I, W)])]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W)]))).
       simpl.
       easy.

       simpl in *.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" & [("l1", I, "p" ! [("l3", I, W)])]))).
       simpl.
       rewrite IHn.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) ("p" ! [("l3", I, W)]))).
       simpl.
       easy.
Qed.

Lemma W1W3Unf: forall n,
  ev n ->
  (forall r, r W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) (S (S n))) W1)) ->
  W3 ~<  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) n) W1.
Proof. intros n Hn0 Hn.
       induction Hn0.
       - simpl in *.
         rewrite(siso_eq (merge_bp_cont "p" bp_end W1)).
         simpl.
         pcofix CIH.
         pfold.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         apply _sref_out.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                            listW3
                            (*5 things here == !?!!!*)
(*                             (Delay (cocons ("p","!") 
                            (act W3)))
                            (*4 things here == ???!*)
                            (Delay (cocons ("p","&") (Delay (cocons ("p","!") (Delay conil))))) *)
                   ); intro Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         rewrite(siso_eq W1).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                            listW3
                   ); intro Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end))
          ("p" ! [("l3", I, W1)]))) in Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hc.
        apply Hc.
        apply srefl.
        rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
        simpl.
        rewrite(siso_eq ( merge_bp_cont "p" bp_end W1)).
        simpl.
        unfold upaco2.
        right.
        specialize(Hn r).
        simpl in Hn.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hn.
        simpl in Hn.
        apply Hn.
        
        apply W3EqList.
        pfold.
        rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
        unfold coseq_id.
        simpl.
        constructor.
        simpl. left. easy.
        
        unfold upaco2.
        left.
        pfold.
        rewrite(coseq_eq(act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
        unfold coseq_id.
        simpl.
        constructor.
        simpl. left. easy.
        unfold upaco2.
        left.
        pcofix CIHE.
        pfold.
        simpl.
        rewrite(siso_eq W1).
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
       apply CIHE.
       
       pfold.
       rewrite(coseq_eq (act ("p" ! [("l3", I, W3)]))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.
       
       unfold upaco2.
       left.
       pcofix CIHE.
       pfold.

       rewrite(siso_eq W3).
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
       apply CIHE.
       
       pfold.
       rewrite(coseq_eq((act (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)) )).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.

       unfold upaco2.
       left.
       pcofix CIHE.
       
       pfold.
       rewrite(siso_eq W1).
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
       apply CIHE.

(*         rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
        simpl.
        pcofix CCIH.
        pfold.
        rewrite(coseq_eq(act W3)).
        unfold coseq_id.
        simpl.
        rewrite(coseq_eq((act ("p" & [("l1", I, "p" & [("l1", I, W1)])])))).
        unfold coseq_id.
        simpl. *)

        simpl. simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p"
                       (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
        simpl.
        pcofix CIH.
        pfold.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq W1).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
                            listW3
                   ); intro Hb.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         simpl in Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1))).
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.

         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
                            listW3
                   ); intro Hc.
         simpl in Hc.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         apply Hc.
         apply srefl.
         
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))) W1))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+4)
                            listW3
                   ); intro Hd.
         simpl in Hd.
         rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I)
             (bp_mergea "p" "l1" (I)
                (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))))
          ("p" ! [("l3", I, W1)])))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
            (bp_mergea "p" "l1" (I)
               (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
            ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
              (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
              ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))
                ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         left.
         pfold.
         apply Hd.
         apply srefl.
         unfold upaco2.
         right.
         specialize(Hn r).
         simpl in Hn.
         easy.
         (* actor checks admitted -- to be done easily *)
Admitted.


Lemma W1W3UnfVar: forall n r,
  ev n ->
  r W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) (S (S n))) W1) ->
  paco2 refinementR r W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) n) W1).
Proof. intro n.
       induction n; intros.
       { simpl in *.
         pcofix CIH.
         pfold.
         rewrite(siso_eq (merge_bp_cont "p" bp_end W1)).
         simpl.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         apply _sref_out.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                            listW3
                   ); intro Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         rewrite(siso_eq W1).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                            listW3
                   ); intro Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end))
          ("p" ! [("l3", I, W1)]))) in Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hc.
        apply Hc.
        apply srefl.
        rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
        simpl.
        rewrite(siso_eq ( merge_bp_cont "p" bp_end W1)).
        simpl.
        unfold upaco2.
        right.
        rename H0 into Hn.
        simpl in Hn.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hn.
        simpl in Hn.
        apply Hn.
       }

        simpl.
        pcofix CIH.
        pfold.
        simpl. 
        rename H0 into Hn.
        simpl in *.

(*         rewrite(siso_eq(merge_bp_cont "p"
                       (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
        simpl. *)
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
        simpl.
(*         pcofix CIH.
        pfold. *)
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq W1).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+1)
                            listW3
                   ); intro Hb.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         simpl in Hb.
(*          rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb. *)
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         (*
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1))).
         simpl. *)
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.

         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
                            listW3
                   ); intro Hc.
         simpl in Hc.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
(*          rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc. *)
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         apply Hc.
         apply srefl.
         
(*          rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))) W1))).
         simpl. *)
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
                            listW3
                   ); intro Hd.
         simpl in Hd.
(*          rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I)
             (bp_mergea "p" "l1" (I)
                (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))))
          ("p" ! [("l3", I, W1)])))) in Hd.
         simpl in Hd. *)
         rewrite(siso_eq(merge_bp_cont "p"
            (bp_mergea "p" "l1" (I)
               (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
            ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
              (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
              ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))
                ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         left.
         pfold.
         apply Hd.
         apply srefl.
         unfold upaco2.
         right.
         simpl in Hn.
         easy.
         (* actor checks admitted -- tobe done easily *)
Admitted.


Lemma W1Unf: forall r, paco2 refinementR r ("p" & [("l1", I, "p" & [("l1", I, W1)])])
                                           ("p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, W1)])])])]).
(* "p" & [("l1", I, "p" & [("l1", I, W1)])] ~<
("p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, "p" & [("l1", I, W1)])])])]). *)
(* merge_bp_contn "p" (bp_receivea "p" "l1" sint) W1 2 ~< merge_bp_contn "p" (bp_receivea "p" "l1" sint) W1 4. *)
Proof. 
(*        simpl.
       rewrite (siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))))).
       simpl.
       rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                       (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                       (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))).
       simpl.
       rewrite (siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                        (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1))).
       simpl.
       rewrite (siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)).
       simpl.
        *)
       pcofix CIH.
       pfold.
       apply _sref_in.
       apply srefl.
       unfold upaco2.
       left.
       pfold.
       apply _sref_in.
       apply srefl.

       unfold upaco2.
       left.
       pcofix CIH2.
       pfold.

       setoid_rewrite(siso_eq W1) at 1.
       simpl.
       apply _sref_in.
       apply srefl.
       unfold upaco2.
       left.
       pfold.
       specialize (_sref_b (upaco2 refinementR r)
                           W1
                           W1
                           "p"
                           "l3" (I) (I)
                           (bp_receivea "p" "l1" sint)
                           2
                           listW3
       ); intro Ha.
       simpl in Ha.
       rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end))
          ("p" ! [("l3", I, W1)])))) in Ha.
       simpl in Ha.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)]))) in Ha.
       simpl in Ha.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Ha.
       simpl in Ha.
       setoid_rewrite(siso_eq W1) at 2.
       simpl.
       apply Ha.
       apply srefl.
       rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1)).
       simpl.
       rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
       simpl.
       rewrite(siso_eq( merge_bp_cont "p" bp_end W1)).
       simpl.
       unfold upaco2.
       right.
       setoid_rewrite(siso_eq W1) in CIH2 at 2.
       simpl in CIH2.
       apply CIH2.
      (* consider later: sameness of actors *)
Admitted.

Lemma W1W3UnfVar2: forall n r,
  ev n ->
  r W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) (S (S n))) W1) ->
  refinementR (upaco2 refinementR r) W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) n) W1).
Proof. intro n.
       induction n; intros.
       { simpl in *.
         rewrite(siso_eq W3).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         apply _sref_out.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                            listW3
                   ); intro Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         rewrite(siso_eq W1).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                            listW3
                   ); intro Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end))
          ("p" ! [("l3", I, W1)]))) in Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hc.
        apply Hc.
        apply srefl.
        rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
        simpl.
        rewrite(siso_eq ( merge_bp_cont "p" bp_end W1)).
        simpl.
        unfold upaco2.
        right.
        rename H0 into Hn.
        simpl in Hn.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hn.
        simpl in Hn.
        apply Hn.
       }
        simpl. 
        rename H0 into Hn.
        simpl in *.

(*         rewrite(siso_eq(merge_bp_cont "p"
                       (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
        simpl. *)
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
        simpl. 
(*         pcofix CIH.
        pfold. *)
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq W1).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+1)
                            listW3
                   ); intro Hb.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         simpl in Hb.
(*          rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb. *)
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         (*
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1))).
         simpl. *)
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.

         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
                            listW3
                   ); intro Hc.
         simpl in Hc.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
(*          rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc. *)
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         apply Hc.
         apply srefl.
         
(*          rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))) W1))).
         simpl. *)
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
                            listW3
                   ); intro Hd.
         simpl in Hd.
(*          rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I)
             (bp_mergea "p" "l1" (I)
                (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))))
          ("p" ! [("l3", I, W1)])))) in Hd.
         simpl in Hd. *)
         rewrite(siso_eq(merge_bp_cont "p"
            (bp_mergea "p" "l1" (I)
               (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
            ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
              (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
              ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))
                ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         left.
         pfold.
         apply Hd.
         apply srefl.
         unfold upaco2.
         right.
         simpl in Hn.
         easy.
Admitted.

Lemma W1W3UnfVar3: forall n r,
  ev n ->
  (upaco2 refinementR r) W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) (S (S n))) W1) ->
  refinementR (upaco2 refinementR r) W3 (merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) n) W1).
Proof. intro n.
       induction n; intros.
       { simpl in *.
         rewrite(siso_eq W3).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         apply _sref_out.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                            listW3
                   ); intro Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         rewrite(siso_eq W1).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                            listW3
                   ); intro Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end))
          ("p" ! [("l3", I, W1)]))) in Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hc.
        apply Hc.
        apply srefl.
        rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
        simpl.
        rewrite(siso_eq ( merge_bp_cont "p" bp_end W1)).
        simpl.
        rename H0 into Hn.
        simpl in Hn.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hn.
        simpl in Hn.
        unfold upaco2 in Hn.
        destruct Hn.
        unfold upaco2.
        left.
        easy.
        unfold upaco2.
        right.
        easy.
       }
        simpl. 
        rename H0 into Hn.
        simpl in *.

(*         rewrite(siso_eq(merge_bp_cont "p"
                       (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
        simpl. *)
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
        simpl. 
(*         pcofix CIH.
        pfold. *)
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq W1).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+1)
                            listW3
                   ); intro Hb.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         simpl in Hb.
(*          rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb. *)
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         (*
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1))).
         simpl. *)
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.

         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
                            listW3
                   ); intro Hc.
         simpl in Hc.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
(*          rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc. *)
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         apply Hc.
         apply srefl.
         
(*          rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))) W1))).
         simpl. *)
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
                            listW3
                   ); intro Hd.
         simpl in Hd.
(*          rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I)
             (bp_mergea "p" "l1" (I)
                (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))))
          ("p" ! [("l3", I, W1)])))) in Hd.
         simpl in Hd. *)
         rewrite(siso_eq(merge_bp_cont "p"
            (bp_mergea "p" "l1" (I)
               (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
            ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
              (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
              ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))
                ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         left.
         pfold.
         apply Hd.
         apply srefl.
         
         unfold upaco2 in Hn.
         destruct Hn as [Hn | Hn].
         unfold upaco2.
         left.
         easy.
         unfold upaco2.
         right.
         simpl in Hn.
         easy.
Admitted.

Lemma W1W3UnfVar4: forall n,
  ev n ->
  W3 ~<  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) n) W1.
Proof. intros.
       generalize dependent n.
       pcofix CIH.
       intros.
       induction H0; intros.
       simpl.

         rewrite(siso_eq (merge_bp_cont "p" bp_end W1)).
         simpl.
         pfold.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         apply _sref_out.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
                            listW3
                   ); intro Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         rewrite(siso_eq W1).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" bp_end W1)) in Hb.
         simpl in Hb.
         apply Hb.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1 
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" sint)
                            2
                            listW3
                   ); intro Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end))
          ("p" ! [("l3", I, W1)]))) in Hc.
        simpl in Hc.
        rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)])))
        in Hc. simpl in Hc.
        rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hc.
        apply Hc.
        apply srefl.
        rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1))).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
        simpl.
        rewrite(siso_eq ( merge_bp_cont "p" bp_end W1)).
        simpl.
        unfold upaco2.
        right.
        specialize(CIH 2).
        simpl in CIH.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) bp_end)) W1)) in CIH.
        simpl in CIH.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)) in CIH.
        simpl in CIH.
        rewrite(siso_eq( merge_bp_cont "p" bp_end W1)) in CIH.
        simpl in CIH.
        apply CIH.
        constructor.
        constructor.
        
        admit.
        admit.
        admit.
        admit.

        rename CIH into Hn.
        simpl. simpl in Hn.

        rewrite(siso_eq(merge_bp_cont "p"
                       (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
        simpl.
        rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
        simpl.
(*         pcofix CIH. *)
        pfold.
         rewrite(siso_eq W3).
         simpl.
         apply _sref_in.
         apply srefl.
         unfold upaco2.
         left.
         pfold.
         rewrite(siso_eq W1).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, "p" ! [("l3", I, W3)])])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+2)
                            listW3
                   ); intro Hb.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         simpl in Hb.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) 
         (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hb.
         simpl in Hb.
         simpl in *.
         apply Hb.
         apply srefl.
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1))).
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.

         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+3)
                            listW3
                   ); intro Hc.
         simpl in Hc.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq((merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
          ("p" ! [("l3", I, W1)])))) in Hc.
         simpl in Hc.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))) in Hc.
         simpl in Hc.
         unfold upaco2.
         left.
         pfold.
         apply Hc.
         apply srefl.
         
         rewrite(siso_eq(  (merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))) W1))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))) W1)).
         simpl.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) W1)).
         simpl.
         rewrite(siso_eq W1).
         simpl.
         rewrite helper.
         simpl.
         rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
         simpl.
         specialize(_sref_b (upaco2 refinementR r)
                            W3
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I)) 
                            (n.+4)
                            listW3
                   ); intro Hd.
         simpl in Hd.
         rewrite(siso_eq((merge_bp_cont "p"
          (bp_mergea "p" "l1" (I)
             (bp_mergea "p" "l1" (I)
                (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))))
          ("p" ! [("l3", I, W1)])))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
            (bp_mergea "p" "l1" (I)
               (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))))
            ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p"
              (bp_mergea "p" "l1" (I) (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)))
              ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n))
                ("p" ! [("l3", I, W1)]))) in Hd.
         simpl in Hd.
         left.
         pfold.
         apply Hd.
         apply srefl.
         unfold upaco2.
         right.
         specialize(Hn (n.+4)).
         simpl in Hn.
         apply Hn.
         constructor.
         constructor.
         easy.
Admitted.

Lemma st2: forall n: nat, subtype TB TB'.
Proof. unfold subtype.
       intros n U.
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

       specialize(W1W3UnfVar4 0); intros.
       rewrite(siso_eq(merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) 0) W1)) in H.
       simpl in H.
       rewrite(siso_eq W1).
       simpl.
       apply H.
       constructor.
Qed.
