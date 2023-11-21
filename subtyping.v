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
                           (bp_receivea "p" "success" sint) 1); intro H.
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
Qed.
(*     (** do not remove: below code proves sameness of actor for this specific case  *)
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
*)

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

(* Lemma rOut: forall n p l s, 
  (p & [(l, s, merge_bp_cont p (Bpn p (bp_receivea p l s) n) W)])
  ==~
  (merge_bp_cont p (Bpn p (bp_mergea  p l s (bp_receivea p l s)) n) (p & [(l, s, W)])).
Proof. intro n.
       induction n; intros.
       - simpl.
         rewrite(siso_eq (merge_bp_cont p bp_end W)).
         simpl.
         rewrite (siso_eq (merge_bp_cont p bp_end (p & [(l, s, W)]))).
         simpl.
       pcofix CIH. *)

(* Lemma inOut: forall n,
  ("p" & [("l1", I, merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) W1)])
  ==~
  (merge_bp_cont "p" (Bpn "p" (bp_mergea "p" "l1" (I) (bp_receivea "p" "l1" (I))) n) ("p" ! [("l3", I, W1)])).
Proof. intro n.
       induction n; intros.
       - simpl.
         rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))).
         simpl.
   *)
Lemma W1W3Unf: forall n,
  ev n ->
  (forall r, r W3 (merge_bp_contn "p" (bp_receivea "p" "l1" sint) W1 (S (S n)))) ->
  W3 ~<  merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" sint) n) W1.
Proof. intros n Hn0 Hn.
       induction Hn0.
       - simpl in *.
(*        induction n; intros.
       - simpl. *)
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
(*          rewrite(siso_eq W1).
         simpl. *)
         specialize(_sref_b (upaco2 refinementR r)
                            ("p" ! [("l3", I, W3)])
                            W1
                            "p"
                            "l3"
                            (I)
                            (I)
                            (bp_receivea "p" "l1" (I))
                            1
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
        rewrite(siso_eq ((merge_bp_cont "p" (bp_receivea "p" "l1" (I))
                                            (merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)))) in Hn.
        simpl in Hn.
        rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" (I)) W1)) in Hn.
        simpl in Hn.
        rewrite(siso_eq W1) in Hn.
        simpl in Hn.
        apply Hn.

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
                   ); intro Hb.
         assert(merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" & [("l1", I, "p" ! [("l3", I, W1)])])
                 =
                merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) (S n)) ("p" ! [("l3", I, W1)])
               ).
         { simpl.
           rewrite(siso_eq(merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) n) ("p" & [("l1", I, "p" ! [("l3", I, W1)])]))).
           simpl.
           rewrite(siso_eq( merge_bp_cont "p" (bp_mergea "p" "l1" (I) (Bpn "p" (bp_receivea "p" "l1" (I)) n)) ("p" ! [("l3", I, W1)]))).
           simpl.
           induction n; intros.
           simpl.
           rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))).
           simpl.
           easy.
           
           admit.
         }
         rewrite H.
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
Qed.


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
 
       generalize dependent n.

      pcofix CIH.
      pfold.
      intro n.
      rewrite (siso_eq W3).
      rewrite (siso_eq W1).
      simpl.
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
        (bp_receivea "p" "l1" sint) 1
      ); intro H.

       rewrite (siso_eq ((merge_bp_cont "p" (Bpn "p" (bp_receivea "p" "l1" (I)) 1) ("p" ! [("l3", I, W1)])))) in H.
       simpl in H.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in H.
       simpl in H.
       rewrite (siso_eq W1).
       simpl.
       apply H.
       apply srefl.

       unfold upaco2.
       left.
       rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) W1)).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end W1)).
       simpl.
       pfold.
       specialize (_sref_b (upaco2 refinementR r1)
       W3
       W1
       "p" "l3" sint sint
       (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))
       1
       ); intro Hc.

       rewrite (siso_eq 
        (merge_bp_cont "p" (Bpn "p" (bp_mergea "p" "l1" (I) (bp_receivea "p" "l1" (I))) 1)
          ("p" ! [("l3", I, W1)])))
       in Hc.
       simpl in Hc.
       rewrite (siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" (I) bp_end) ("p" ! [("l3", I, W1)]))) in Hc.
       simpl in Hc.
       rewrite (siso_eq W1).
       simpl.
       rewrite(siso_eq(merge_bp_cont "p" bp_end ("p" ! [("l3", I, W1)]))) in Hc.
       simpl in Hc.
       rewrite(siso_eq W1) in Hc.
       simpl in Hc.
       apply Hc.
       apply srefl.

Admitted.
(*
       rewrite (siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)) W1)).
       simpl.
       rewrite (siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
       simpl.

       unfold upaco2.
       left. (*here*)
       pcofix CIH4.
       pfold.
       rewrite(siso_eq W3).
       simpl.

      specialize (_sref_in (upaco2 refinementR r2)
      (st_send "p" [("l3", sint, st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])])
      (st_receive "p" [("l1", sint, W1)])
      "p" "l1" sint sint
      ); intro Hd.
      apply Hd.
      apply srefl.
      unfold upaco2.
      left.
      rewrite(siso_eq W1).
      simpl.
(*       pcofix CIH6. *)

      specialize (_sref_b (upaco2 refinementR r2)
        (st_send "p" [("l3", sint, st_send "p" [("l3", sint, W3)])])
        W1
        "p" "l3" sint sint
       (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))
       1
      ); intro He.
      rewrite(siso_eq (merge_bp_contn "p"
                      (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))
                      (st_send "p" [("l3", sint, W1)]) 1) ) in He.
      simpl  in He.
      rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) 
             (st_send "p" [("l3", sint, W1)]))) in He.
      simpl in He.
      pfold.
      apply He.
      apply srefl.
      rewrite (siso_eq (merge_bp_cont "p" 
                       (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)) W1)).
      simpl.
      rewrite (siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
      simpl.
      
      unfold upaco2.
      left.
(*       pcofix CIH8. *)
      pfold.
      specialize (_sref_b (upaco2 refinementR r2)
        (st_send "p" [("l3", sint, W3)])
        W1
        "p" "l3" sint sint
       (bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)))
       1
      ); intro Hf.
      rewrite(siso_eq (merge_bp_contn "p" (bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)))
          (st_send "p" [("l3", sint, W1)]) 1)) in Hf.
      simpl in Hf.
      rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))
              (st_send "p" [("l3", sint, W1)]))) in Hf.
      simpl in Hf.
      rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) (st_send "p" [("l3", sint, W1)]))) in Hf.
      simpl in Hf.
      rewrite(siso_eq W1).
      simpl.
      apply Hf.
      apply srefl.
      unfold upaco2.
      left.

      rewrite (siso_eq  (merge_bp_cont "p" (bp_mergea "p" "l1" sint 
       (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))) W1)).
      simpl.
      rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" sint
                      (bp_receivea "p" "l1" sint)) W1)).
      simpl.
      rewrite(siso_eq(merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
      simpl.
(*       pcofix CIH10. *)
      pfold.
      
      specialize (_sref_b (upaco2 refinementR r2)
        W3
        W1
        "p" "l3" sint sint
       (bp_mergea "p" "l1" sint(bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint 
       (bp_receivea "p" "l1" sint))))
       1
      ); intro Hg.
      rewrite(siso_eq (merge_bp_contn "p"
          (bp_mergea "p" "l1" sint
             (bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))))
          (st_send "p" [("l3", sint, W1)]) 1)) in Hg.
      simpl in Hg.
      rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)))
              (st_send "p" [("l3", sint, W1)]))) in Hg.
      simpl in Hg.
      rewrite(siso_eq(merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))
                  (st_send "p" [("l3", sint, W1)]))) in Hg.
      simpl in Hg.
      rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) (st_send "p" [("l3", sint, W1)]))) in Hg.
      simpl in Hg.
      rewrite (siso_eq W1).
      simpl.
      apply Hg.
      apply srefl.
      rewrite(siso_eq (merge_bp_cont "p"
        (bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint (bp_mergea "p" "l1" sint
        (bp_receivea "p" "l1" sint)))) W1)).
      simpl.
      rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" sint 
                      (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint))) W1)).
      simpl.
      rewrite(siso_eq (merge_bp_cont "p" (bp_mergea "p" "l1" sint (bp_receivea "p" "l1" sint)) W1)).
      simpl.
      rewrite(siso_eq (merge_bp_cont "p" (bp_receivea "p" "l1" sint) W1)).
      simpl.
      unfold upaco2.
      left.
      specialize(W1W3Unf2 r2); intro HR.
      apply HR.
      specialize(W1W3Unf1); intro HP.
      apply HP.
      apply CIH5, CIH1, CIH0.
      apply CIH.
Qed.
*)

