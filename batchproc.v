From ST Require Import stream st so si siso subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List Coq.Arith.Even.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.


CoFixpoint Tctl := st_send "src" [("b1",sunit,st_receive "src" [("b1",sunit,
                                  st_receive "sk" [("b1",sunit,st_send "sk" [("b1",sunit,
                                  st_send "src" [("b2",sunit,st_receive "src" [("b2",sunit,
                                  st_receive "sk" [("b2",sunit,st_send "sk" [("b2",sunit,Tctl)])])])])])])])].
Print Tctl.

CoFixpoint TR := st_receive "src" [("b1",sunit,st_receive "sk" [("b1",sunit,
                                   st_send "sk" [("b1",sunit,st_send "src" [("b1",sunit,
                                   st_receive "src" [("b2",sunit,st_receive "sk" [("b2",sunit,
                                   st_send "sk" [("b2",sunit,st_send "src" [("b2",sunit,TR)])])])])])])])].
Print TR.

Definition Tctl' := st_send "src" [("b1",sunit,st_send "src" [("b2",sunit,TR)])].
Print Tctl'.

Definition listTctl := [("src","!");("src","?");("sk","!");("sk","?")].

Lemma listTctlEq: forall r, paco2 cosetIncL r (act Tctl) listTctl.
Proof. pcofix CIH.
       pfold.
       rewrite(coseq_eq(act Tctl)).
       unfold coseq_id.
       simpl.
       unfold listTctl.
       constructor.
       simpl. left. easy.
       rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk"! [("b1", (),
                              "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. right. left. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk"
                      ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. right. right. right. left. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. right. right. left. easy.
       rewrite(coseq_eq((act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. left. easy.
       rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. right. left. easy.
       rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. right. right. right. left. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), Tctl)])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. right. right. left. easy.
       unfold upaco2.
       right.
       unfold listTctl in CIH.
       apply CIH.
Qed.

Lemma listTREq: forall r, paco2 cosetIncL r (act TR) listTctl.
Proof. intros.
       pcofix CIH.
       unfold listTctl.
       rewrite(coseq_eq(act TR)).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.
       simpl. right. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" &
                                     [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. right. right. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. right. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. right. right. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. right. right. left. easy.
       unfold upaco2.
       left.
       pfold.
       rewrite(coseq_eq((act ("src" ! [("b2", (), TR)])))).
       unfold coseq_id.
       simpl.
       constructor.
       simpl. left. easy.
       unfold upaco2.
       right.
       unfold listTctl in CIH.
       apply CIH.
Qed.

Lemma listTctlEq': forall r, paco2 cosetIncL r (act Tctl') listTctl.
Proof. intros.
       unfold listTctl.
       rewrite(coseq_eq(act Tctl')).
       unfold coseq_id.
       simpl.
       pfold.
       constructor.
       simpl. left. easy.
       rewrite(coseq_eq((act ("src" ! [("b2", (), TR)])))).
       unfold coseq_id.
       simpl.
       unfold upaco2.
       left.
       pfold.
       constructor.
       simpl. left. easy.
       unfold upaco2.
       left.
       apply listTREq.
Qed.

Lemma stb: subtype Tctl' Tctl.
Proof. unfold subtype.
       intro U.
       split.
       pcofix CIH.
       pfold.
       rewrite(siso_eq Tctl'). simpl.
       specialize(st2so_snd (upaco2 st2so r)
                            "b1" sunit
                            ("src" ! [("b2", (), TR)])
                            U
                            ([("b1", (), "src" ! [("b2", (), TR)])])
                            "src"
                            ); intro Ha.
       apply Ha.
       simpl. left. easy.
       unfold upaco2.
       right.
       rewrite(siso_eq Tctl') in CIH. simpl in CIH.
       apply CIH.

       intro V'.
       split.
       pcofix CIH.
       pfold.
       rewrite(siso_eq Tctl). simpl.
       specialize(st2si_snd (upaco2 st2si r) 
                            "src" 
                            ["b1";"b1";"b1";"b1";"b2";"b2";"b2";"b2"]
                            [sunit;sunit;sunit;sunit;sunit;sunit;sunit;sunit]
                            V'
                            ([("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])
                            ([("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])
                            ); intro Ha.
       simpl in Ha.
       apply Ha.
       simpl.
       Search Forall.
       apply Forall_forall.
       intros(x1,x2) Hc.
       simpl.
       simpl in Hc.
       destruct Hc as [Hc | Hc].
       inversion Hc.
       unfold upaco2.
       left.
       pcofix CIH2.
       pfold.
       specialize(st2si_rcv (upaco2 st2si r0)
                            "b1" 
                            sunit
                            ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])] )
                            ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])
                            ([("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])
                            "src"
                            ); intros Hd.
       apply Hd.
       simpl. left. easy.
       unfold upaco2.
       right.
       apply CIH2.
       easy.
       rewrite(siso_eq Tctl) in CIH. simpl in CIH.
       unfold upaco2.
       right.
       apply CIH.

       exists Tctl'.
       split.
       symmetry.
       pcofix CIH.
       pfold.
       rewrite(siso_eq Tctl'). simpl.
       specialize(st2siso_snd (upaco2 st2siso r) 
                              "b1" sunit
                              ("src" ! [("b2", (), TR)])
                              U
                              ([("b1", (), "src" ! [("b2", (), TR)])])
                              "src"
                              ); intro Ha.
       apply Ha.
       simpl. left. easy.
       unfold upaco2.
       right.
       rewrite(siso_eq Tctl') in CIH. simpl in CIH.
       apply CIH.
       
       exists Tctl.
       split.
       symmetry.
       pcofix CIH.
       pfold.
       rewrite(siso_eq Tctl). simpl.
       specialize(st2siso_snd (upaco2 st2siso r) 
                              "b1" sunit
                              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])
                              V'
                              ([("b1", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])
                              "src"
                              ); intro Ha.
       apply Ha.
       simpl. left. easy.
       unfold upaco2.
       right.
       rewrite(siso_eq Tctl) in CIH. simpl in CIH.
       apply CIH.

       rewrite(siso_eq Tctl').
       rewrite(siso_eq Tctl). simpl.
       pfold.
       constructor.
       apply srefl.
       unfold upaco2.
       left.
       pcofix CIH.
       pfold.
       assert("src" <> "sk") as Hdeq by easy.
       specialize(_sref_b (upaco2 refinementR r)
                          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (),
                           "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])])
                          ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])
                          "src"
                          "b2"
                          sunit
                          sunit
                          (bp_mergea "src" "b1" sunit (bp_mergea "sk" "b1" sunit (bp_send "sk" Hdeq "b1" sunit)))
                          1
                          listTctl
                 ); intro Ha.
       simpl in Ha.
       rewrite(siso_eq((merge_bp_cont "src"
          (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
          ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])))) in Ha.
       simpl in Ha.
       rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
            ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))) in Ha.
       simpl in Ha.
       rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
              ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))) in Ha.
       simpl in Ha.
       rewrite(siso_eq TR).
       simpl.
       apply Ha.
       apply srefl.
       rewrite(siso_eq((merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
                       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       rewrite(siso_eq( merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (())) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       
       unfold upaco2.
       left. 
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
       pfold.
       apply _sref_out.
       apply srefl.
       
       rewrite(siso_eq Tctl).
       simpl.

       unfold upaco2.
       left.
       pfold.
       specialize(_sref_b (upaco2 refinementR r)
       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])
       ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])
       "src"
       "b1"
       sunit
       sunit
       (bp_mergea "src" "b2" sunit (bp_mergea "sk" "b2" sunit (bp_send "sk" Hdeq "b2" sunit)))
       1
       listTctl
       ); intro Hb.
       simpl in Hb.
       rewrite(siso_eq( (merge_bp_cont "src"
          (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
          ("src"
           ! [("b1", (),
               "src" &
               [("b1", (),
                 "sk" &
                 [("b1", (),
                   "sk"
                   ! [("b1", (),
                       "src"
                       ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])))) in Hb.
        simpl in Hb.
        rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
            ("src"
             ! [("b1", (),
                 "src" &
                 [("b1", (),
                   "sk" &
                   [("b1", (),
                     "sk"
                     ! [("b1", (),
                         "src"
                         ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))) in Hb.
         simpl in Hb.
         rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
              ("src"
               ! [("b1", (),
                   "src" &
                   [("b1", (),
                     "sk" &
                     [("b1", (),
                       "sk"
                       ! [("b1", (),
                           "src"
                           ! [("b2", (),
                               "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))) in Hb.
          simpl in Hb.
          apply Hb.
          apply srefl.
          rewrite(siso_eq((merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
                          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), 
                           "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
          simpl.
          rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
                         ("src" & [("b1", (), "sk" & [("b1", (),
                          "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
         ("src" &
          [("b1", (),
            "sk" &
            [("b1", (),
              "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.

         unfold upaco2.
         left.
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
         pfold.
         apply _sref_out.
         apply srefl.
         
         unfold upaco2.
         right.
         apply CIH.
         
         pfold.
         unfold listTctl.
         rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])))).
         unfold coseq_id.
         simpl.
         constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])))).
         unfold coseq_id.
         simpl.
         unfold upaco2.
         left.
         pfold.
         constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))).
         unfold coseq_id, upaco2.
         simpl.
         left.
         pfold.
         constructor.
         simpl. right. right. left. easy.
         rewrite(coseq_eq((act ("src" ! [("b2", (), TR)])))).
         unfold coseq_id, upaco2.
         simpl.
         left.
         pfold.
         constructor.
         simpl. left. easy.
         unfold upaco2.
         left.
         apply listTREq.
         
         rewrite(siso_eq((merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
                                              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
                                      ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
                                      ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.
         rewrite(coseq_eq((act ("src" & [("b2", (),
                                "sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])])))).
         unfold coseq_id, upaco2.
         simpl.
         pfold.
         constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])))).
         unfold coseq_id, upaco2.
         simpl.
         left.
         pfold. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])))).
         unfold upaco2, coseq_id.
         simpl.
         left. pfold.
         constructor.
         simpl. right. right. left. easy.
         rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. right. left. easy.
         rewrite(coseq_eq((act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b2", (), Tctl)])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. right. left. easy.
         unfold upaco2. left.
         apply listTctlEq.

admit.
admit.
         pfold.
         rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])])))).
         unfold coseq_id.
         simpl. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
         unfold coseq_id, upaco2.
         left. pfold. simpl. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. right. right. left. easy.
         rewrite(coseq_eq((act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])))).
         unfold upaco2, coseq_id.
         left. simpl. pfold. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])))).
         unfold upaco2, coseq_id.
         simpl. left. pfold. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. right. right. left. easy.
         rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. left. easy.
         unfold upaco2. left.
         apply listTREq.

         rewrite(siso_eq((merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
                                       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
                                      ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
         simpl.
         rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (())) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
         simpl.
         pfold.
         rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])))).
         unfold coseq_id, upaco2.
         simpl. constructor. 
         simpl. right. left. easy.
         left. pfold.
         rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
         unfold coseq_id.
         simpl. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. right. right. left. easy.
         rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
         unfold coseq_id, upaco2.
         left. simpl. pfold. constructor.
         simpl. right. left. easy.
         rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])))).
         unfold coseq_id, upaco2.
         simpl. left. pfold. constructor.
         simpl. right. right. right. left. easy.
         rewrite(coseq_eq((act ("sk" ! [("b2", (), Tctl)])))).
         unfold coseq_id, upaco2. 
         simpl. left. pfold. constructor.
         simpl. right. right. left. easy.
         unfold upaco2.
         left.
         apply listTctlEq.
admit.
admit.
Admitted.
