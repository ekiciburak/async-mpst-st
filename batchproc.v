From ST Require Import stream st so si reordering siso refinement reorderingfacts subtyping.
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

Lemma singletonTctl: singleton Tctl.
Proof. pcofix CIH.
       pfold. rewrite(siso_eq(Tctl)). simpl.
       constructor. 
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.

CoFixpoint TR := st_receive "src" [("b1",sunit,st_receive "sk" [("b1",sunit,
                                   st_send "sk" [("b1",sunit,st_send "src" [("b1",sunit,
                                   st_receive "src" [("b2",sunit,st_receive "sk" [("b2",sunit,
                                   st_send "sk" [("b2",sunit,st_send "src" [("b2",sunit,TR)])])])])])])])].

Definition Tctl' := st_send "src" [("b1",sunit,st_send "src" [("b2",sunit,TR)])].

Lemma singletonTctl': singleton Tctl'.
Proof. pfold. rewrite(siso_eq(Tctl')). simpl.
       constructor. 
       left. pfold. constructor.
       left.
       pcofix CIH.
       rewrite(siso_eq TR). simpl.
       pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       left. pfold. constructor.
       right. exact CIH.
Qed.

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

Lemma action1: cosetIncR listTctl (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])).
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       unfold coseq_id. simpl.
       constructor.
       specialize(CoInSplit2 ("src", "!")
       (Delay (cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay (cocons ("sk", "?") (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))))
       ("sk", "?") (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "!") (act ("src" ! [("b2", (), TR)])) ))
       ("sk", "!") (act ("src" ! [("b2", (), TR)]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", "!")
       (Delay(cocons ("src", "!") (act TR)))
       ("src", "!") (act TR)
       ); intro Hd.
       apply Hd. simpl. easy. easy.

       constructor.
       specialize(CoInSplit1 ("src", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))))
       ("sk", "?") (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "!")
       (Delay(cocons ("sk", "!") (act ("src" ! [("b2", (), TR)]))))
       ("sk", "!") (act ("src" ! [("b2", (), TR)]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "?")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))))
       ("sk", "?") (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       constructor.
Qed.

Lemma action2: forall (Hdeq: "src" <> "sk"),
cosetIncR listTctl
  (act
     (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
        ("src" &
         [("b1", (),
           "sk" &
           [("b1", (),
             "sk"
             ! [("b1", (),
                 "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
Proof. intros.
       unfold listTctl.
       rewrite(siso_eq((merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
                                     ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
                                    ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
                                    ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl.
       rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Ha.
       constructor.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "!") (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))
       ("sk", "!") 
       (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro He.
       apply He. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "!") (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", "!") 
       (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hf.
       apply Hf. simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", "!")
       (Delay(cocons ("src", "!") (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))))
       ("src", "!") 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))
       ); intro Hg.
       apply Hg. simpl. easy. easy.

       constructor.
       specialize(CoInSplit1 ("src", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       constructor.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "!")
       (Delay(cocons ("sk", "!") (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))
       ("sk", "!") 
       (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.
       constructor.

       specialize(CoInSplit2 ("sk", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("sk", "?")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       constructor.
Qed.

Lemma action3:
cosetIncR listTctl
  (act
     ("src" &
      [("b1", (),
        "sk" &
        [("b1", (),
          "sk"
          ! [("b1", (),
              "src"
              ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])])).
Proof. unfold listTctl.
       rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Ha.
       constructor.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "!") (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))))
       ("sk", "!") 
       (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", "!")
       (Delay(cocons ("src", "!") (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))))
       ("src", "!") 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.

       constructor.
       specialize(CoInSplit1 ("src", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "!")
       (Delay(cocons ("sk", "!") (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))))
       ("sk", "!") 
       (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "?")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       constructor.
Qed.

Lemma action4: forall (Hdeq: "src" <> "sk"),
cosetIncR listTctl
  (act
     (merge_bp_cont "src"
        (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
        ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
Proof. intros.
       unfold listTctl.
       rewrite(siso_eq((merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (())) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "!") (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))))
       ("sk", "!") 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))))
       ("src", "?") 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b2", (), Tctl)]))))
       ("sk", "?") 
       (act ("sk" ! [("b2", (), Tctl)]))
       ); intro He.
       apply He. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), Tctl)])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", "!")
       (Delay( cocons ("sk", "!") (act Tctl)))
       ("sk", "!") 
       (act (Tctl))
       ); intro Hf.
       apply Hf. simpl. easy. easy.
       rewrite(siso_eq Tctl). simpl.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", "!")
       (Delay(cocons ("src", "!") (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))
       ("src", "!") 
       (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))
       ); intro Hg.
       apply Hg. simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       specialize(CoInSplit1 ("src", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", "!")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "!")
       (Delay(cocons ("sk", "!") (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))))
       ("sk", "!") 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))
       ); intro Hc.
       apply Hc.  simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", "?")
       (Delay(cocons ("src", "?") (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", "?") 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", "?")
       (Delay(cocons ("sk", "?") (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", "?") 
       (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.

       constructor.
Qed.

Lemma acteqT1:
forall (Hdeq: "src" <> "sk"),
act_eq ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])
  (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
     ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])).
Proof. intros.
       unfold act_eq.
       intros (p,s).
       split; intro Hp.
       punfold Hp. inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act
          (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
              ("src" &
               [("b1", (),
                 "sk" &
                 [("b1", (),
                   "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))). simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act
          (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))). 
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
              ("src" &
               [("b1", (),
                 "sk" &
                 [("b1", (),
                   "sk"
                   ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act
         (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
         ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act
           (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1.
       unfold upaco2 in H3. destruct H3. punfold H1. inversion H1. subst. simpl in H3. inversion H3. subst. clear H3.
       rewrite(coseq_eq((act
           (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
           ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy. easy.
       rewrite(coseq_eq(act
           (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
           ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (())) ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy. easy.
       rewrite(coseq_eq((act
         (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
         ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])) ).
       simpl. easy.
       subst. simpl in H3. inversion H3. subst. clear H3.
       unfold upaco2 in H5. destruct H5. punfold H3. inversion H3. subst. simpl in H5. inversion H5. subst. clear H5. 
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
         ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy. easy.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
         ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
          (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). 
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl. easy.
       subst. simpl in H5. inversion H5. subst. clear H5.
       rewrite(coseq_eq(act
          (merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
              ("src" &
               [("b1", (),
                 "sk" &
                 [("b1", (),
                   "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))). simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act
         (merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
         ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act
         (merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
         ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])) ).
       simpl. easy. easy.
       unfold upaco2. left.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). 
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). 
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))).
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). 
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act ("sk" ! [("b2", (), Tctl)]))).
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). 
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act (Tctl))).
       simpl. easy. easy.
       rewrite (coseq_eq(act Tctl)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act
           ("src" &
            [("b1", (),
              "sk" &
              [("b1", (),
                "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       (*middle*)
       punfold Hp. inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. simpl in H. subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1.
       unfold upaco2 in H3. destruct H3. punfold H1. inversion H1. simpl in H1. subst. simpl in H3. inversion H3. subst. clear H3.
       pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). 
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). 
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). 
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("src" ! [("b2", (), TR)]))).
       simpl. easy.
       subst. simpl in H3. inversion H3. subst. clear H3.
       unfold upaco2 in H5. destruct H5. punfold H3. inversion H3. simpl in H5. inversion H5. subst. easy.
       subst. simpl in H5. inversion H5. subst. clear H5 H6.
       unfold upaco2 in H7. destruct H7. punfold H5. inversion H5. subst. simpl in H6. inversion H6. subst. easy.
       subst. simpl in H6. inversion H6. subst. clear H6 H7.
       unfold upaco2 in H8. destruct H8. punfold H6. inversion H6. subst. simpl in H7. inversion H7. subst. easy.
       subst. simpl in H7. inversion H7. subst. clear H7 H8.
       unfold upaco2 in H9. destruct H9. punfold H7. inversion H7. subst. simpl in H8. inversion H8. subst.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       unfold coseq_id. simpl. clear H8.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys :=  (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys :=  (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys :=  (act ("src" ! [("b2", (), TR)]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys :=  (act TR)).
       simpl. easy.
       subst. simpl in H8. inversion H8. subst. clear H8 H10 H7 H6 H5 H3 H1 H Hp.
       pcofix CIH.
       pfold.
       rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act ("src" ! [("b2", (), TR)]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act ("src" ! [("b2", (), TR)])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act TR)).
       simpl. easy. easy.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (),
              "sk"
              ! [("b1", (),
                  "src"
                  ! [("b1", (),
                      "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq((act
         ("sk" &
          [("b1", (),
            "sk"
            ! [("b1", (),
                "src"
                ! [("b1", (),
                    "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk"
              ! [("b1", (),
                  "src"
                  ! [("b1", (),
                      "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("sk"
          ! [("b1", (),
              "src"
              ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act
           ("src"
                  ! [("b1", (),
                      "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("src"
          ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act
           ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
Qed.

Lemma acteqT2:
forall (Hdeq: "src" <> "sk"),
act_eq
  ("src" &
   [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])])
  (merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
     ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])).
Proof. intros.
       unfold act_eq.
       intros (p,s).
       split. intro Hp.
       punfold Hp. inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy.
       subst. simpl in H. inversion H. subst. clear H.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
          (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
          ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act
           (merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H Hp.
       unfold upaco2 in H3. destruct H3. punfold H. inversion H. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           (merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with  (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H.
       unfold upaco2 in H4. destruct H4. punfold H. inversion H. simpl in H1. inversion H1. subst. clear H1.
       pfold.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           (merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
              ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         (merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
         ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])) ).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act ("sk" ! [("b2", (), Tctl)]))).
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act Tctl)).
       simpl. easy. easy.
       rewrite(coseq_eq(act Tctl)). unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit1A with (ys := (act
           ("src" &
            [("b1", (),
              "sk" &
              [("b1", (),
                "sk"
                ! [("b1", (),
                    "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H5 H.
       rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
                      ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
                      ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       rewrite(siso_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
                      ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       pfold.
       rewrite(coseq_eq(act
           ("src" &
            [("b1", (),
              "sk" &
              [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (),
              "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("sk" &
              [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act
           ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pcofix CIH. pfold.
       rewrite(coseq_eq(act
           ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk" ! [("b2", (), Tctl)]))).
       simpl. easy. easy.
       rewrite(coseq_eq(act
           ("sk" ! [("b2", (), Tctl)]))).
       unfold coseq_id. simpl.
       unfold upaco2. left. pfold.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act(Tctl))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act Tctl)). unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act
           ("src" &
            [("b1", (),
              "sk" &
              [("b1", (),
                "sk"
                ! [("b1", (),
                    "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("src" &
            [("b1", (),
              "sk" &
              [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
              [("b1", (),
                "sk"
                ! [("b1", (),
                    "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("sk" &
              [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk"
                ! [("b1", (),
                    "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act
           ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
           ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act
           ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl. easy. easy.
       unfold upaco2. right. exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       (*middle*)
       intro Hp.
       punfold Hp. inversion Hp. subst. simpl in H. inversion H. subst. clear H.
       rewrite(coseq_eq(act
         ("src" &
          [("b1", (),
            "sk" &
            [("b1", (),
              "sk"
              ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit1A with (ys := (act
           ("sk" &
            [("b1", (),
              "sk"
              ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy.
       subst. simpl in H. inversion H. subst. clear H Hp.
       unfold upaco2 in H1. destruct H1. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq(act
         ("src" &
          [("b1", (),
            "sk" &
            [("b1", (),
              "sk"
          ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (),
              "sk"
              ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("sk" &
          [("b1", (),
        "sk"
        ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act
           ("sk"
            ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H.
       unfold upaco2 in H3. destruct H3. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1.
       pfold.
       rewrite(coseq_eq(act
         ("src" &
          [("b1", (),
            "sk" &
            [("b1", (),
              "sk"
              ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (),
              "sk"
              ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("sk" &
            [("b1", (),
              "sk"
              ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H.
       unfold upaco2 in H4. destruct H4. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H4.
       unfold upaco2 in H5. destruct H5. punfold H1. inversion H1. subst. simpl in H4. inversion H4. subst. clear H4. easy.
       subst. simpl in H4. inversion H4. subst. clear H H1 H4 H5.
       unfold upaco2 in H6. destruct H6. punfold H. inversion H. subst. simpl in H1. inversion H1. subst. clear H1. easy.
       subst. simpl in H1. inversion H1. subst. clear H H1 H4.
       unfold upaco2 in H5. destruct H5. punfold H. inversion H. simpl in H1. inversion H1. subst. clear H1.
       rewrite(coseq_eq (act
         ("src" &
          [("b1", (),
            "sk" &
            [("b1", (),
              "sk"
              ! [("b1", (),
                  "src"
                  ! [("b1", (),
                      "src" &
                  [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])]))).
       unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (),
              "sk"
              ! [("b1", (),
                  "src"
                  ! [("b1", (),
                      "src" &
                      [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("sk" &
          [("b1", (),
            "sk"
            ! [("b1", (),
                "src"
                ! [("b1", (),
                "src" &
                [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk"
            ! [("b1", (),
                "src"
                ! [("b1", (),
                    "src" &
                    [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("sk"
            ! [("b1", (),
                "src"
                ! [("b1", (),
                "src" &
                [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act
           ("src"
                ! [("b1", (),
                    "src" &
                    [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act
         ("src"
                ! [("b1", (),
                "src" &
                [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1A with (ys := (act
           ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       simpl. easy.
       subst. simpl in H1. inversion H1. subst. clear H1 H H5.
       pfold.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left.  pcofix CIH. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act
           ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act
           ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "?")) (ys := (act
           ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("sk", "!")) (ys := (act
           ("src" ! [("b2", (), TR)]))).
       simpl. easy. easy.
       unfold upaco2. left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))).
       unfold coseq_id. simpl.
       apply CoInSplit2A with (y := ("src", "!")) (ys := (act(TR))).
       simpl. easy. easy.
       unfold upaco2. left.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       pfold.
       apply CoInSplit2A with (y := ("src", "?")) (ys := (act
           ("sk" &
            [("b1", (),
              "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       unfold upaco2. right.
       exact CIH.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
       easy.
       apply CoIn_mon.
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

       exists (mk_siso Tctl' (singletonTctl')).
       split.
(*        symmetry. *)
       pcofix CIH.
       pfold. simpl.
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
       right. simpl in CIH.
       rewrite(siso_eq Tctl') in CIH. simpl in CIH.
       apply CIH.
       
       exists (mk_siso Tctl (singletonTctl)).
       split.
(*        symmetry. *)
       pcofix CIH.
       pfold. simpl.
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
       right. simpl in CIH.
       rewrite(siso_eq Tctl) in CIH. simpl in CIH.
       apply CIH. simpl.

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
         
         apply acteqT1.
         apply acteqT2.
Qed.
