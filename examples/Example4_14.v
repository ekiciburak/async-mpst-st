Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
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
(* Print Tctl. *)

Lemma singletonTctl: singleton Tctl.
Proof. pcofix CIH.
       pfold. rewrite(st_eq(Tctl)). simpl.
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
(* Print TR. *)

Definition Tctl' := st_send "src" [("b1",sunit,st_send "src" [("b2",sunit,TR)])].
(* Print Tctl'. *)

Lemma singletonTctl': singleton Tctl'.
Proof. pfold. rewrite(st_eq(Tctl')). simpl.
       constructor. 
       left. pfold. constructor.
       left.
       pcofix CIH.
       rewrite(st_eq TR). simpl.
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


Definition listTctl := [("src",snd);("src",rcv);("sk",snd);("sk",rcv)].

Lemma listTctlEq: forall r, paco2 coseqInL r (act Tctl) listTctl.
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

Lemma listTREq: forall r, paco2 coseqInL r (act TR) listTctl.
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

Lemma listTctlEq': forall r, paco2 coseqInL r (act Tctl') listTctl.
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

Lemma action1: coseqInR listTctl (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])).
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       unfold coseq_id. simpl.
       constructor.
       specialize(CoInSplit2 ("src", snd)
       (Delay (cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha.
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay (cocons ("sk", rcv) (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))))
       ("sk", rcv) (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))
       ); intro Hb.
       apply Hb.
       simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", snd) (act ("src" ! [("b2", (), TR)])) ))
       ("sk", snd) (act ("src" ! [("b2", (), TR)]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", snd)
       (Delay(cocons ("src", snd) (act TR)))
       ("src", snd) (act TR)
       ); intro Hd.
       apply Hd. simpl. easy. easy.

       constructor.
       specialize(CoInSplit1 ("src", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))))
       ("sk", rcv) (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", snd)
       (Delay(cocons ("sk", snd) (act ("src" ! [("b2", (), TR)]))))
       ("sk", snd) (act ("src" ! [("b2", (), TR)]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))))
       ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", rcv)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))))
       ("sk", rcv) (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       constructor.
Qed.

Lemma action2: forall (Hdeq: "src" <> "sk"),
coseqInR listTctl
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
       rewrite(st_eq((merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
                                     ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       simpl.
       rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
                                    ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
                                    ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
       simpl.
       rewrite(coseq_eq((act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Ha.
       constructor.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", snd) (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))
       ("sk", snd) 
       (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro He.
       apply He. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", snd) (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", snd) 
       (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hf.
       apply Hf. simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", snd)
       (Delay(cocons ("src", snd) (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))))
       ("src", snd) 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))
       ); intro Hg.
       apply Hg. simpl. easy. easy.

       constructor.
       specialize(CoInSplit1 ("src", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       constructor.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", snd)
       (Delay(cocons ("sk", snd) (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))
       ("sk", snd) 
       (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.
       constructor.

       specialize(CoInSplit2 ("sk", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))).
       unfold coseq_id.
       simpl.
       specialize(CoInSplit1 ("sk", rcv)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       constructor.
Qed.

Lemma action3:
coseqInR listTctl
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
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Ha.
       constructor.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", snd) (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))))
       ("sk", snd) 
       (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", snd)
       (Delay(cocons ("src", snd) (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))))
       ("src", snd) 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.

       constructor.
       specialize(CoInSplit1 ("src", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", snd)
       (Delay(cocons ("sk", snd) (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))))
       ("sk", snd) 
       (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.

       constructor.
       specialize(CoInSplit2 ("sk", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", rcv)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       constructor.
Qed.

Lemma action4: forall (Hdeq: "src" <> "sk"),
coseqInR listTctl
  (act
     (merge_bp_cont "src"
        (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
        ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
Proof. intros.
       unfold listTctl.
       rewrite(st_eq((merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl.
       rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (())) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", snd) (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))))
       ("sk", snd) 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))
       ); intro Hc.
       apply Hc. simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))))
       ("src", rcv) 
       (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))
       ); intro Hd.
       apply Hd. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b2", (), Tctl)]))))
       ("sk", rcv) 
       (act ("sk" ! [("b2", (), Tctl)]))
       ); intro He.
       apply He. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), Tctl)])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("src", snd)
       (Delay( cocons ("sk", snd) (act Tctl)))
       ("sk", snd) 
       (act (Tctl))
       ); intro Hf.
       apply Hf. simpl. easy. easy.
       rewrite(st_eq Tctl). simpl.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("src", snd)
       (Delay(cocons ("src", snd) (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))))
       ("src", snd) 
       (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))
       ); intro Hg.
       apply Hg. simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       specialize(CoInSplit1 ("src", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", snd)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", snd)
       (Delay(cocons ("sk", snd) (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))))
       ("sk", snd) 
       (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))
       ); intro Hc.
       apply Hc.  simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))).
       unfold coseq_id. simpl.
       specialize(CoInSplit2 ("sk", rcv)
       (Delay(cocons ("src", rcv) (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))))
       ("src", rcv) 
       (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))
       ); intro Ha.
       apply Ha. simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])))).
       unfold coseq_id. simpl.
       specialize(CoInSplit1 ("sk", rcv)
       (Delay(cocons ("sk", rcv) (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))))
       ("sk", rcv) 
       (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))
       ); intro Hb.
       apply Hb. simpl. easy. easy.

       constructor.
Qed.


Lemma dirRC: coseqInLC (act TR) listTctl.
Proof. pcofix CIH.
       unfold listTctl.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       right. exact CIH.
Qed.

Lemma dirctlC: coseqInLC (act Tctl) listTctl.
Proof. pcofix CIH.
       unfold listTctl.
       rewrite(coseq_eq(act Tctl)). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       right. exact CIH.
Qed.

Lemma dirR: coseqInR listTctl (act TR).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       simpl. easy. easy.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))).
       simpl. easy. easy.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))).
       simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       simpl. easy. easy.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq11: coseqInLC (act ("src" ! [("b2", (), TR)])) listTctl.
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. apply dirRC.
Qed.

Lemma action_eq13: coseqInR listTctl (act ("src" ! [("b2", (), TR)])).
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       specialize dirR; intro H.
       constructor.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))).
       unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq14: coseqInR listTctl (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])).
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("src", rcv)) (ys :=  (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit1 with (y := ("src", rcv)) (ys :=  (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("src", rcv)) (ys :=  (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys :=  (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq15: coseqInLC (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. apply dirRC.
Qed.

Lemma action_eq16: coseqInLC (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left.
       apply dirctlC.
Qed.

Lemma action_eq17: coseqInR listTctl (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])).
Proof. unfold listTctl.
       rewrite(coseq_eq (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.
       rewrite(coseq_eq (act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act (TR))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.
       rewrite(coseq_eq (act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq (act (TR))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act (TR))). simpl. easy. easy.
       rewrite(coseq_eq (act (TR))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq18: coseqInR listTctl (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])).
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq19: coseqInLC (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. apply dirRC.
Qed.

Lemma action_eq20: coseqInLC (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq16.
Qed.

Lemma action_eq21: coseqInR listTctl (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])).
Proof. unfold listTctl.
       rewrite(coseq_eq((act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.
       rewrite(coseq_eq((act ("src" ! [("b2", (), TR)])))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act (TR))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.
       rewrite(coseq_eq((act ("src" ! [("b2", (), TR)])))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act (TR))). simpl. easy. easy.
       rewrite(coseq_eq(act TR)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.

       constructor.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       rewrite(coseq_eq((act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.

       constructor.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq22: coseqInR listTctl (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq23: coseqInLC (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq15.
Qed.

Lemma action_eq24: coseqInLC (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply dirctlC.
Qed.

Lemma action_eq25: coseqInR listTctl (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), TR)]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq26: coseqInR listTctl (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), Tctl)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act (Tctl))). simpl. easy. easy.
       rewrite(coseq_eq(act Tctl)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), Tctl)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act (Tctl))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), Tctl)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq27: coseqInLC (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply action_eq23.
Qed.

Lemma action_eq28: coseqInLC (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply action_eq24.
Qed.

Lemma action_eq29: coseqInR listTctl (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq30: coseqInR listTctl (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), Tctl)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act (Tctl))). simpl. easy. easy.
       rewrite(coseq_eq(act Tctl)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), Tctl)]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq31: coseqInLC (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq27.
Qed.

Lemma action_eq32: coseqInLC (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq28.
Qed.

Lemma action_eq33: coseqInR listTctl (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq34: coseqInR listTctl (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b2", (), Tctl)]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act (Tctl))). simpl. easy. easy.
       rewrite(coseq_eq(act Tctl)). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq36: coseqInLC (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply dirctlC.
Qed.

Lemma action_eq37: coseqInR listTctl (act ("src" ! [("b2", (), TR)])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq(act (TR))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq(act (TR))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       rewrite(coseq_eq(act (TR))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma action_eq38: coseqInR listTctl (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])).
Proof. unfold listTctl.
       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", snd)) (ys := (act ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). simpl. easy. easy.

       constructor.
       rewrite(coseq_eq(act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("src", rcv)) (ys := (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("sk", rcv)) (ys := (act ("sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). simpl. easy. easy.
       constructor.
Qed.

Lemma stb: subtype Tctl' Tctl.
Proof. unfold subtype.
       exists (mk_siso Tctl' (singletonTctl')).
       split.
       pfold. simpl.
       rewrite(st_eq Tctl'). simpl.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pcofix CIH.
       pfold.
       rewrite(st_eq TR). simpl.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.

       exists (mk_siso Tctl (singletonTctl)).
       split.
       simpl.
       pcofix CIH.
       pfold. 
       rewrite(st_eq Tctl). simpl.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_rcv. simpl.
       left. pfold.
       apply st2siso_snd. simpl.
       right. exact CIH.

       simpl.
       rewrite(st_eq Tctl').
       rewrite(st_eq Tctl). simpl.
       pfold.

       specialize(ref_b (upaco2 refinementR bot2) ("src" ! [("b2", (), TR)])  
                                                 ("src" &
       [("b1", (),
         "sk" &
         [("b1", (),
           "sk"
           ! [("b1", (),
               "src"
               ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])
       "src" "b1" (()) (()) (bp_end) 1); intros HSB.
       simpl in HSB.
       simpl in HSB.
       rewrite bpend_an in HSB.
       rewrite bpend_an in HSB.
       apply HSB.
       clear HSB.
       apply srefl.

       unfold upaco2.
       left.
       pcofix CIH.
       pfold.
       assert("src" <> "sk") as Hdeq by easy.
       specialize(ref_b (upaco2 refinementR r)
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
       rewrite(st_eq((merge_bp_cont "src"
          (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
          ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])))) in Ha.
       simpl in Ha.
       rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
            ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))) in Ha.
       simpl in Ha.
       rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (()))
              ("src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))) in Ha.
       simpl in Ha.
       rewrite(st_eq TR).
       simpl.
       apply Ha.
       apply srefl.
       rewrite(st_eq((merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
                       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
       simpl.
       rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.
       rewrite(st_eq( merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (())) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
       simpl.

       unfold upaco2.
       left. 
       pfold.

       specialize(ref_a (upaco2 refinementR r) ("sk" & [("b1", (),
        "sk"
        ! [("b1", (),
            "src"
            ! [("b1", (),
                "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])  
       ("sk" & [("b1", (),
        "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]) 
        "src" "b1" (()) (()) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA.
       clear HSA.

       apply srefl.

       unfold upaco2.
       left. 
       pfold.
       clear HSA.

       specialize(ref_a (upaco2 refinementR r) ("sk"
        ! [("b1", (),
            "src"
            ! [("b1", (),
                "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])  
       ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]) 
        "sk" "b1" (()) (()) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA.
       clear HSA.

       apply srefl.

       unfold upaco2.
       left. 
       pfold.

       clear HSB.
       specialize(ref_b (upaco2 refinementR r) ("src"
       ! [("b1", (),
           "src" &
           [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])  
       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]) 
        "sk" "b1" (()) (()) (bp_end) 1); intros HSB.
       simpl in HSB.
       rewrite bpend_an in HSB.
       rewrite bpend_an in HSB.
       apply HSB.
       clear HSB.

       apply srefl.
       rewrite(st_eq Tctl).
       simpl.

       unfold upaco2.
       left.
       pfold.
       specialize(ref_b (upaco2 refinementR r)
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
       rewrite(st_eq( (merge_bp_cont "src"
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
        rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
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
         rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
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
          rewrite(st_eq((merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
                          ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), 
                           "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
          simpl.
          rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
                         ("src" & [("b1", (), "sk" & [("b1", (),
                          "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.
         rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
         ("src" &
          [("b1", (),
            "sk" &
            [("b1", (),
              "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.

         unfold upaco2.
         left.
         pfold.
         clear HSA HSB.

        specialize(ref_a (upaco2 refinementR r) ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])  
        ("sk" &
         [("b2", (),
          "sk"
          ! [("b2", (),
           "src" &
           [("b1", (),
             "sk" &
             [("b1", (),
               "sk"
               ! [("b1", (),
                   "src"
                   ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]) 
         "src" "b2" (()) (()) (ap_end) 1); intros HSA.
        simpl in HSA.
        rewrite apend_an in HSA.
        rewrite apend_an in HSA.
        apply HSA.
        clear HSA.

         apply srefl.

         unfold upaco2.
         left.
         pfold.

         clear HSA.
         specialize(ref_a (upaco2 refinementR r) ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])  
          ("sk"
          ! [("b2", (),
            "src" &
            [("b1", (),
              "sk" &
              [("b1", (),
                "sk"
                ! [("b1", (),
                    "src"
                    ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])]) 
          "sk" "b2" (()) (()) (ap_end) 1); intros HSA.
         simpl in HSA.
         rewrite apend_an in HSA.
         rewrite apend_an in HSA.
         apply HSA.
         clear HSA.

         apply srefl.

         unfold upaco2.
         left.
         pfold.
         clear HSA.
         specialize(ref_b (upaco2 refinementR r) ("src" ! [("b2", (), TR)])  
          ("src" &
            [("b1", (),
              "sk" &
              [("b1", (),
                "sk"
                ! [("b1", (),
                    "src"
                    ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]) 
          "sk" "b2" (()) (()) (bp_end) 1); intros HSB.
         simpl in HSB.
         rewrite bpend_an in HSB.
         rewrite bpend_an in HSB.
         apply HSB.
         clear HSB.

         apply srefl.

         unfold upaco2.
         right.
         apply CIH.
         exists listTctl.
         split.
apply action_eq11.
split.
apply action_eq36.
split.
apply action_eq13.
apply action_eq14.
exists listTctl.
split.
apply action_eq15.
split.
apply action_eq16.
split.
apply action_eq17.
apply action_eq18.
exists listTctl.
split.
apply action_eq19.
split.
apply action_eq20.
split.
apply action_eq21.
apply action_eq22.
exists listTctl.
split.
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
         split.

         rewrite(st_eq((merge_bp_cont "src" (bp_mergea "src" "b2" (()) (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (()))))
                                              ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])))).
         simpl.
         rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b2" (()) (bp_send "sk" Hdeq "b2" (())))
                                      ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])]))).
         simpl.
         rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b2" (()))
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
         split.
         apply action1.
         apply action2.
         exists listTctl.
         split.
apply action_eq23.
split.
apply action_eq24.
split.
apply action_eq25.
apply action_eq26.
exists listTctl.
split.
apply action_eq27.
split.
apply action_eq28.
split.
apply action_eq29.
apply action_eq30.
exists listTctl.
split.
apply action_eq31.
split.
apply action_eq32.
split.
apply action_eq33.
apply action_eq34.
exists listTctl.
split.
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
         split.

         rewrite(st_eq((merge_bp_cont "src" (bp_mergea "src" "b1" (()) (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (()))))
                                       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])))).
         simpl.
         rewrite(st_eq(merge_bp_cont "src" (bp_mergea "sk" "b1" (()) (bp_send "sk" Hdeq "b1" (())))
                                      ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
         simpl.
         rewrite(st_eq(merge_bp_cont "src" (bp_send "sk" Hdeq "b1" (())) ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))).
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
         split.
         apply action3.
         apply action4.
         exists listTctl.
         split.
apply action_eq11.
split.
apply action_eq36.
split.
apply action_eq37.
apply action_eq38.
Qed.
