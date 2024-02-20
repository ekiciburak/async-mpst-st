Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.refinement ST.src.reorderingfacts ST.examples.subtyping.
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

Definition listTctl := [("src",snd);("src",rcv);("sk",snd);("sk",rcv)].

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
       rewrite(siso_eq Tctl). simpl.
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


Lemma actTRC: cosetIncLC (act TR) listTctl.
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

Lemma actTctlC: cosetIncLC (act Tctl) listTctl.
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

Lemma actTR: cosetIncR listTctl (act TR).
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

Lemma action_eq11: cosetIncLC (act ("src" ! [("b2", (), TR)])) listTctl.
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. apply actTRC.
Qed.

Lemma action_eq13: cosetIncR listTctl (act ("src" ! [("b2", (), TR)])).
Proof. unfold listTctl.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("src", snd)) (ys := (act TR)). simpl. easy. easy.
       specialize actTR; intro H.
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

Lemma action_eq14: cosetIncR listTctl (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])).
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

Lemma action_eq15: cosetIncLC (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. apply actTRC.
Qed.

Lemma action_eq16: cosetIncLC (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])) listTctl.
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
       apply actTctlC.
Qed.

Lemma action_eq17: cosetIncR listTctl (act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])).
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

Lemma action_eq18: cosetIncR listTctl (act ("sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])).
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

Lemma action_eq19: cosetIncLC (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("src" ! [("b2", (), TR)]))). unfold coseq_id. simpl.
       constructor. simpl. left. easy.
       left. apply actTRC.
Qed.

Lemma action_eq20: cosetIncLC (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq16.
Qed.

Lemma action_eq21: cosetIncR listTctl (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])).
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

Lemma action_eq22: cosetIncR listTctl (act ("sk" & [("b2", (), "sk" ! [("b2", (), "src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])])])).
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

Lemma action_eq23: cosetIncLC (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])) listTctl.
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

Lemma action_eq24: cosetIncLC (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b2", (), Tctl)]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply actTctlC.
Qed.

Lemma action_eq25: cosetIncR listTctl (act ("src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])).
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

Lemma action_eq26: cosetIncR listTctl (act ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])).
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

Lemma action_eq27: cosetIncLC (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply action_eq23.
Qed.

Lemma action_eq28: cosetIncLC (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. left. easy.
       left. apply action_eq24.
Qed.

Lemma action_eq29: cosetIncR listTctl (act ("sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])).
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

Lemma action_eq30: cosetIncR listTctl (act ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])).
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

Lemma action_eq31: cosetIncLC (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq27.
Qed.

Lemma action_eq32: cosetIncLC (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])) listTctl.
Proof. pfold.
       rewrite(coseq_eq(act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])]))). unfold coseq_id. simpl.
       constructor. simpl. right. right. right. left. easy.
       left. apply action_eq28.
Qed.

Lemma action_eq33: cosetIncR listTctl (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])])).
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

Lemma action_eq34: cosetIncR listTctl (act ("sk" & [("b1", (), "sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])).
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

Lemma action_eq36: cosetIncLC (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])) listTctl.
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
       left. apply actTctlC.
Qed.

Lemma action_eq37: cosetIncR listTctl (act ("src" ! [("b2", (), TR)])).
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

Lemma action_eq38: cosetIncR listTctl (act ("src" & [("b1", (), "sk" & [("b1", (), "sk" ! [("b1", (), "src" ! [("b2", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])])])])])).
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

       exists Tctl'.
       split.
(*        symmetry. *)
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
(*        symmetry. *)
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

       specialize(_sref_b (upaco2 refinementR bot2) ("src" ! [("b2", (), TR)])  
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
       apply HSB with (L := listTctl).
       clear HSB.
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

       specialize(_sref_a (upaco2 refinementR r) ("sk" & [("b1", (),
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
       apply HSA with (L := listTctl).
       clear HSA.

(*        apply _sref_in. *)
       apply srefl.

       unfold upaco2.
       left. 
       pfold.
       clear HSA.

       specialize(_sref_a (upaco2 refinementR r) ("sk"
        ! [("b1", (),
            "src"
            ! [("b1", (),
                "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])])  
       ("sk" ! [("b1", (), "src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])])]) 
        "sk" "b1" (()) (()) (ap_end) 1); intros HSA.
       simpl in HSA.
       rewrite apend_an in HSA.
       rewrite apend_an in HSA.
       apply HSA with (L := listTctl).
       clear HSA.

(*        apply _sref_in. *)
       apply srefl.

       unfold upaco2.
       left. 
       pfold.

       clear HSB.
       specialize(_sref_b (upaco2 refinementR r) ("src"
       ! [("b1", (),
           "src" &
           [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])])])  
       ("src" & [("b2", (), "sk" & [("b2", (), "sk" ! [("b2", (), Tctl)])])]) 
        "sk" "b1" (()) (()) (bp_end) 1); intros HSB.
       simpl in HSB.
       rewrite bpend_an in HSB.
       rewrite bpend_an in HSB.
       apply HSB with (L := listTctl).
       clear HSB.
       
(*        apply _sref_out. *)
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
         clear HSA HSB.

        specialize(_sref_a (upaco2 refinementR r) ("sk" & [("b2", (), "sk" ! [("b2", (), "src" ! [("b2", (), TR)])])])  
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
        apply HSA with (L := listTctl).
        clear HSA.
        
(*          apply _sref_in. *)
         apply srefl.

         unfold upaco2.
         left.
         pfold.

         clear HSA.
         specialize(_sref_a (upaco2 refinementR r) ("sk" ! [("b2", (), "src" ! [("b2", (), TR)])])  
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
         apply HSA with (L := listTctl).
         clear HSA.
         
(*          apply _sref_in. *)
         apply srefl.

         unfold upaco2.
         left.
         pfold.
         clear HSA.
         specialize(_sref_b (upaco2 refinementR r) ("src" ! [("b2", (), TR)])  
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
         apply HSB with (L := listTctl).
         clear HSB.

(*          apply _sref_out. *)
         apply srefl.

         unfold upaco2.
         right.
         apply CIH.

apply action_eq11.
apply action_eq36.
apply action_eq13.
apply action_eq14.
apply action_eq15.
apply action_eq16.
apply action_eq17.
apply action_eq18.
apply action_eq19.
apply action_eq20.
apply action_eq21.
apply action_eq22.
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

         apply action1.
         apply action2.

apply action_eq23.
apply action_eq24.
apply action_eq25.
apply action_eq26.
apply action_eq27.
apply action_eq28.
apply action_eq29.
apply action_eq30.
apply action_eq31.
apply action_eq32.
apply action_eq33.
apply action_eq34.
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

         apply action3.
         apply action4.
apply action_eq11.
apply action_eq36.
apply action_eq37.
apply action_eq38.
Qed.
