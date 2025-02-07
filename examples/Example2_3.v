Require Import ST.src.stream ST.processes.process ST.processes.beta ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.nondepro ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
(* From mathcomp Require Import all_ssreflect seq. *)
From Paco Require Import paco.
Require Import String List ZArith.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Local Open Scope string_scope.

Definition M1 (p q: participant) (l: label): session :=
  (p <-- ps_receive q [(l,isae(aevar "x"),ps_end)] | nilq) ||| (q <-- ps_send p l (isval (vint 42%Z)) ps_end | nilq).

Definition M1' (p q: participant) (l: label): session :=
  (p <-- ps_end | nilq) ||| (q <-- ps_end | nilq).

Example redM1: forall (p q: participant) (l: label), beta_multistep (M1 p q l) (M1' p q l).
Proof. intros.
       unfold beta_multistep, M1, M1'.
       setoid_rewrite scomm.
       apply multi_step with (y := 
         ((q <-- ps_end | (conq nilq (mesq p l (vint 42) nilq))) ||| 
          (p <-- ps_receive q [(l, isae (aevar "x"), ps_end)] | nilq))).
       apply r_send with (c := estate). simpl.
       setoid_rewrite scomm.
       apply multi_step with (y := 
         (((p <-- subst_expr (ps_receive q [(l, isae (aevar "x"), ps_end)]) l (isval (vint 42)) | nilq) ||| 
          (q <-- ps_end | nilq)))).
       specialize (r_rcv p q l ([(l, isae (aevar "x"), ps_end)])
                         (vint 42) (ps_end) nilq nilq
                         (p <-- ps_end | nilq)
       ); intro HR.
       setoid_rewrite scomm in HR.
       setoid_rewrite sann in HR.
       exact HR.

       simpl.
       rewrite String.eqb_refl.
       apply multi_refl.
Qed.

(* Example 2 in "A Very Gentle Introduction to Multiparty Session Types" *)
Definition PAlice: process := 
  ps_send "Bob" "l1" (isval (vint 50)) (ps_receive "Carol" [("l3",isae (aevar "x"),ps_end)]).

Definition PBob: process :=
  ps_receive "Alice" [("l1",isae (aevar "x"),ps_send "Carol" "l2" (isval (vint 100)) ps_end); 
                      ("l4",isae (aevar "x"),ps_send "Carol" "l2" (isval (vint 2))  ps_end)].

Definition PCarol: process :=
  ps_receive "Bob" [("l2",isae (aevar "x"),ps_send "Alice" "l3" (isae (aesucc (aevar "x")))  ps_end)].

Definition MS: session := ("Alice" <-- PAlice | nilq) ||| ("Bob" <-- PBob | nilq) ||| ("Carol" <-- PCarol | nilq).

Definition MS': session := ("Alice" <-- ps_end | nilq) ||| ("Bob" <-- ps_end | nilq) ||| ("Carol" <-- ps_end | nilq).

Example redMS: beta_multistep MS MS'.
Proof. intros.
       unfold beta_multistep, MS, MS', PAlice.
       apply multi_step with
       (y := (("Alice" <-- (ps_receive "Carol" [("l3", isae (aevar "x"), ps_end)]) | conq nilq (mesq "Bob" "l1" (vint 50) nilq)) ||| 
             ("Bob" <-- PBob | nilq)) ||| ("Carol" <-- PCarol | nilq)).
       setoid_rewrite sassoc.
       apply r_send with (c := estate). simpl.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ("Bob" <-- subst_expr (PBob) "l1" (isval (vint 50)) | nilq)
              ||| ("Alice" <-- ps_receive "Carol" [("l3", isae (aevar "x"), ps_end)] | nilq)
              ||| ("Carol" <-- PCarol | nilq)).
       apply r_rcv.
       simpl. unfold exprR. 
       unfold PCarol.

       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Bob" <-- ps_end | conq nilq (mesq "Carol" "l2" (vint 100) nilq) )
               ||| ("Carol" <-- ps_receive "Bob" [("l2", isae (aevar "x"), ps_send "Alice" "l3" (isae (aesucc (aevar "x"))) ps_end)] | nilq))
               ||| ("Alice" <-- ps_receive "Carol" [("l3", isae (aevar "x"), ps_end)] | nilq))).
       setoid_rewrite sassoc.
       apply r_send with (c := estate). simpl.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Carol" <-- subst_expr (ps_receive "Bob" [("l2", isae (aevar "x"), ps_send "Alice" "l3" (isae (aesucc (aevar "x")) ) ps_end)]) "l2" (isval (vint 100)) | nilq)
                 ||| ("Bob" <-- ps_end | nilq))
                 ||| ("Alice" <-- ps_receive "Carol" [("l3", isae (aevar "x"), ps_end)] | nilq))).
       apply r_rcv. simpl. unfold exprR.
       simpl.

       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Carol" <-- ps_end | conq nilq (mesq "Alice" "l3" (eval estate (isae (aesucc (aeval 100)))) nilq) )
               ||| ("Alice" <-- ps_receive "Carol" [("l3", isae (aevar "x"), ps_end)] | nilq))
               ||| ("Bob" <-- ps_end | nilq))).
       setoid_rewrite sassoc.
       apply r_send with (c := estate). simpl.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

      apply multi_step with
      (y := ((("Alice" <-- subst_expr (ps_receive "Carol" [("l3", isae (aevar "x"), ps_end)]) "l3" (isval (vint 101)) | nilq) 
             ||| ("Carol" <-- ps_end | nilq))
             ||| ("Bob" <-- ps_end | nilq))).
      apply r_rcv. simpl.

      apply multi_refl.
Qed.










