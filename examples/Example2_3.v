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
  (p <-- ps_receive q [(l,ps_end)] | nilq) |||| (q <-- ps_send p l (e_val (vint 42%Z)) ps_end | nilq).

Definition M1' (p q: participant) (l: label): session :=
  (p <-- ps_end | nilq) |||| (q <-- ps_end | nilq).

Example redM1: forall (p q: participant) (l: label), beta_multistep (M1 p q l) (M1' p q l).
Proof. intros.
       unfold beta_multistep, M1, M1'.
       setoid_rewrite scomm.
       apply multi_step with (y := 
         ((q <-- ps_end | (conq nilq (mesq p l (e_val (vint 42)) nilq))) ||||
          (p <-- ps_receive q [(l,ps_end)] | nilq))).
       apply r_send. simpl.
       constructor.

       setoid_rewrite scomm.
       apply multi_step with (y := 
         (((p <-- subst_expr_proc (ps_receive q [(l, ps_end)]) (e_val (vint 42)) l 0 0 | nilq) |||| 
          (q <-- ps_end | nilq)))).
       specialize (r_rcv p q l ([(l, ps_end)])
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
  ps_send "Bob" "l1" (e_val (vnat 50)) (ps_receive "Carol" [("l3", ps_end)]).

Definition PBob: process :=
  ps_receive "Alice" [("l1",ps_send "Carol" "l2" (e_val (vnat 100)) ps_end); 
                      ("l4",ps_send "Carol" "l2" (e_val (vnat 2))  ps_end)].

Definition PCarol: process :=
  ps_receive "Bob" [("l2", ps_send "Alice" "l3" (e_succ (e_var 1))  ps_end)].

Definition MS: session := ("Alice" <-- PAlice | nilq) |||| ("Bob" <-- PBob | nilq) |||| ("Carol" <-- PCarol | nilq).

Definition MS': session := ("Alice" <-- ps_end | nilq) |||| ("Bob" <-- ps_end | nilq) |||| ("Carol" <-- ps_end | nilq).

Example redMS: beta_multistep MS MS'.
Proof. intros.
       unfold beta_multistep, MS, MS', PAlice.
       apply multi_step with
       (y := (("Alice" <-- (ps_receive "Carol" [("l3", ps_end)]) | conq nilq (mesq "Bob" "l1" (e_val (vnat 50)) nilq)) ||||
             ("Bob" <-- PBob | nilq)) |||| ("Carol" <-- PCarol | nilq)).
       setoid_rewrite sassoc.
       apply r_send. simpl.
       constructor.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ("Bob" <-- subst_expr_proc (PBob) (e_val (vnat 50)) "l1"  0 0 | nilq)
              |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nilq)
              |||| ("Carol" <-- PCarol | nilq)).
       apply r_rcv.
       simpl. 
       unfold PCarol.

       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Bob" <-- ps_end | conq nilq (mesq "Carol" "l2" (e_val (vnat 100)) nilq) )
               |||| ("Carol" <-- ps_receive "Bob" [("l2", ps_send "Alice" "l3" (e_succ (e_var 1)) ps_end)] | nilq))
               |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nilq))).
       setoid_rewrite sassoc.
       apply r_send. simpl.
       constructor.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Carol" <-- subst_expr_proc (ps_receive "Bob" [("l2", ps_send "Alice" "l3" (e_succ (e_var 1)) ps_end)]) (e_val (vnat 100)) "l2" 0 0 | nilq)
                 |||| ("Bob" <-- ps_end | nilq))
                 |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nilq))).
       apply r_rcv. simpl.
       simpl.

       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Carol" <-- ps_end | conq nilq (mesq "Alice" "l3" (e_val (vnat 101)) nilq) )
               |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nilq))
               |||| ("Bob" <-- ps_end | nilq))).
       setoid_rewrite sassoc.
       apply r_send. simpl.
       specialize (ec_succ (e_val (vnat 100)) 100); intro He. apply He. constructor.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

      apply multi_step with
      (y := ((("Alice" <-- subst_expr_proc (ps_receive "Carol" [("l3", ps_end)]) (e_val (vnat 101)) "l3" 0 0 | nilq) 
             |||| ("Carol" <-- ps_end | nilq))
             |||| ("Bob" <-- ps_end | nilq))).
      apply r_rcv. simpl.

      apply multi_refl.
Qed.









