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
  (p <-- ps_receive q [(l,ps_end)] | nil) |||| (q <-- ps_send p l (e_val (vint 42%Z)) ps_end | nil).

Definition M1' (p q: participant) (l: label): session :=
  (p <-- ps_end | nil) |||| (q <-- ps_end | nil).

Example redM1: forall (p q: participant) (l: label), beta_multistep (M1 p q l) (M1' p q l).
Proof. intros.
       unfold beta_multistep, M1, M1'.
       setoid_rewrite scomm.
       apply multi_step with (y := 
         ((q <-- ps_end | (nil ++ [(p,l,(e_val (vint 42)))])) ||||
          (p <-- ps_receive q [(l,ps_end)] | nil))).
       apply r_send.
       constructor. simpl.

       setoid_rewrite scomm.
       apply multi_step with (y := 
         (((p <-- subst_expr_proc (ps_receive q [(l, ps_end)]) (e_val (vint 42)) l 0 0 | nil) |||| 
          (q <-- ps_end | nil)))).
       specialize (r_rcv p q l ([(l, ps_end)])
                         (vint 42) (ps_end) nil nil
                         (p <-- ps_end | nil)
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

Definition MS: session := ("Alice" <-- PAlice | nil) |||| ("Bob" <-- PBob | nil) |||| ("Carol" <-- PCarol | nil).

Definition MS': session := ("Alice" <-- ps_end | nil) |||| ("Bob" <-- ps_end | nil) |||| ("Carol" <-- ps_end | nil).

Example redMS: beta_multistep MS MS'.
Proof. intros.
       unfold beta_multistep, MS, MS', PAlice.
       apply multi_step with
       (y := (("Alice" <-- (ps_receive "Carol" [("l3", ps_end)]) | (nil ++ [("Bob","l1",(e_val (vnat 50)))])) ||||
             ("Bob" <-- PBob | nil)) |||| ("Carol" <-- PCarol | nil)).
       setoid_rewrite sassoc.
       apply r_send.
       constructor.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ("Bob" <-- subst_expr_proc (PBob) (e_val (vnat 50)) "l1"  0 0 | nil)
              |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nil)
              |||| ("Carol" <-- PCarol | nil)).
       apply r_rcv.
       simpl. 
       unfold PCarol.

       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Bob" <-- ps_end | (nil ++ [("Carol","l2",(e_val (vnat 100)))]) )
               |||| ("Carol" <-- ps_receive "Bob" [("l2", ps_send "Alice" "l3" (e_succ (e_var 1)) ps_end)] | nil))
               |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nil))).
       setoid_rewrite sassoc.
       apply r_send.
       constructor.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Carol" <-- subst_expr_proc (ps_receive "Bob" [("l2", ps_send "Alice" "l3" (e_succ (e_var 1)) ps_end)]) (e_val (vnat 100)) "l2" 0 0 | nil)
                 |||| ("Bob" <-- ps_end | nil))
                 |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nil))).
       apply r_rcv. simpl.
       simpl.

       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

       apply multi_step with
       (y := ((("Carol" <-- ps_end | (nil ++ [("Alice","l3",(e_val (vnat 101)))]))
               |||| ("Alice" <-- ps_receive "Carol" [("l3", ps_end)] | nil))
               |||| ("Bob" <-- ps_end | nil))).
       setoid_rewrite sassoc.
       apply r_send. simpl.
       specialize (ec_succ (e_val (vnat 100)) 100); intro He. apply He. constructor.

       setoid_rewrite sassoc.
       setoid_rewrite scomm.
       setoid_rewrite sassoc2.
       setoid_rewrite <- sassoc.

      apply multi_step with
      (y := ((("Alice" <-- subst_expr_proc (ps_receive "Carol" [("l3", ps_end)]) (e_val (vnat 101)) "l3" 0 0 | nil) 
             |||| ("Carol" <-- ps_end | nil))
             |||| ("Bob" <-- ps_end | nil))).
      apply r_rcv. simpl.

      apply multi_refl.
Qed.









