Require Import ST.processes.unscoped.
Require Import ST.processes.axioms ST.processes.process.
(* From mathcomp Require Import all_ssreflect seq. *)
From Paco Require Import paco.
From Stdlib Require Import String List ZArith Relations.
Local Open Scope string_scope.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.

Fixpoint incr_freeE (fv m : nat) (e : expr) :=
  match e with
    | e_var n    => e_var (if Nat.leb fv n then (n + m) else n)
    | e_val v    => e_val v 
    | e_succ n   => e_succ (incr_freeE fv m n)
    | e_neg n    => e_neg (incr_freeE fv m n)
    | e_not n    => e_not (incr_freeE fv m n)
    | e_gt u v   => e_gt (incr_freeE fv m u) (incr_freeE fv m v)
    | e_plus u v => e_plus (incr_freeE fv m u) (incr_freeE fv m v) 
    | e_det u v  => e_det (incr_freeE fv m u) (incr_freeE fv m v)
  end. 

Fixpoint subst_expr (n d : nat) (e : expr) (e1 : expr) : expr :=
  match e1 with 
    | e_var 0       => if Nat.eqb n 0 then (incr_freeE 0 d e) else e_var 0
    | e_var (S m)   => if Nat.eqb (S m) n then (incr_freeE 0 d e) else 
                       if Nat.ltb (S m) n then e_var (S m) else e_var m 
    | e_succ e'     => e_succ (subst_expr n d e e')
    | e_neg e'      => e_neg (subst_expr n d e e')
    | e_not e'      => e_not (subst_expr n d e e')
    | e_gt e' e''   => e_gt (subst_expr n d e e') (subst_expr n d e e'')
    | e_plus e' e'' => e_plus (subst_expr n d e e') (subst_expr n d e e'')
    | e_det e' e''  => e_det (subst_expr n d e e') (subst_expr n d e e'')
    | _             => e1
  end.

Fixpoint incr_free (fvP fvE m k : nat) (P : process) : process :=
  match P with 
    | ps_var n          => ps_var (if Nat.leb fvP n then (n + m) else n)
    | ps_send p l e P'  => ps_send p l (incr_freeE fvE k e) (incr_free fvP fvE m k P')
    | ps_receive p llp  => ps_receive p (List.map (
                                                    fun u => match u with 
                                                      | (l, p') => (l, (incr_free fvP (S fvE) m k p'))
                                                    end) llp
                                                  )
    | ps_ite e P1 P2   => ps_ite (incr_freeE fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
    | ps_mu P'         => ps_mu (incr_free (S fvP) fvE m k P')
    | ps_inact         => ps_inact
  end.

Fixpoint retProc (l: list(label*process)) (x: label): option process :=
  match l with
    | nil       => Datatypes.None
    | (y,P)::ys => if eqb x y then Datatypes.Some P else retProc ys x
  end.

Fixpoint subst_expr_proc (p : process) (e : expr) (lb: label) (n d : nat) : process :=
  match p with 
    | ps_send pt l e' P => ps_send pt l (subst_expr n d e e') (subst_expr_proc P e lb n d)
    | ps_ite e' P Q     => ps_ite (subst_expr n d e e') (subst_expr_proc P e lb n d) (subst_expr_proc Q e lb n d)
    | ps_receive pt lst => ps_receive pt (map (fun x => match x with
                                                          | (l, y) => if eqb l lb then (l, subst_expr_proc y e lb (S n) (S d)) else (l, y)
                                                        end) lst)
    | ps_mu P           => ps_mu (subst_expr_proc P e lb n d)
    | _ => p
  end.


Inductive qcong: mqueue -> mqueue -> Prop :=
  | qcons : forall q1 q2 l1 l2 v1 v2 h1 h2, q1 <> q2 -> 
                                            qcong (h1 ++ [(q1,l1,v1)] ++ [(q2,l2,v2)] ++ h2)
                                                  (h1 ++ [(q2,l2,v2)] ++ [(q1,l1,v1)] ++ h2)
  | qnilL : forall h, qcong (nil ++ h) h
  | qnilR : forall h, qcong h (nil ++ h)
  | qassoc: forall h1 h2 h3, qcong (h1 ++ (h2 ++ h3)) ((h1 ++ h2) ++ h3).

Inductive pcong: relation process :=
  | pmuUnf: forall p, pcong (ps_mu p) (subst_process ((ps_mu p) .: ps_var) p).

Inductive scong: relation session :=
  | sann   : forall p M, scong ((p <-- ps_end | nil) |||| M) M
  | scomm  : forall M1 M2, scong (M1 |||| M2) (M2 |||| M1)
  | sassoc : forall M1 M2 M3, scong (M1 |||| M2 |||| M3) (M1 |||| (M2 |||| M3))
(*   | sassoc2: forall M1 M2 M3, scong (M1 ||| M2 ||| M3) ((M1 ||| M2) ||| M3) *)
  | sassoc2: forall M1 M2 M3, scong (M1 |||| M2 |||| M3) (M1 |||| (M3 |||| M2)) 
  | scongl : forall p P Q h1 h2 M, pcong P Q -> qcong h1 h2 -> 
                                   scong ((p <-- P | h1) |||| M) ((p <-- Q | h2) |||| M).

Inductive beta: relation session :=
  | r_sendl  : forall p q l e P hp v, stepE e (e_val v) -> 
                                      beta (p <-- (ps_send q l e P) | hp)
                                           (p <-- P | (hp ++ ([(q,l,(e_val v))])))
  | r_rcvl   : forall p q l xs v Q hp hq y, Datatypes.Some y = retProc xs l ->
                                            beta ((p <-- ps_receive q xs | hp) |||| (q <-- Q | ([(p,l,(e_val v))] ++ hq)))
                                                 ((p <-- subst_expr_proc y (* (ps_receive q xs) *) (e_val v) l 0 0 | hp)  |||| (q <-- Q | hq))
  | r_cond_tl: forall p e P Q h, stepE e (e_val (vbool true))  -> beta ((p <-- ps_ite e P Q | h)) ((p <-- P | h))
  | r_cond_fl: forall p e P Q h, stepE e (e_val (vbool false)) -> beta ((p <-- ps_ite e P Q | h)) ((p <-- Q | h))
  | r_send   : forall p q l e P hp M v, stepE e (e_val v) -> 
                                        beta ((p <-- (ps_send q l e P) | hp) |||| M) 
                                             ((p <-- P | (hp ++ ([(q,l,(e_val v))]))) |||| M)
  | r_rcv    : forall p q l xs v Q hp hq M y, Datatypes.Some y = retProc xs l ->
                                              beta ((p <-- ps_receive q xs | hp) |||| (q <-- Q | ([(p,l,(e_val v))] ++ hq)) |||| M)
                                                   ((p <-- subst_expr_proc y (* (ps_receive q xs) *) (e_val v) l 0 0 | hp)  |||| (q <-- Q | hq) |||| M)
  | r_cond_t : forall p e P Q h M, stepE e (e_val (vbool true))  -> beta ((p <-- ps_ite e P Q | h) |||| M) ((p <-- P | h) |||| M)
  | r_cond_f : forall p e P Q h M, stepE e (e_val (vbool false)) -> beta ((p <-- ps_ite e P Q | h) |||| M) ((p <-- Q | h) |||| M)
  | r_struct : forall M1 M1' M2 M2', scong M1 M1' -> scong M2' M2 -> beta M1' M2' -> beta M1 M2.

Declare Instance Equivalence_beta : Equivalence beta.
Declare Instance Equivalence_scong : Equivalence scong.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Definition beta_multistep := multi beta.

(* #[global]
Declare Instance RW_scong1: Proper (scong ==> scong ==> flip impl) beta.
#[global]
Declare Instance RW_scong2: Proper (scong ==> scong ==> flip impl) beta_multistep. *)

#[global]
Declare Instance RW_scong3: Proper (scong ==> scong ==> impl) beta.
#[global]
Declare Instance RW_scong4: Proper (scong ==> scong ==> impl) beta_multistep.

(* #[global]
Declare Instance RW_scong5: Proper (scong ==> flip scong ==> impl) beta_multistep.
#[global]
Declare Instance RW_scong6: Proper (flip scong ==> scong ==> impl) beta_multistep.
#[global]
Declare Instance RW_scong7: Proper (scong ==> flip scong ==> flip impl) beta_multistep.
#[global]
Declare Instance RW_scong8: Proper (flip scong ==> scong ==> flip impl) beta_multistep. *)
