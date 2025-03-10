Require Import ST.processes.axioms ST.processes.process.
(* From mathcomp Require Import all_ssreflect seq. *)
From Paco Require Import paco.
Require Import String List ZArith Relations.
Local Open Scope string_scope.
Import ListNotations.
Require Import Setoid Morphisms.

Definition veqb (v1 v2: value): bool :=
  match (v1, v2) with
    | (vint n1, vint n2  ) => Z.eqb n1 n2
    | (vbool n1, vbool n2) => Bool.eqb n1 n2
    | (vunit tt, vunit tt) => true
    | _                    => false
  end.

Fixpoint aeeqb (e1 e2: aexpr): bool :=
  match (e1, e2) with
    | (aeval v1, aeval v2)   => Z.eqb v1 v2
    | (aevar s1, aevar s2)   => eqb s1 s2
    | (aesucc e1, aesucc e2) => aeeqb e1 e2
    | (aeinv e1, aeinv e2)   => aeeqb e1 e2
    | _                    => false
  end.

Fixpoint beeqb (e1 e2: bexpr): bool :=
  match (e1, e2) with
    | (beval v1, beval v2) => Bool.eqb v1 v2
    | (bevar s1, bevar s2) => eqb s1 s2
    | (beneg e1, beneg e2) => beeqb e1 e2
    | _                    => false
  end.

Definition eeqb (e1 e2: expr): bool :=
  match (e1, e2) with
    | (isae v1, isae v2)   => aeeqb v1 v2
    | (isbe v1, isbe v2)   => beeqb v1 v2
    | (isgt v1, isgt v2)   => aeeqb v1 v2
    | _                    => false
  end.

Definition total_map (A : Type) := string -> A.
Definition state := total_map (Z*bool).
Definition estate := fun (x: string) => (0%Z,false).

Fixpoint aevaluate (m: state) (e: aexpr): Z :=
  match e with
    | aeinv e1  => (aevaluate m e1) * (-1)
    | aesucc e1 => (aevaluate m e1) + 1
    | aevar x   => fst (m x) 
    | aeval n   => n
  end.

Definition negate(b: bool): bool :=
  match b with
    | true  => false
    | false => true
  end.

Fixpoint bevaluate (m: state) (e: bexpr): bool :=
  match e with
    | beneg e1  => negate (bevaluate m e1)
    | bevar x   => snd (m x) 
    | beval n   => n
  end.

Definition eval (m: state) (e: expr): value :=
  match e with
    | isae a  => vint (aevaluate m a)
    | isbe b  => vbool (bevaluate m b)
    | isgt e1 => vbool (Z.eqb (aevaluate m e1) 0)
    | isval n => n 
  end.

(*  Eval compute in
 eval (fun x => if eqb x "x" then (5%Z,false) else (0%Z,false)) (isae (aesucc (aesucc (aesucc (aevar "x"))))). *)

Fixpoint aexprR (e: aexpr) (y: string) (e1: aexpr): aexpr :=
  match e with
    | aevar x   => if eqb x y then e1 else e
    | aesucc e' => aesucc (aexprR e' y e1)
    | aeinv e'  => aeinv (aexprR e' y e1)
    | _         => e
  end.

Fixpoint bexprR (e: bexpr) (y: string) (e1: bexpr): bexpr :=
  match e with
    | bevar x   => if eqb x y then e1 else e
    | beneg e'  => beneg (bexprR e' y e1)
    | _        => e
  end.

Definition exprR (e: expr) (y: string) (e1: expr): expr :=
  match (e,e1) with
    | (isae a, isae a1)  => isae (aexprR a y a1)
    | (isbe b, isbe b1)  => isbe (bexprR b y b1)
    | (isgt a, isgt a1)  => isgt (aexprR a y a1)
    | (isae a, isval (vint a1)) => isae (aexprR a y (aeval a1))
    | (isbe a, isval (vbool a1)) => isbe (bexprR a y (beval a1))
    | _                  => e
  end.

Fixpoint subst_expr (p: process) (l: label) (e: expr): process :=
  match p with
    | ps_receive s0 s1  => 
      let fix next lst :=
      match lst with
        | (lbl,(isae (aevar x)),P)::xs => if eqb lbl l then
                                          match P with
                                            | ps_send pt l e1 P => ps_send pt l (exprR e1 x e) (subst_expr P l e)
                                            | ps_ite e1 P Q     => ps_ite (exprR e1 x e) (subst_expr P l e) (subst_expr Q l e)
                                            | _                 => subst_expr P l e
                                          end
                                          else next xs
        | (lbl,(isbe (bevar x)),P)::xs => if eqb lbl l then
                                          match P with
                                            | ps_send pt l e1 P => ps_send pt l (exprR e1 x e) (subst_expr P l e)
                                            | ps_ite e1 P Q     => ps_ite (exprR e1 x e) (subst_expr P l e) (subst_expr Q l e)
                                            | _                 => subst_expr P l e
                                          end
                                          else next xs
       | (lbl,_,P)::xs                 => next xs
       | _                             => p
     end
     in next s1
    | _                                => p
  end.

Inductive qcong: relation mqueue :=
  | qcons : forall q1 q2 l1 l2 v1 v2 h1 h2, q1 <> q2 -> 
                                            qcong (conq h1 (conq (mesq q1 l1 v1 nilq) (conq (mesq q2 l2 v2 nilq) h2)))
                                                  (conq h1 (conq (mesq q2 l2 v2 nilq) (conq (mesq q1 l1 v1 nilq) h2)))
  | qnilL : forall h, qcong (conq nilq h) h
  | qnilR : forall h, qcong h (conq nilq h)
  | qassoc: forall h1 h2 h3, qcong (conq h1 (conq h2 h3)) (conq (conq h1 h2) h3).

Inductive pcong: relation process :=
  | pmuUnf: forall p, pcong (ps_mu p) (unfold_muP p).

Inductive scong: relation session :=
  | sann   : forall p M, scong ((p <-- ps_end | nilq) |||| M) M
  | scomm  : forall M1 M2, scong (M1 |||| M2) (M2 |||| M1)
  | sassoc : forall M1 M2 M3, scong (M1 |||| M2 |||| M3) (M1 |||| (M2 |||| M3))
(*   | sassoc2: forall M1 M2 M3, scong (M1 ||| M2 ||| M3) ((M1 ||| M2) ||| M3) *)
  | sassoc2: forall M1 M2 M3, scong (M1 |||| M2 |||| M3) (M1 |||| (M3 |||| M2)) 
  | scongl : forall p P Q h1 h2 M, pcong P Q -> qcong h1 h2 -> 
                                   scong ((p <-- P | h1) |||| M) ((p <-- Q | h2) |||| M).

Inductive beta: relation session :=
  | r_send : forall p q l e P hp M c, beta ((p <-- (ps_send q l e P) | hp) |||| M) 
                                           ((p <-- P | conq hp (mesq q l (eval c e) nilq)) |||| M)
  | r_rcv   : forall p q l xs v Q hp hq M, beta ((p <-- ps_receive q xs | hp) |||| (q <-- Q | conq (mesq p l v nilq) hq) |||| M)
                                                ((p <-- subst_expr (ps_receive q xs) l (isval v) | hp)  |||| (q <-- Q | hq) |||| M)
  | r_cond_t: forall p e P Q h M c, eval c e = vbool true  -> beta ((p <-- ps_ite e P Q | h) |||| M) ((p <-- P | h) |||| M)
  | r_cond_f: forall p e P Q h M c, eval c e = vbool false -> beta ((p <-- ps_ite e P Q | h) |||| M) ((p <-- Q | h) |||| M)
  | r_struct: forall M1 M1' M2 M2', scong M1 M1' -> scong M2' M2 -> beta M1' M2' -> beta M1 M2.

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
