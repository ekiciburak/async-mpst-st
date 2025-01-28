Require Import ST.processes.process ST.types.local ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import String List Datatypes ZArith.
Local Open Scope string_scope.
Import ListNotations.

Inductive theta: Type :=
  | tempt : theta
  | tconse: expr    -> local.sort -> theta -> theta
  | tconsp: process -> local      -> theta -> theta.

Fixpoint lookupe (t: theta) (e: expr): option local.sort :=
  match (e, t) with
    | (isae (aevar s), tconse (isae (aevar m)) st t') => if eqb s m then Some st else lookupe t' e
    | _                                               => None
  end.

Fixpoint lookupp (t: theta) (p: process): option local :=
  match (p, t) with
    | ((ps_var n), tconsp (ps_var m) lt t') => if Nat.eqb n m then Some lt else lookupp t' p
    | _                                     => None
  end.

Definition extende (t: theta) (e: expr) (s: local.sort): theta := tconse e s t.

Definition extendp (t: theta) (p: process) (l: local): theta := tconsp p l t.

Definition sort_eqb (s1 s2: local.sort): bool :=
  match (s1, s2) with
    | (sint, sint)   => true
    | (sbool, sbool) => true
    | (snat, snat)   => true
    | (sunit, sunit) => true
    | _              => false
  end.

Definition is_ss (s1 s2: local.sort): bool :=
  match (s1, s2) with
    | (sint, sint)   => true
    | (sbool, sbool) => true
    | (snat, snat)   => true
    | (sunit, sunit) => true
    | (snat, sint)   => true
    | _              => false
  end.

Fixpoint tcAE (c: theta) (e: aexpr): option local.sort :=
  match e with
    | aeval n  => Some sint
    | aevar s  => lookupe c (isae (aevar s))
    | aesucc a => let ss := tcAE c a in
                  match ss with
                    | Some ss' => if sort_eqb ss' sint then Some sint else None 
                    | _        => None
                  end
    | aeinv a => let ss := tcAE c a in
                  match ss with
                    | Some ss' => if sort_eqb ss' sint then Some sint else None 
                    | _        => None
                  end
  end.

Fixpoint tcBE (c: theta) (e: bexpr): option local.sort :=
  match e with
    | beval n  => Some sbool
    | bevar s  => lookupe c (isbe (bevar s))
    | beneg b => let ss := tcBE c b in
                  match ss with
                    | Some ss' => if sort_eqb ss' sbool then Some sbool else None 
                    | _        => None
                  end 
  end.

(* Definition tcE (c: theta) (e: expr): option local.sort :=
  match e with
    | isval (vint n)   => Some sint
    | isval (vbool b)  => Some sbool
    | isval (vunit tt) => Some sunit
    | isae a           => tcAE c a
    | isbe b           => tcBE c b
    | isgt a           => let ss := tcAE c a in
                          match ss with
                            | Some ss' => if sort_eqb ss' sint then Some sbool else None 
                            | _        => None
                          end
  end. 

Definition stcE (c: theta) (e: expr) (S: local.sort): option local.sort :=
  let ss := tcE c e in 
  match ss with
    | Some SS => if is_ss SS S then Some S else None
    | _       => None
  end.
*)

Inductive tcE: theta -> expr -> local.sort -> Prop :=
  | tce_iv1: forall c n, tcE c (isval (vint n)) sint
  | tce_iv2: forall c n, tcE c (isval (vbool n)) sbool
  | tce_iv3: forall c n, tcE c (isval (vunit n)) sunit
  | tce_iae: forall c a s, Some s = tcAE c a -> tcE c (isae a) sint
  | tce_ibe: forall c b s, Some s = tcBE c b -> tcE c (isbe b) sbool
  | tce_igt: forall c a s, Some s = tcAE c a -> tcE c (isgt a) sbool
  | tce_iss: forall c e s' s, is_ss s s' = true -> tcE c e s' -> tcE c e s.


Fixpoint matchSel (l: label) (xs: list(label*local.sort*local)): option (local.sort*local) :=
  match xs with
    | nil           => None
    | (lbl,s,t)::ys => if eqb l lbl then Some(s,t) else matchSel l ys
  end.

Inductive tcP: theta -> process -> local -> Prop :=
  | tc_end  : forall c, tcP c ps_end lt_end
  | tc_var  : forall c n T, Some T = lookupp c (ps_var n) -> tcP c (ps_var n) T
  | tc_snd  : forall c q l e S P T xs, Some(S,T) = matchSel l xs -> 
                                       tcE c e S ->
                                       tcP c P T -> tcP c (ps_send q l e P) (lt_send q xs)
  | tc_rcv  : forall c q L E P S T, size E >= size S ->
                                    size P >= size T ->
(*                                  List.Forall (fun u => tcE c (fst u) (snd u)) (zip E S) -> *)
                                    List.Forall (fun u => tcP (extende c (fst u) (fst (snd u))) (fst (snd (snd u))) (snd (snd (snd u)))) (zip E (zip S (zip P T))) ->
                                    tcP c (ps_receive q (zip (zip L E) P)) (lt_receive q (zip (zip L S) T))
  | tc_condt: forall c e P Q T, tcE c e sbool -> tcP c P T -> tcP c Q T -> tcP c (ps_ite e P Q) T
  | tc_mu   : forall c P T, tcP (extendp c (ps_var 0) (lt_var 0)) P T -> tcP c (ps_mu P) (lt_mu T)
  | tc_sst  : forall c P T T' p q r s, tcP c P T -> subltype2 T T' p q r s -> tcP c P T'.

Lemma remark4_5: forall c e, tcE c (isbe e) sbool ->
                             tcP c (ps_ite (isbe e) (ps_send "q" "l1" (isval (vint 1%Z)) (ps_send "r" "l2" (isval (vint 2)) ps_end)) 
                                                    (ps_send "q" "l1" (isval (vint 11)) (ps_send "r" "l2" (isval (vint 22)) ps_end)))
                                   (lt_send "q" [("l1",sint, lt_send "r" [("l2",sint,lt_end)])]).
Proof. intros.
       apply tc_condt.
       - easy.
       - specialize (tc_snd c "q" "l1" (isval (vint 1)) sint
                            (ps_send "r" "l2" (isval (vint 2)) ps_end)
                            (lt_send "r" [("l2", sint, lt_end)])
                            [("l1", sint, lt_send "r" [("l2", sint, lt_end)])]
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         easy. 
         apply tce_iv1.
         specialize (tc_snd c "r" "l2" (isval (vint 2)) sint
                            (ps_end)
                            (lt_end)
                            [("l2", sint, lt_end)]
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         easy.
         apply tce_iv1.
         apply tc_end.
       - specialize (tc_snd c "q" "l1" (isval (vint 11)) sint
                            (ps_send "r" "l2" (isval (vint 22)) ps_end)
                            (lt_send "r" [("l2", sint, lt_end)])
                            [("l1", sint, lt_send "r" [("l2", sint, lt_end)])]
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         easy. 
         apply tce_iv1.
         specialize (tc_snd c "r" "l2" (isval (vint 22)) sint
                            (ps_end)
                            (lt_end)
                            [("l2", sint, lt_end)]
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         easy.
         apply tce_iv1.
         apply tc_end.
Qed.





