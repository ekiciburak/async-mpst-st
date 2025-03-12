Require Import ST.processes.process ST.types.local ST.subtyping.subtyping ST.src.st ST.negations.nsubtyping ST.types.typenv.
From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import String List Datatypes ZArith.
Local Open Scope string_scope.
Import ListNotations.

(* Inductive theta: Type :=
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
  end. *)

(*
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
  end. *)

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

Definition ctxS := list (option local.sort).
Definition ctxT := list (option local).

Fixpoint SList {A} (lis : list A) : Prop := 
  match lis with 
    | x :: [] => True 
    | _ :: xs                => SList xs
    | []                     => False
  end.

Fixpoint extendLis {A} (n : nat) (ST : option A) : list (option A) :=
  match n with 
    | S m  => None :: extendLis m ST
    | 0    => [ST]
  end.

Fixpoint onth {A : Type} (n : nat) (lis : list (option A)) : option A :=
  match n with 
    | S m => 
      match lis with 
        | x::xs => onth m xs
        | []    => None 
      end
    | 0   =>
      match lis with 
        | x::xs => x 
        | []    => None
      end
  end.

Inductive typ_expr: ctxS -> expr -> local.sort -> Prop :=
  | sc_var : forall c s t, onth s c = Some t -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 typ_expr c e s'
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint
  | sc_det  : forall c e1 e2 s, typ_expr c e1 s -> typ_expr c e2 s -> typ_expr c (e_det e1 e2) s.

(* Inductive tcE: theta -> expr -> local.sort -> Prop :=
  | tce_iv1: forall c n, tcE c (isval (vint n)) sint
  | tce_iv2: forall c n, tcE c (isval (vbool n)) sbool
  | tce_iv3: forall c n, tcE c (isval (vunit n)) sunit
  | tce_iae: forall c a s, Some s = tcAE c a -> tcE c (isae a) sint
  | tce_ibe: forall c b s, Some s = tcBE c b -> tcE c (isbe b) sbool
  | tce_igt: forall c a s, Some s = tcAE c a -> tcE c (isgt a) sbool
  | tce_iss: forall c e s' s, is_ss s s' = true -> tcE c e s' -> tcE c e s. *)

Inductive typ_queue: mqueue -> queue -> Prop :=
  | tq_nil : typ_queue nil nil
  | tq_cons: forall p l v s xs ys cs, typ_expr cs v s -> typ_queue xs ys -> typ_queue ((p,l,v)::xs) ((p,l,s)::ys).

Lemma typ_queu_app: forall q1 m1 q2 m2, typ_queue q1 m1 -> typ_queue q2 m2 -> typ_queue (q1 ++ q2) (m1 ++ m2).
Proof. intro q1.
       induction q1; intros.
       - inversion H. subst. simpl. easy.
       - case_eq m1; intros.
         + subst. inversion H.
         + subst.
           destruct a as ((r1,l1),s1).
           destruct p as ((r2,l2),s2).
           simpl.
           inversion H. subst.
           apply tq_cons with (cs := cs). easy.
           apply IHq1; easy.
Qed.

Inductive typ_proc: ctxS -> ctxT -> process -> local -> Prop :=
  | tc_inact: forall cs ct,     typ_proc cs ct (ps_end) (lt_end)
  | tc_var  : forall cs ct s t, nth s ct None = Some t -> (* wfC t -> *)
                                typ_proc cs ct (ps_var s) t
  | tc_mu   : forall cs ct p t, typ_proc cs (Some t :: ct) p t ->
                                typ_proc cs ct (ps_mu p) t
  | tc_ite  : forall cs ct e p1 p2 T, typ_expr cs e sbool ->
                                      typ_proc cs ct p1 T ->
                                      typ_proc cs ct p2 T ->
                                      typ_proc cs ct (ps_ite e p1 p2) T
  | tc_sst  : forall cs ct P T T' Tr Tr', typ_proc cs ct P T -> lt2stC T Tr -> lt2stC T' Tr' -> subtype3 Tr Tr'  -> typ_proc cs ct P T'
  | tc_recv : forall cs ct p STT P,
                     length P = length STT ->
                     SList P ->
                     Forall2 (fun u v => (exists l proc l' srt typ, u = (l, proc) /\ v = (l', srt, typ) /\ l = l' /\ typ_proc (Some srt :: cs) ct proc typ)) P STT ->
                     typ_proc cs ct (ps_receive p P) (lt_receive p STT)
  | tc_snd  : forall cs ct p l e P S T, typ_expr cs e S ->
                                        typ_proc cs ct P T ->
                                        typ_proc cs ct (ps_send p l e P) (lt_send p (cons (l, S, T) nil)).

Inductive ForallT (P : participant -> process -> mqueue -> Prop) : session -> Prop := 
  | ForallT_mono: forall pt op h, P pt op h -> ForallT P (pt <-- op | h)
  | ForallT_par : forall (M1 M2 : session), ForallT P M1 -> ForallT P M2 -> ForallT P (M1 |||| M2). 

(*add guardedness of local types and processes + make sure that the typing context and the session having exact same participants with no duplications*)
Inductive typ_sess : session -> ctx -> Prop := 
  | t_sess : forall M G, ForallT (fun u P h => exists gamma T, M.find u G = Some (gamma, T) /\ typ_queue h gamma /\ typ_proc nil nil P T) M ->
                         typ_sess M G.

Lemma remark4_5: forall cs ct e, typ_expr cs e sbool ->
                                 typ_proc cs ct (ps_ite e (ps_send "q" "l1" (e_val (vint 1%Z)) (ps_send "r" "l2" (e_val (vint 2)) ps_end)) 
                                                          (ps_send "q" "l1" (e_val (vint 11)) (ps_send "r" "l2" (e_val (vint 22)) ps_end)))
                                                (lt_send "q" [("l1",sint, lt_send "r" [("l2",sint,lt_end)])]).
Proof. intros.
       apply tc_ite.
       - easy.
       - specialize (tc_snd cs ct "q" "l1" (e_val (vint 1)) (ps_send "r" "l2" (e_val (vint 2)) ps_end) sint (lt_send "r" [("l2", sint, lt_end)])
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         constructor.
         specialize (tc_snd cs ct "r" "l2" (e_val (vint 2)) 
                            (ps_end) sint
                            (lt_end)
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         constructor.
         constructor.
       - specialize (tc_snd cs ct "q" "l1" (e_val (vint 11)) 
                            (ps_send "r" "l2" (e_val (vint 22)) ps_end) sint
                            (lt_send "r" [("l2", sint, lt_end)])
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         constructor.
         specialize (tc_snd cs ct "r" "l2" (e_val (vint 22)) 
                            (ps_end) sint
                            (lt_end)
                    ); intro HS.
         simpl in HS. apply HS; clear HS.
         constructor.
         constructor.
Qed.

(* Fixpoint matchSel (l: label) (xs: list(label*local.sort*local)): option (local.sort*local) :=
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
  | tc_sst  : forall c P T T' Tr Tr', tcP c P T -> lt2stC T Tr -> lt2stC T' Tr' -> subtype3 Tr Tr'  -> tcP c P T'. *)

(* Lemma remark4_5: forall c e, tcE c (isbe e) sbool ->
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
 *)




