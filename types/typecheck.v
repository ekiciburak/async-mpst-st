Require Import ST.processes.process ST.processes.beta ST.types.local ST.subtyping.subtyping ST.src.st ST.negations.nsubtyping ST.types.typenv.
From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import String List Datatypes ZArith.
Local Open Scope string_scope.
Import ListNotations.
Import CoListNotations.

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
  | tc_sst  : forall cs ct P T T', typ_proc cs ct P T -> subtype3 (lt2st T) (lt2st T') -> typ_proc cs ct P T'
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

