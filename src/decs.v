From Coq Require Import ClassicalEpsilon.
From Paco Require Import paco.
Require Export Coq.Init.Specif.
Require Import ST.src.stream ST.src.st ST.src.so ST.src.si.

CoInductive ForallHoC {A : Type} (P : A -> Prop): coseq A -> Prop :=
  | Forall_conilc  : ForallHoC P conil
  | Forall_coconsc : forall x l, P x -> ForallHoC P l -> ForallHoC P (cocons x l).

Inductive Forall2CCo {a b : Type} (P : a -> b -> Prop) : coseq a -> coseq b -> Prop :=
  | Forall2o_conilc : Forall2CCo P conil conil
  | Forall2o_coconsc: forall x y l l',
                      P x y -> Forall2CCo P l l' -> Forall2CCo P (cocons x l) (cocons y l').

Lemma fconsF1: forall {a b: Type} {f} x xs, @Forall2CCo a b f conil (cocons x xs) -> False.
Proof. intros.
       inversion H.
Defined.

Lemma fconsF2: forall {a b: Type} {f} x xs, @Forall2CCo a b f (cocons x xs) conil -> False.
Proof. intros.
       inversion H.
Defined.

Definition f2codec: forall {a b: Type} {f} ys xs (h: @Forall2CCo a b f ys xs),
  (sigT (fun us =>
    (sigT (fun vs => 
      (sigT (fun u =>
        (sigT (fun v => ys = cocons u us /\ xs = cocons v vs /\ f u v /\ (@Forall2CCo a b f us vs))))))))) +
  (xs = conil /\ ys = conil).
Proof. destruct ys; destruct xs.
       + right. easy.
       + intros. apply fconsF1 in h. easy.
       + intros. apply fconsF2 in h. easy.
       + intros. 
         left.
         exists ys. exists xs. exists a0. exists b0.
         split. easy. split. easy.
         inversion h. subst. split. easy. easy.
Defined.

CoInductive st2soCC: st -> st -> Prop :=
  | st2so_endc: st2soCC st_end st_end
  | st2so_sndc: forall l s x xs y p,
                st2soCC x y ->
                copathsel l s xs y ->
                st2soCC (st_send p (cocons (l,s,x) conil)) (st_send p xs)
  | st2so_rcvc: forall p xs ys,
                Forall2CCo (fun u v => exists l s t t', u = (l,s,t) /\ v = (l,s,t') /\ st2soCC t t') ys xs ->
                st2soCC (st_receive p ys) (st_receive p xs).

Inductive st2siCC: st -> st -> Prop :=
  | st2si_endc: st2siCC st_end st_end
  | st2si_rcvc: forall l s x xs y p,
                st2siCC x y ->
                copathsel l s xs y ->
                st2siCC (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2si_sndc: forall p xs ys,
                Forall2Co (fun u v => exists l s t t', u = (l,s,t) /\ v = (l,s,t') /\ st2siCC t t') ys xs ->
                st2siCC (st_send p ys) (st_send p xs).

CoFixpoint wrf2 ys xs (h: Forall2CCo 
                           (fun u v : String.string * local.sort * st => 
                              exists (l : String.string) (s : local.sort) (t t' : st),
                              u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t') 
                           ys xs): coseq (String.string * local.sort * st) :=
  match f2codec ys xs h with
    | inl (existT us (existT vs (existT u (existT v (conj _ (conj _ (conj _ H))))))) =>
        cocons u (wrf2 _ _ H)
    | _ => conil
  end.

Lemma wrf2_eq: forall l l' f, l = (wrf2 l l' f).
Proof. intros. apply cext.
       revert l l' f.
       pcofix CIH.
       intros.
       dependent inversion f. subst.
       pfold.
       rewrite(coseq_eq(wrf2 conil conil
         (Forall2o_conilc
           (fun u v : String.string * local.sort * st =>
            exists (l : String.string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t')))). simpl.
       constructor.
       
       subst.
       rewrite(coseq_eq(wrf2 (cocons x l0) (cocons y l'0)
          (Forall2o_coconsc
            (fun u v : String.string * local.sort * st => 
             exists (l : String.string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t') x y l0 l'0 e f0))). simpl.
        pfold.
        constructor.
        right.
        apply CIH. easy.
Qed.

Lemma cf1: forall s c, st2soCC (end) (s & c) -> False.
Proof. intros. inversion H. Defined.

Lemma cf2: forall s c, st2soCC (end) (s ! c) -> False.
Proof. intros. inversion H. Defined.

Lemma cf3: forall s c, st2soCC (s & c) (end) -> False.
Proof. intros. inversion H. Defined.

Lemma cf4: forall s c, st2soCC (s ! c) (end) -> False.
Proof. intros. inversion H. Defined.

Lemma cf5: forall s s0 c c0, st2soCC (s & c) (s0 ! c0)-> False.
Proof. intros. inversion H. Defined.

Lemma cf6: forall s s0 c c0, st2soCC (s ! c) (s0 & c0)-> False.
Proof. intros. inversion H. Defined.

Definition sodec: forall t1 t2 (h: st2soCC t1 t2),
  (sigT (fun l =>
    (sigT (fun s =>
      (sigT (fun x =>
        (sigT (fun xs =>
          (sigT (fun p =>
            (sig (fun y => (copathsel l s xs y) /\ t1 = (st_send p (cocons (l,s,x) conil)) /\ (t2 = (st_send p xs)) /\ (st2soCC x y) ))))))))))))
  +
  (t1 = st_end /\ t2 = st_end)
  +
  (sigT (fun xs =>
    (sigT (fun p =>
      (sig (fun ys => t1 = (st_receive p ys) /\ t2 = (st_receive p xs) /\ 
        (Forall2CCo 
          (fun u v : String.string * local.sort * st => exists (l : String.string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t') 
          ys xs) )))))).
Proof. intros.
       destruct t1; destruct t2.
       - left. right. easy.
       - apply cf1 in h. easy.
       - apply cf2 in h. easy.
       - apply cf3 in h. easy.
       - right. exists c0. exists s. exists c.
         inversion h. subst.
         split. easy. split. easy. easy.
       - apply cf5 in h. easy.
       - apply cf4 in h. easy.
       - apply cf6 in h. easy.
       - 
         destruct c; destruct c0. 
         left. right.
         inversion h.
         left. right.
         inversion h.
         left. right.
         inversion h. subst.
         inversion H5.

         left. left.
         destruct p as ((l1,s1),t1).
         destruct p0 as ((l2,s2),t2).
         exists l1. exists s1. exists t1.
         exists(cocons (l2, s2, t2) c0).
         exists s0.
         apply constructive_indefinite_description.
         inversion h. subst. exists y.
         split. easy. split. easy. split. easy. easy.
Qed.

CoFixpoint wrapSo t1 t2 (h: st2soCC t1 t2): st :=
  match sodec t1 t2 h with
    | inl (inl (existT l (existT s (existT x (existT xs (existT p (exist y (conj _ (conj _ (conj _ H)))))))))) =>
        st_send p (cocons (l,s,wrapSo x y H) conil)
    | inr (existT xs (existT p (exist ys (conj _ (conj _ H))))) =>
        st_receive p (wrf2 ys xs H)
    | _ => st_end
  end.

Lemma eqTfr: forall t r, paco2 st_equiv r t t.
Proof. intros. revert t.
       pcofix CIH.
       intros.
       destruct t.
       pfold. constructor.
       pfold. constructor.
       revert c.
       pcofix CIH2. 
       destruct c. pfold. constructor.
       pfold. constructor.
       destruct p as ((l1,s1),t1).
       exists l1. exists s1. exists t1. exists l1. exists s1. exists t1.
       split. easy. split. easy. split. easy. split. easy. right. apply CIH.
       right. apply CIH2.

       pfold. constructor.
       revert c.
       pcofix CIH2. 
       destruct c. pfold. constructor.
       pfold. constructor.
       destruct p as ((l1,s1),t1).
       exists l1. exists s1. exists t1. exists l1. exists s1. exists t1.
       split. easy. split. easy. split. easy. split. easy. right. apply CIH.
       right. apply CIH2.
Qed.

Lemma f2co_refl: forall l r,
Forall2Co
  (fun u v : String.string * local.sort * st =>
   exists (l0 : String.string) (s : local.sort) (t : st) (l'0 : String.string) (s' : local.sort) 
   (t' : st), u = (l0, s, t) /\ v = (l'0, s', t') /\ l0 = l'0 /\ s = s' /\ upaco2 st_equiv r t t') 
  l l.
Proof. intros. revert l. pcofix CIH.
       intros.
       destruct l. pfold. constructor.
       pfold. constructor.
       destruct p as ((l1,s1),t1).
       exists l1. exists s1. exists t1. exists l1. exists s1. exists t1.
       split. easy. split. easy. split. easy. split. easy.
       left. apply eqTfr.
       right. apply CIH.
Qed.

(* CoInductive st_equivCC: st -> st -> Prop :=
  | eq_st_endc: st_equivCC st_end st_end
  | eq_st_rcvc: forall p xs ys,
               Forall2Co (fun u v => exists l s t l' s' t', u = (l,s,t) /\ v = (l',s',t') /\ l = l' /\ s = s'/\ st_equivCC t t') ys xs ->
               st_equivCC (st_receive p ys) (st_receive p xs)
  | eq_st_sndc: forall p xs ys,
               Forall2Co (fun u v => exists l s t l' s' t', u = (l,s,t) /\ v = (l',s',t') /\ l = l' /\ s = s'/\ st_equivCC t t') ys xs ->
               st_equivCC (st_send p ys) (st_send p xs).  *)

Lemma extrsoH: forall t1 t2 (h: st2soCC t1 t2), st_equivC t1 (wrapSo t1 t2 h).
Proof. pcofix CIH. intros.
       dependent inversion h; subst.
       pfold.
       rewrite(st_eq((wrapSo (end) (end) st2so_endc))). simpl.
       destruct(sodec (end) (end) st2so_endc).
       destruct s as [H | H].
       destruct H as (l,(s,(y,(xs,(p,(x,(Ha,(Hb,(Hc,Hd))))))))). easy.
       constructor.
       destruct s as (xs,(p,(ys,(Ha,(Hb,Hc))))). easy.

       rewrite(st_eq((wrapSo (p ! cocons (l, s, x) conil) (p ! xs) (st2so_sndc l s x xs y p s0 c)))). simpl.
       destruct(sodec (p ! cocons (l, s, x) conil) (p ! xs) (st2so_sndc l s x xs y p s0 c)).
       destruct s1 as [H | H].
       destruct H as (l1,(s1,(y1,(xs1,(p1,(x1,(Ha1,(Hb1,(Hc1,Hd1))))))))).
       inversion Hb1. subst. inversion Hc1. subst.
       pfold.
       constructor.
       pfold. 
       constructor. 
       exists l1. exists s1. exists y1.
       exists l1. exists s1. exists (wrapSo y1 x1 Hd1).
       split. easy. split. easy. split. easy. split. easy.
       right. apply CIH.
       
       left. pfold.
       constructor.
       easy.
       destruct s1 as (xs1,(p1,(ys1,(Ha1,(Hb1,Hc1))))). easy.
       
       inversion f; subst. 
       pfold.
       rewrite(st_eq((wrapSo (p & conil) (p & conil) (st2so_rcvc p conil conil f)))). simpl.
       destruct (sodec (p & conil) (p & conil) (st2so_rcvc p conil conil f)).
       destruct s as [H | H].
       destruct H as (l1,(s1,(y1,(xs1,(p1,(x1,(Ha1,(Hb1,(Hc1,Hd1))))))))). easy.
       easy.
       destruct s as (xs1,(p1,(ys1,(Ha1,(Hb1,Hc1))))).
       inversion Ha1. subst. inversion Hb1. subst.
       rewrite(coseq_eq(wrf2 conil conil Hc1)). simpl.
       constructor.
       pfold.
       constructor.
       
       pfold.
       rewrite(st_eq(wrapSo (p & cocons x l) (p & cocons y l') (st2so_rcvc p (cocons y l') (cocons x l) f))). simpl.
       destruct(sodec (p & cocons x l) (p & cocons y l') (st2so_rcvc p (cocons y l') (cocons x l) f)).
       destruct s as [H1 | H1].
       destruct H1 as (l1,(s1,(y1,(xs1,(p1,(x1,(Ha1,(Hb1,(Hc1,Hd1))))))))). easy.
       easy.
       destruct s as (xs1,(p1,(ys1,(Ha1,(Hb1,Hc1))))).
       inversion Ha1. subst. inversion Hb1. subst.
       
       dependent inversion Hc1. subst.
       rewrite(coseq_eq(wrf2 (cocons x l) (cocons y l')
         (Forall2o_coconsc
           (fun u v : String.string * local.sort * st =>
            exists (l0 : String.string) (s : local.sort) (t t' : st), u = (l0, s, t) /\ v = (l0, s, t') /\ st2soCC t t') x y l l' e f0))). simpl.
        constructor.
        pfold. constructor.
        
       destruct e as (l1,(s1,(t1,(t2,(ea,(eb,ec)))))).
       subst.
       exists l1. exists s1. exists t1. exists l1. exists s1. exists t1.
       split. easy. split. easy. split. easy. split. easy.
       left. apply eqTfr.
       
       rewrite <- wrf2_eq with (l' := l') (f := f0).
       left. apply f2co_refl.
Qed.

Lemma extrso: forall t1 t2 (h: st2soCC t1 t2), t1 = (wrapSo t1 t2 h).
Proof. intros.
       apply stExt, extrsoH.
Qed.

