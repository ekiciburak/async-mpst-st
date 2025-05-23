From Coq Require Import ClassicalEpsilon.
From Paco Require Import paco.
Require Export Coq.Init.Specif.
Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.siso.

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

CoInductive st2siCC: st -> st -> Prop :=
  | st2si_endc: st2siCC st_end st_end
  | st2si_rcvc: forall l s x xs y p,
                st2siCC x y ->
                copathsel l s xs y ->
                st2siCC (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2si_sndc: forall p xs ys,
                Forall2CCo (fun u v => exists l s t t', u = (l,s,t) /\ v = (l,s,t') /\ st2siCC t t') ys xs ->
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

CoFixpoint wrf ys xs (h: Forall2CCo 
                          (fun u v : String.string * local.sort * st => 
                             exists (l : String.string) (s : local.sort) (t t' : st),
                             u = (l, s, t) /\ v = (l, s, t') /\ st2siCC t t') 
                          ys xs): coseq (String.string * local.sort * st) :=
  match f2codec ys xs h with
    | inl (existT us (existT vs (existT u (existT v (conj _ (conj _ (conj _ H))))))) =>
        cocons u (wrf _ _ H)
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

Lemma cf7: forall s c, st2siCC (end) (s & c) -> False.
Proof. intros. inversion H. Defined.

Lemma cf8: forall s c, st2siCC (end) (s ! c) -> False.
Proof. intros. inversion H. Defined.

Lemma cf9: forall s c, st2siCC (s & c) (end) -> False.
Proof. intros. inversion H. Defined.

Lemma cf10: forall s c, st2siCC (s ! c) (end) -> False.
Proof. intros. inversion H. Defined.

Lemma cf11: forall s s0 c c0, st2siCC (s & c) (s0 ! c0)-> False.
Proof. intros. inversion H. Defined.

Lemma cf12: forall s s0 c c0, st2siCC (s ! c) (s0 & c0)-> False.
Proof. intros. inversion H. Defined.

Definition sodecC: forall t1 t2 (h: st2soCC t1 t2),
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
Defined.

Definition sidecC: forall t1 t2 (h: st2siCC t1 t2),
  (sigT (fun l =>
    (sigT (fun s =>
      (sigT (fun x =>
        (sigT (fun xs =>
          (sigT (fun p =>
            (sig (fun y => (copathsel l s xs y) /\ t1 = (st_receive p (cocons (l,s,x) conil)) /\ (t2 = (st_receive p xs)) /\ (st2siCC x y) ))))))))))))
  +
  (t1 = st_end /\ t2 = st_end)
  +
  (sigT (fun xs =>
    (sigT (fun p =>
      (sig (fun ys => t1 = (st_send p ys) /\ t2 = (st_send p xs) /\ 
        (Forall2CCo 
          (fun u v : String.string * local.sort * st => exists (l : String.string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ st2siCC t t') 
          ys xs) )))))).
Proof. intros.
       destruct t1; destruct t2.
       - left. right. easy.
       - apply cf7 in h. easy.
       - apply cf8 in h. easy.
       - apply cf9 in h. easy.
       - destruct c; destruct c0. 
         left. right.
         inversion h. subst.
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
       - apply cf11 in h. easy.
       - apply cf10 in h. easy.
       - apply cf12 in h. easy.
       - right. exists c0. exists s. exists c.
         inversion h. subst.
         split. easy. split. easy. easy.
Defined.

CoFixpoint wrapSoC t1 t2 (h: st2soCC t1 t2): st :=
  match sodecC t1 t2 h with
    | inl (inl (existT l (existT s (existT x (existT xs (existT p (exist y (conj _ (conj _ (conj _ H)))))))))) =>
        st_send p (cocons (l,s,wrapSoC x y H) conil)
    | inr (existT xs (existT p (exist ys (conj _ (conj _ H))))) =>
        st_receive p (wrf2 ys xs H)
    | _ => st_end
  end.

CoFixpoint wrapSiC t1 t2 (h: st2siCC t1 t2): st :=
  match sidecC t1 t2 h with
    | inl (inl (existT l (existT s (existT x (existT xs (existT p (exist y (conj _ (conj _ (conj _ H)))))))))) =>
        st_receive p (cocons (l,s,wrapSiC x y H) conil)
    | inr (existT xs (existT p (exist ys (conj _ (conj _ H))))) =>
        st_send p (wrf ys xs H)
    | _ => st_end
  end.

Lemma help1CA: forall ys2 xs2 l1 s1 y1,
  copathsel l1 s1 xs2 y1 ->
  (Forall2CCo (fun u v : String.string * local.sort * st =>
     exists (l : String.string) (s : local.sort) (t t' : st),
     u = (l, s, t) /\ v = (l, s, t') /\ st2siCC t t') ys2 xs2) ->
  exists x2, (st2siCC x2 y1 * copathsel l1 s1 ys2 x2)%type.
Proof. intros.
       revert H0.
       revert ys2.
       induction H; intros.
       - inversion H0. subst.
         destruct H3 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst. exists t2. split. easy.
         constructor.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. split. 
         destruct H3. easy.
         constructor. easy. destruct H3. easy.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. split. destruct H3. easy.
         apply pselneqs. easy. destruct H3. easy.
Defined.

Lemma help1C: forall ys2 xs2 l1 s1 y1,
  copathsel l1 s1 xs2 y1 ->
  (Forall2CCo (fun u v : String.string * local.sort * st =>
     exists (l : String.string) (s : local.sort) (t t' : st),
     u = (l, s, t) /\ v = (l, s, t') /\ st2siCC t t') ys2 xs2) ->
  exists x2, st2siCC x2 y1.
Proof. intros.
       revert H0.
       revert ys2.
       induction H; intros.
       - inversion H0. subst.
         destruct H3 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst. exists t2. easy.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. easy.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. easy.
Defined.

Lemma help2CA: forall ys2 xs2 l1 s1 y1,
  copathsel l1 s1 xs2 y1 ->
  (Forall2CCo (fun u v : String.string * local.sort * st =>
     exists (l : String.string) (s : local.sort) (t t' : st),
     u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t') ys2 xs2) ->
  exists x2, (st2soCC x2 y1 * copathsel l1 s1 ys2 x2)%type.
Proof. intros.
       revert H0.
       revert ys2.
       induction H; intros.
       - inversion H0. subst.
         destruct H3 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst. exists t2. split. easy. constructor.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3.
         destruct H3. split. easy. 
         constructor. easy. easy.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. split.
         destruct H3. easy.
         apply pselneqs. easy.
         destruct H3. easy.
Defined.

Lemma help2C: forall ys2 xs2 l1 s1 y1,
  copathsel l1 s1 xs2 y1 ->
  (Forall2CCo (fun u v : String.string * local.sort * st =>
     exists (l : String.string) (s : local.sort) (t t' : st),
     u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t') ys2 xs2) ->
  exists x2, st2soCC x2 y1.
Proof. intros.
       revert H0.
       revert ys2.
       induction H; intros.
       - inversion H0. subst.
         destruct H3 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst. exists t2. easy.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. easy.
       - inversion H1. subst.
         destruct H5 as (l2,(s2,(t2,(t2',(H2a,(H2b,H2c)))))).
         inversion H2b. subst.
         apply IHcopathsel in H6.
         destruct H6 as (t3,H3). exists t3. easy.
Defined.

CoFixpoint wrapSiSoC t1 t2 t (h1: st2soCC t1 t) (h2: st2siCC t2 t): st.
Proof. destruct(sodecC t1 t h1); destruct(sidecC t2 t h2).
       - destruct s as [H1 | H1].
         + destruct H1 as (l1,(s1,(x1,(xs1,(p1,(y1,(Ha1,(Hb1,(Hc1,Hd1))))))))).
           destruct s0 as [H2 | H2].
           ++ exact st_end.
           ++ exact st_end.
         + destruct H1 as (Ha1,Hb1).
           destruct s0 as [H2 | H2].
           ++ exact st_end.
           ++ exact st_end.
       - destruct s as [H1 | H1].
         + destruct H1 as (l1,(s1,(x1,(xs1,(p1,(y1,(Ha1,(Hb1,(Hc1,Hd1))))))))).
           destruct s0 as (xs2,(p2,(ys2,(Ha2,(Hb2,Hc2))))).
           subst. inversion Hb2. subst.
           specialize(help1CA _ _ _ _ _ Ha1 Hc2); intro HN.
           apply constructive_indefinite_description in HN.
           destruct HN as (x2,(Hd2,He2)).
           exact((p2 ! cocons (l1, s1, (wrapSiSoC x1 x2 y1 Hd1 Hd2)) conil)).
         + exact st_end.
       - destruct s as (xs1,(p1,(ys1,(Ha1,(Hb1,Hc1))))). subst.
         destruct s0 as [H2 | H2].
         ++ destruct H2 as (l2,(s2,(x2,(xs2,(p2,(y2,(Ha2,(Hb2,(Hc2,Hd2))))))))).
            subst. inversion Hc2. subst.
            specialize(help2CA _ _ _ _ _ Ha2 Hc1); intro HN.
            apply constructive_indefinite_description in HN.
            destruct HN as (x1,(Hd1,He2)).
            exact((p2 & cocons (l2, s2, (wrapSiSoC x1 x2 y2 Hd1 Hd2)) conil)).
         ++ exact st_end.
         ++ exact st_end.
Defined.

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
     (t' : st), u = (l0, s, t) /\ v = (l'0, s', t') /\ l0 = l'0 /\ s = s' /\ upaco2 st_equiv r t t') l l.
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

Lemma eqpath: forall l s xs u v, copathsel l s xs u -> copathsel l s xs v -> u = v.
Proof. intros.
       induction H; intros.
       inversion H0. easy.
       subst. easy.
       subst. easy.
       inversion H0. subst. easy. subst.
       apply IHcopathsel; easy.
       subst.
       apply IHcopathsel; easy.
       inversion H0. subst. easy. subst.
       apply IHcopathsel; easy.
       subst.
       apply IHcopathsel; easy.
Qed.


Lemma equivWrapSiSoS: forall p l s x xs ys y H c f,
  st_equivC
  (wrapSiSoC (p ! cocons (l, s, x) conil) (p ! ys) (p ! xs) (st2so_sndc l s x xs y p H c) (st2si_sndc p xs ys f))
  (p ! cocons (l, s, (wrapSiSoC x (proj1_sig (@constructive_indefinite_description _ _ (help1CA _ _ _ _ _ c f))) y H  
                                  (fst (proj2_sig (@constructive_indefinite_description _ _ (help1CA _ _ _ _ _ c f)))))) conil).
Proof. pcofix CIH.
       intros.
       inversion f. subst.
       inversion c.
       subst.
       destruct H as (l3,(s3,(t3,(t4,(H3a,(H3b,H3c)))))).
       subst.
       rewrite(st_eq(wrapSiSoC (p ! cocons (l, s, x) conil) (p ! cocons (l3, s3, t3) l0) (p ! cocons (l3, s3, t4) l')
     (st2so_sndc l s x (cocons (l3, s3, t4) l') y p H0 c)
     (st2si_sndc p (cocons (l3, s3, t4) l') (cocons (l3, s3, t3) l0) f))).
     simpl.
     destruct(
     constructive_indefinite_description
         (fun x0 : st =>
          copathsel l s (cocons (l3, s3, t4) l') x0 /\
          p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
          p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
         (eq_ind_r
            (fun s0 : String.string =>
             l = l ->
             s = s ->
             x = x ->
             conil = conil ->
             s0 ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' ->
             st2soCC x y ->
             copathsel l s (cocons (l3, s3, t4) l') y ->
             exists x0 : st,
               copathsel l s (cocons (l3, s3, t4) l') x0 /\
               p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
               p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
            (fun H2 : l = l =>
             eq_ind_r
               (fun s0 : String.string =>
                s = s ->
                x = x ->
                conil = conil ->
                p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' ->
                st2soCC x y ->
                copathsel s0 s (cocons (l3, s3, t4) l') y ->
                exists x0 : st,
                  copathsel l s (cocons (l3, s3, t4) l') x0 /\
                  p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                  p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
               (fun H3 : s = s =>
                eq_ind_r
                  (fun s0 : local.sort =>
                   x = x ->
                   conil = conil ->
                   p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' ->
                   st2soCC x y ->
                   copathsel l s0 (cocons (l3, s3, t4) l') y ->
                   exists x0 : st,
                     copathsel l s (cocons (l3, s3, t4) l') x0 /\
                     p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                     p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                  (fun H4 : x = x =>
                   eq_ind_r
                     (fun s0 : st =>
                      conil = conil ->
                      p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' ->
                      st2soCC s0 y ->
                      copathsel l s (cocons (l3, s3, t4) l') y ->
                      exists x0 : st,
                        copathsel l s (cocons (l3, s3, t4) l') x0 /\
                        p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                        p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                     (fun H5 : conil = conil =>
                      eq_ind conil
                        (fun c0 : coseq (String.string * local.sort * st) =>
                         p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' ->
                         st2soCC x y ->
                         copathsel l s (cocons (l3, s3, t4) l') y ->
                         exists x0 : st,
                           copathsel l s (cocons (l3, s3, t4) l') x0 /\
                           p ! cocons (l, s, x) c0 = p ! cocons (l, s, x) conil /\
                           p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                        (fun H6 : p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' =>
                         eq_ind_r
                           (fun s0 : String.string =>
                            cocons (l3, s3, t4) l' = cocons (l3, s3, t4) l' ->
                            st2soCC x y ->
                            copathsel l s (cocons (l3, s3, t4) l') y ->
                            exists x0 : st,
                              copathsel l s (cocons (l3, s3, t4) l') x0 /\
                              s0 ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                              p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                           (fun H7 : cocons (l3, s3, t4) l' = cocons (l3, s3, t4) l' =>
                            eq_ind_r
                              (fun c0 : coseq (String.string * local.sort * st) =>
                               st2soCC x y ->
                               copathsel l s c0 y ->
                               exists x0 : st,
                                 copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                 p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                                 p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                              (fun (H8 : st2soCC x y) (H9 : copathsel l s (cocons (l3, s3, t4) l') y) =>
                               eq_ind conil
                                 (fun c0 : coseq (String.string * local.sort * st) =>
                                  st2soCC (p ! cocons (l, s, x) c0) (p ! cocons (l3, s3, t4) l') ->
                                  exists x0 : st,
                                    copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                    p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                                    p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                                 (fun h : st2soCC (p ! cocons (l, s, x) conil) (p ! cocons (l3, s3, t4) l') =>
                                  eq_ind_r
                                    (fun s0 : String.string =>
                                     st2soCC (s0 ! cocons (l, s, x) conil) (p ! cocons (l3, s3, t4) l') ->
                                     exists x0 : st,
                                       copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                       p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                                       p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                                    (fun _ : st2soCC (p ! cocons (l, s, x) conil) (p ! cocons (l3, s3, t4) l') =>
                                     ex_intro
                                       (fun x0 : st =>
                                        copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                        p ! cocons (l, s, x) conil = p ! cocons (l, s, x) conil /\
                                        p ! cocons (l3, s3, t4) l' = p ! cocons (l3, s3, t4) l' /\ st2soCC x x0)
                                       y (conj H9 (conj eq_refl (conj eq_refl H8))))
                                    (f_equal (fun e : st => match e with
                                                            | s0 ! _ => s0
                                                            | _ => p
                                                            end) H6) h) conil H5
                                 (st2so_sndc l s x (cocons (l3, s3, t4) l') y p H0 c)) H7)
                           (f_equal (fun e : st => match e with
                                                   | s0 ! _ => s0
                                                   | _ => p
                                                   end) H6)
                           (f_equal (fun e : st => match e with
                                                   | _ ! c0 => c0
                                                   | _ => cocons (l3, s3, t4) l'
                                                   end) H6)) conil H5) H4) H3) H2) eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl H0 c)
     ). destruct a.
        destruct a.
        destruct a.
        unfold eq_rec_r, eq_rec, eq_rect, eq_sym.
        assert(e = eq_refl).
        { specialize(UIP_refl _ _ e); intro H. easy. }
        subst.
        assert(e0 = eq_refl).
        { specialize(UIP_refl _ _ e0); intro H. easy. }
        subst.
        simpl.
        assert(y = x0).
        { apply eqpath with (l := l) (s := s) (xs := (cocons (l3, s3, t4) l')); easy. }  subst.
        assert(c = c0).
        { now destruct (proof_irrelevance _ c c0). } subst.

        destruct(
          constructive_indefinite_description
         (fun x2 : st => (st2siCC x2 x0 * copathsel l s (cocons (l3, s3, t3) l0) x2)%type)
         (help1CA (cocons (l3, s3, t3) l0) (cocons (l3, s3, t4) l') l s x0 c0 f)
        ).
        simpl.
        destruct p0. simpl.
        pfold. constructor.
        pfold. constructor.
        assert(s0 = H0).
        { now destruct (proof_irrelevance _ s0 H0). } subst.
        exists l. exists s.
        exists(wrapSiSoC x x1 x0 H0 s1).
        exists l. exists s.
        exists(wrapSiSoC x x1 x0 H0 s1).
        split. easy. split. easy. split. easy. split. easy.
        left. apply eqTfr.
        left. pfold. constructor. 
Qed.

Lemma equivWrapSiSoR: forall p l s x xs ys y H0 c f,
  st_equivC
  (wrapSiSoC (p & ys) (p & cocons (l, s, x) conil) (p & xs) (st2so_rcvc p xs ys f) (st2si_rcvc l s x xs y p H0 c))
  (p & cocons (l, s, (wrapSiSoC (proj1_sig (@constructive_indefinite_description _ _ (help2CA _ _ _ _ _ c f))) x y
                                (fst (proj2_sig (@constructive_indefinite_description _ _ (help2CA _ _ _ _ _ c f)))) H0)) conil). 
Proof. pcofix CIH.
       intros.
       inversion f. subst.
       inversion c.
       subst.
       destruct H as (l3,(s3,(t3,(t4,(H3a,(H3b,H3c)))))).
       subst.
       rewrite(st_eq(wrapSiSoC (p & cocons (l3, s3, t3) l0) (p & cocons (l, s, x) conil)
     (p & cocons (l3, s3, t4) l')
     (st2so_rcvc p (cocons (l3, s3, t4) l') (cocons (l3, s3, t3) l0) f)
     (st2si_rcvc l s x (cocons (l3, s3, t4) l') y p H0 c))).
     simpl.
        unfold eq_rec_r, eq_rec, eq_rect, eq_sym.
     destruct(
       constructive_indefinite_description
         (fun x0 : st =>
          copathsel l s (cocons (l3, s3, t4) l') x0 /\
          p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
          p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
         (eq_ind_r
            (fun s0 : String.string =>
             l = l ->
             s = s ->
             x = x ->
             conil = conil ->
             s0 & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' ->
             st2siCC x y ->
             copathsel l s (cocons (l3, s3, t4) l') y ->
             exists x0 : st,
               copathsel l s (cocons (l3, s3, t4) l') x0 /\
               p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
               p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
            (fun H2 : l = l =>
             eq_ind_r
               (fun s0 : String.string =>
                s = s ->
                x = x ->
                conil = conil ->
                p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' ->
                st2siCC x y ->
                copathsel s0 s (cocons (l3, s3, t4) l') y ->
                exists x0 : st,
                  copathsel l s (cocons (l3, s3, t4) l') x0 /\
                  p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                  p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
               (fun H3 : s = s =>
                eq_ind_r
                  (fun s0 : local.sort =>
                   x = x ->
                   conil = conil ->
                   p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' ->
                   st2siCC x y ->
                   copathsel l s0 (cocons (l3, s3, t4) l') y ->
                   exists x0 : st,
                     copathsel l s (cocons (l3, s3, t4) l') x0 /\
                     p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                     p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                  (fun H4 : x = x =>
                   eq_ind_r
                     (fun s0 : st =>
                      conil = conil ->
                      p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' ->
                      st2siCC s0 y ->
                      copathsel l s (cocons (l3, s3, t4) l') y ->
                      exists x0 : st,
                        copathsel l s (cocons (l3, s3, t4) l') x0 /\
                        p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                        p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                     (fun H5 : conil = conil =>
                      eq_ind conil
                        (fun c0 : coseq (String.string * local.sort * st) =>
                         p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' ->
                         st2siCC x y ->
                         copathsel l s (cocons (l3, s3, t4) l') y ->
                         exists x0 : st,
                           copathsel l s (cocons (l3, s3, t4) l') x0 /\
                           p & cocons (l, s, x) c0 = p & cocons (l, s, x) conil /\
                           p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                        (fun H6 : p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' =>
                         eq_ind_r
                           (fun s0 : String.string =>
                            cocons (l3, s3, t4) l' = cocons (l3, s3, t4) l' ->
                            st2siCC x y ->
                            copathsel l s (cocons (l3, s3, t4) l') y ->
                            exists x0 : st,
                              copathsel l s (cocons (l3, s3, t4) l') x0 /\
                              s0 & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                              p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                           (fun H7 : cocons (l3, s3, t4) l' = cocons (l3, s3, t4) l' =>
                            eq_ind_r
                              (fun c0 : coseq (String.string * local.sort * st) =>
                               st2siCC x y ->
                               copathsel l s c0 y ->
                               exists x0 : st,
                                 copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                 p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                                 p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                              (fun (H8 : st2siCC x y) (H9 : copathsel l s (cocons (l3, s3, t4) l') y) =>
                               eq_ind conil
                                 (fun c0 : coseq (String.string * local.sort * st) =>
                                  st2siCC (p & cocons (l, s, x) c0) (p & cocons (l3, s3, t4) l') ->
                                  exists x0 : st,
                                    copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                    p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                                    p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                                 (fun h : st2siCC (p & cocons (l, s, x) conil) (p & cocons (l3, s3, t4) l') =>
                                  eq_ind_r
                                    (fun s0 : String.string =>
                                     st2siCC (s0 & cocons (l, s, x) conil) (p & cocons (l3, s3, t4) l') ->
                                     exists x0 : st,
                                       copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                       p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                                       p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                                    (fun _ : st2siCC (p & cocons (l, s, x) conil) (p & cocons (l3, s3, t4) l')
                                     =>
                                     ex_intro
                                       (fun x0 : st =>
                                        copathsel l s (cocons (l3, s3, t4) l') x0 /\
                                        p & cocons (l, s, x) conil = p & cocons (l, s, x) conil /\
                                        p & cocons (l3, s3, t4) l' = p & cocons (l3, s3, t4) l' /\ st2siCC x x0)
                                       y (conj H9 (conj eq_refl (conj eq_refl H8))))
                                    (f_equal (fun e : st => match e with
                                                            | s0 & _ => s0
                                                            | _ => p
                                                            end) H6) h) conil H5
                                 (st2si_rcvc l s x (cocons (l3, s3, t4) l') y p H0 c)) H7)
                           (f_equal (fun e : st => match e with
                                                   | s0 & _ => s0
                                                   | _ => p
                                                   end) H6)
                           (f_equal
                              (fun e : st => match e with
                                             | _ & c0 => c0
                                             | _ => cocons (l3, s3, t4) l'
                                             end) H6)) conil H5) H4) H3) H2) eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl H0 c)
     ). destruct a.
        destruct a.
        destruct a.
        assert(e = eq_refl).
        { specialize(UIP_refl _ _ e); intro H. easy. }
        subst.
        assert(e0 = eq_refl).
        { specialize(UIP_refl _ _ e0); intro H. easy. }
        subst.
        simpl.
        assert(y = x0).
        { apply eqpath with (l := l) (s := s) (xs := (cocons (l3, s3, t4) l')); easy. }  subst.
        assert(c = c0).
        { now destruct (proof_irrelevance _ c c0). } subst.

        destruct(
        constructive_indefinite_description
         (fun x2 : st => (st2soCC x2 x0 * copathsel l s (cocons (l3, s3, t3) l0) x2)%type)
         (help2CA (cocons (l3, s3, t3) l0) (cocons (l3, s3, t4) l') l s x0 c0 f)
        ).
        simpl. destruct p0.
        pfold. constructor.
        pfold. constructor.
        assert(s0 = H0).
        { now destruct (proof_irrelevance _ s0 H0). } subst.
        exists l. exists s.
        exists(wrapSiSoC x1 x x0 s1 H0).
        exists l. exists s.
        exists(wrapSiSoC x1 x x0 s1 H0).
        split. easy. split. easy. split. easy. split. easy.
        left. apply eqTfr.
        left. pfold. constructor. 
Qed.

Lemma eqWrapSiSoS: forall p l s x xs ys y H c f,
  (wrapSiSoC (p ! cocons (l, s, x) conil) (p ! ys) (p ! xs) (st2so_sndc l s x xs y p H c) (st2si_sndc p xs ys f))  =
  (p ! cocons (l, s, (wrapSiSoC x (proj1_sig (@constructive_indefinite_description _ _ (help1CA _ _ _ _ _ c f))) y H  
                                  (fst (proj2_sig (@constructive_indefinite_description _ _ (help1CA _ _ _ _ _ c f)))))) conil).
Proof. intros. 
       apply stExt, equivWrapSiSoS.
Qed.

Lemma eqWrapSiSoR: forall p l s x xs ys y H0 c f,
  (wrapSiSoC (p & ys) (p & cocons (l, s, x) conil) (p & xs) (st2so_rcvc p xs ys f) (st2si_rcvc l s x xs y p H0 c)) =
  (p & cocons (l, s, (wrapSiSoC (proj1_sig (@constructive_indefinite_description _ _ (help2CA _ _ _ _ _ c f))) x y
                                (fst (proj2_sig (@constructive_indefinite_description _ _ (help2CA _ _ _ _ _ c f)))) H0)) conil). 
Proof. intros. 
       apply stExt, equivWrapSiSoR.
Qed.

Require Import Coq.Program.Equality.

Lemma invSi: forall x x0 y (H: st2soCC x y) (s0: st2siCC x0 y), st2siCC (wrapSiSoC x x0 y H s0) x.
Proof. cofix CIH. intros.
       dependent destruction H; dependent destruction s0. subst.
       rewrite(st_eq (wrapSiSoC (end) (end) (end) st2so_endc st2si_endc)). simpl. constructor.
       
       rewrite eqWrapSiSoS.
       constructor.
       constructor.
       destruct((constructive_indefinite_description (fun x2 : st => (st2siCC x2 y * copathsel l s ys x2)%type)
           (help1CA ys xs l s y c f))).
       simpl.
       
       exists l. exists s. destruct p0. exists (wrapSiSoC x x0 y H s0). exists x.
       split. simpl. easy. split. easy. apply CIH.
       constructor.

       rewrite eqWrapSiSoR.
       destruct(
       (constructive_indefinite_description (fun x2 : st => (st2soCC x2 y * copathsel l s ys x2)%type)
              (help2CA ys xs l s y c f))
       ). simpl.
       apply st2si_rcvc with (y := x0).
       apply CIH.
       destruct p0. easy.
Admitted.

Lemma invSo: forall x x0 y (H: st2soCC x y) (s0: st2siCC x0 y), st2soCC (wrapSiSoC x x0 y H s0) x0.
Proof. cofix CIH. intros.
       dependent destruction H; dependent destruction s0. subst.
       rewrite(st_eq (wrapSiSoC (end) (end) (end) st2so_endc st2si_endc)). simpl. constructor.
       
       rewrite eqWrapSiSoS.
       destruct(constructive_indefinite_description
                (fun x2 : st => (st2siCC x2 y * copathsel l s ys x2)%type)
                (help1CA ys xs l s y c f)).
       simpl.
       destruct p0.
       apply st2so_sndc with (y := x0). simpl.
       apply CIH.
       easy.

       rewrite eqWrapSiSoR.
       constructor.
       constructor.
       destruct(constructive_indefinite_description
           (fun x2 : st => (st2soCC x2 y * copathsel l s ys x2)%type)
           (help2CA ys xs l s y c f)).
       simpl.
       destruct p0.
       simpl.
       exists l. exists s. exists (wrapSiSoC x0 x y s1 s0). exists x.
       split. simpl. easy. split. easy. apply CIH.
       constructor.
Admitted.

Lemma intersect: forall t1 t2 t, st2soCC t1 t -> st2siCC t2 t -> exists w, st2siCC w t1 /\ st2soCC w t2.
Proof. intros.
       exists(wrapSiSoC t1 t2 t H H0).
       split.
       dependent destruction H; dependent destruction H0. subst. 
       rewrite(st_eq (wrapSiSoC (end) (end) (end) st2so_endc st2si_endc)). simpl. constructor.

       rewrite eqWrapSiSoS.
       constructor.
       constructor.
       destruct((constructive_indefinite_description
           (fun x2 : st => (st2siCC x2 y * copathsel l s ys x2)%type)
           (help1CA ys xs l s y c f))).
       simpl.
       exists l. exists s. destruct p0. exists (wrapSiSoC x x0 y H s0). exists x.
       split.  easy. split. easy.
       apply invSi.

       constructor.

       rewrite eqWrapSiSoR.
       destruct((constructive_indefinite_description
              (fun x2 : st => (st2soCC x2 y * copathsel l s ys x2)%type)
              (help2CA ys xs l s y c f))).
       simpl.
       apply st2si_rcvc with (y := x0).
       destruct p0. simpl.
       apply invSi.
       destruct p0. easy.
       
       
       dependent destruction H; dependent destruction H0. subst. 
       rewrite(st_eq (wrapSiSoC (end) (end) (end) st2so_endc st2si_endc)). simpl. constructor.

       rewrite eqWrapSiSoS.
       destruct(constructive_indefinite_description
                (fun x2 : st => (st2siCC x2 y * copathsel l s ys x2)%type)
                (help1CA ys xs l s y c f)).
       simpl.
       apply st2so_sndc with (y := x0).
       destruct p0. simpl.
       apply invSo.
       destruct p0. easy.

       rewrite eqWrapSiSoR.
       constructor.
       constructor.
       destruct((constructive_indefinite_description
           (fun x2 : st => (st2soCC x2 y * copathsel l s ys x2)%type)
           (help2CA ys xs l s y c f))).
       simpl.
       destruct p0. simpl.
       exists l. exists s. exists (wrapSiSoC x0 x y s0 H0). exists x.
       split.  easy. split. easy.
       apply invSo.

       constructor.
Qed.



