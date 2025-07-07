From Coq Require Import ssreflect.
From Coq Require Import ClassicalEpsilon.
From Paco Require Import paco.
Require Export Coq.Init.Specif.
Require Import ST.src.stream ST.src.st ST.src.so ST.src.si ST.src.siso ST.src.reordering.

CoInductive ForallHoC {A : Type} (P : A -> Prop): coseq A -> Prop :=
  | Forall_conilc  : ForallHoC P conil
  | Forall_coconsc : forall x l, P x -> ForallHoC P l -> ForallHoC P (cocons x l).

CoInductive Forall2CCo {a b : Type} (P : a -> b -> Prop) : coseq a -> coseq b -> Prop :=
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

Lemma fo2pN: forall ys xs r
  (CIH : forall t1 t2 : st, st2soCC t1 t2 -> r t1 t2),
  Forall2CCo
    (fun u v : String.string * local.sort * st =>
     exists (l : String.string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t')
    ys xs
 ->
Forall2Co
  (fun u v : String.string * local.sort * st =>
   exists (l : String.string) (s : local.sort) (t t' : st),
     u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2so r t t') ys xs.
Proof. intros. revert xs ys H. pcofix CIH2.
       intros. inversion H0.
       subst. pfold. constructor.
       subst.
       pfold. constructor.
       destruct H as (l1,(s1,(t1,(t2,(Ha,(Hb,Hc)))))).
       subst.
       exists l1. exists s1. exists t1. exists t2.
       split. easy. split. easy. right. apply CIH. easy.
       right.
       apply CIH2. easy.
Qed.

(* Lemma fo2pNR: forall ys xs
  (CIH : forall t1 t2 : st, st2soC t1 t2 -> st2soCC t1 t2),
  Forall2Co
  (fun u v : String.string * local.sort * st =>
   exists (l : String.string) (s : local.sort) (t t' : st),
     u = (l, s, t) /\ v = (l, s, t') /\ upaco2 st2so bot2 t t') ys xs ->
  Forall2CCo
    (fun u v : String.string * local.sort * st =>
     exists (l : String.string) (s : local.sort) (t t' : st), u = (l, s, t) /\ v = (l, s, t') /\ st2soCC t t')
    ys xs.
Proof. intros. revert xs ys H. cofix CIH2.
       intros. pinversion H.
       subst. constructor.
       subst.
       constructor.
       destruct H0 as (l1,(s1,(t1,(t2,(Ha,(Hb,Hc)))))).
       subst.
       exists l1. exists s1. exists t1. exists t2.
       split. easy. split. easy. apply CIH.
       destruct Hc. easy. easy.
       specialize(CIH2 l' l H1).
       assumption.
       apply (@mon_f2Ho ).
Admitted.

Lemma st2soL: forall t1 t2, st2soCC t1 t2 -> st2soC t1 t2.
Proof. pcofix CIH.
       intros.
       inversion H0. subst.
       pfold. constructor.
       subst. pfold.
       apply st2so_snd with (y := y). right.
       apply CIH. easy.
       easy.
       pfold. constructor. subst.
       apply fo2pN; easy.
Qed.

Lemma st2soR: forall t1 t2, st2soC t1 t2 -> st2soCC t1 t2.
Proof. cofix CIH.
       intros.
       pinversion H.
       constructor.
       subst.
       apply st2so_sndc with (y := y).
       apply CIH; easy.
       easy.

       subst.
       constructor.
       apply fo2pNR; easy.
       apply st2so_mon.
Admitted.

Lemma st2soEq: forall t1 t2, st2soC t1 t2 <-> st2soCC t1 t2.
Proof. split.
       apply st2soR.
       apply st2soL.
Qed.
 *)
 
CoInductive st2siCC: st -> st -> Prop :=
  | st2si_endc: st2siCC st_end st_end
  | st2si_rcvc: forall l s x xs y p,
                st2siCC x y ->
                copathsel l s xs y ->
                st2siCC (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2si_sndc: forall p xs ys,
                Forall2CCo (fun u v => exists l s t t', u = (l,s,t) /\ v = (l,s,t') /\ st2siCC t t') ys xs ->
                st2siCC (st_send p ys) (st_send p xs).

CoInductive st2sisoCC: st -> st -> Prop :=
  | st2siso_endc: st2sisoCC st_end st_end
  | st2siso_rcvc: forall l s x xs y p,
                  st2sisoCC x y ->
                  copathsel l s xs y ->
                  st2sisoCC (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2siso_sndc: forall l s x xs y p,
                  st2sisoCC x y ->
                  copathsel l s xs y ->
                  st2sisoCC (st_send p (cocons (l,s,x) conil)) (st_send p xs).

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
       apply st2si_sndc.
       constructor. 
       destruct((constructive_indefinite_description (fun x2 : st => (st2siCC x2 y * copathsel l s ys x2)%type)
           (help1CA ys xs l s y c f))). 
       simpl.
       
       exists l. exists s. destruct p0. exists (wrapSiSoC x x0 y H s0). exists x.
       split. simpl. easy. split. easy.
       by have @ := CIH _ _ _ H s0.
       constructor.

       rewrite eqWrapSiSoR.
       destruct(
       (constructive_indefinite_description (fun x2 : st => (st2soCC x2 y * copathsel l s ys x2)%type)
              (help2CA ys xs l s y c f))
       ). simpl.
       apply st2si_rcvc with (y := x0).
       destruct p0.
       simpl.
       apply CIH.
       destruct p0.
       easy.
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
       split. easy. split. easy.
       
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

Require Import List.
Import ListNotations.
Import CoListNotations.
Require Import ST.src.stream ST.processes.process ST.types.local.
Require Import String List Nat.

(* session trees *)

(* From MMaps Require Import MMaps.

Module SS.

  Import String.
  Definition t := string.
  Definition eq x y := if eqb x y then True else False.

  Lemma equiv: Equivalence eq.
  Proof. constructor.
         - repeat intro. unfold eq. rewrite eqb_refl. easy.
         - repeat intro. unfold eq in *.
           case_eq(String.eqb x y ); intros.
           + rewrite eqb_sym in H0. rewrite H0. easy.
           + rewrite H0 in H. easy.
         - repeat intro. unfold eq in *.
           case_eq(String.eqb x y ); intros.
           + case_eq(String.eqb y z); intros.
             ++ rewrite eqb_eq in H1. rewrite eqb_eq in H2.
                subst. rewrite eqb_refl. easy.
             ++ rewrite H2 in H0. easy.
           + rewrite H1 in H. easy. 
  Defined.

  Lemma dec : forall x y : string, {eq x y} + {~ eq x y}.
  Proof. intros.
         unfold eq.
         case_eq(String.eqb x y ); intros.
         + left. easy.
         + right. easy.
  Defined.

  Definition eq_equiv := equiv.

  Definition eq_dec := dec.

End SS.

Module M  := MMaps.WeakList.Make(SS).
Module MF := MMaps.Facts.Properties SS M.

Print M.

Check M.t (local.sort*local.sort). *)

CoInductive lstr: Type :=
  | lstr_end    : lstr
  | lstr_receive: participant -> (label -> option (nat*local.sort*lstr)) -> lstr
  | lstr_send   : participant -> (label -> option (nat*local.sort*lstr)) -> lstr.

(* Inductive lrefinementR2 (seq: lstr -> lstr -> Prop): lstr -> lstr -> Prop :=
  | lref2_a  : forall w w' p f l s s' a n, subsort s' s ->
(*                                         seq w (merge_ap_contn p a w' n)  -> *)
(*                                         act_eq w (merge_ap_contn p a w' n) -> *)
                                        f l = Some(0,s,w) ->
                                        lrefinementR2 seq (lstr_receive p f) (merge_ap_contn p a (st_receive p (cocons (l,s',w') conil)) n)
(*   | ref2_b  : forall w w' p l s s' b n, subsort s s' ->
                                        seq w (merge_bp_contn p b w' n) ->
                                        act_eq w (merge_bp_contn p b w' n) ->
                                        refinementR2 seq (st_send p (cocons (l,s,w) conil)) (merge_bp_contn p b (st_send p (cocons (l,s',w') conil)) n) *)
  | lref2_end: lrefinementR2 seq lst_end lst_end.

Definition refinement2: st -> st -> Prop := fun s1 s2 => paco2 refinementR2 bot2 s1 s2. *)

CoInductive str: Type :=
  | str_end    : str
  | str_receive: participant -> (label -> option (local.sort*str)) -> str
  | str_send   : participant -> (label -> option (local.sort*str)) -> str.

Definition str_id (s: str): str :=
  match s with
    | str_end         => str_end
    | str_receive p l => str_receive p l
    | str_send p l    => str_send p l
  end.

Lemma str_eq: forall s, s = str_id s.
Proof. intro s; destruct s; easy. Defined.

Inductive str_equiv (R: str -> str -> Prop): str -> str -> Prop :=
  | eq_str_end: str_equiv R str_end str_end
  | eq_str_rcv: forall p f1 f2,
                (forall l,
                   match (f1 l, f2 l) with
                     | (None, None)              => True
                     | (Some(s1,t1),Some(s2,t2)) => s1 = s2 /\ R t1 t2
                     | (_, _)                    => False
                   end
                ) ->
                str_equiv R (str_receive p f1) (str_receive p f2)
  | eq_str_snd: forall p f1 f2,
                (forall l,
                   match (f1 l, f2 l) with
                     | (None, None)              => True
                     | (Some(s1,t1),Some(s2,t2)) => s1 = s2 /\ R t1 t2
                     | (_, _)                    => False
                   end
                ) ->
                str_equiv R (str_send p f1) (str_send p f2).

Definition str_equivC: str -> str -> Prop := fun s1 s2 => paco2 str_equiv bot2 s1 s2.

Axiom strExt: forall s1 s2, str_equivC s1 s2 -> s1 = s2.


(* CoFixpoint str2st (t: st): str.
Proof. case_eq t; intros.
       - exact (str_end).
       - clear H. revert c. cofix CIH. intros.
         case_eq c; intros.
         + exact (str_receive s (fun _ => None)).
         + destruct p as ((l1,s1),t1).
           case_eq c0; intros.
           + exact(str_receive s (fun x => if String.eqb x l1 then Some(s1,str2st t1) else None)).
           + destruct p as ((l2,s2),t2).
             exact(str_receive s (fun x => if String.eqb x l1 then Some(s1,str2st t1) else if String.eqb x l2 then Some(s2, CIH c0) else None)).
       - clear H. revert c. cofix CIH. intros.
         case_eq c; intros.
         + exact (str_send s (fun _ => None)).
         + destruct p as ((l1,s1),t1).
           case_eq c0; intros.
           + exact(str_send s (fun x => if String.eqb x l1 then Some(s1,str2st t1) else None)).
           + destruct p as ((l2,s2),t2).
             exact(str_send s (fun x => if String.eqb x l1 then Some(s1,str2st t1) else Some(s2, CIH c0))).
Defined.

CoFixpoint et2F := st_receive "q" [| ("l8"%string, sint, et2F); ("l9"%string, snat, et2F) |].

CoFixpoint Et2F := str_receive "q" 
(fun l =>
   if String.eqb l "l8"%string then Some (sint, Et2F)
   else if String.eqb l "l9"%string then Some (snat, Et2F)
   else None
).

Lemma asd: str_equivC (str2st et2F) Et2F.
Proof. pcofix CIH.
       rewrite(str_eq(str2st et2F)).
       rewrite(str_eq Et2F). simpl.
       pfold. constructor.
       intros.
       case_eq((l =? "l8")%string); intros.
       - split. easy. right. exact CIH.
       - case_eq((l =? "l9")%string); intros.
         + split. easy.
           rewrite(str_eq ((cofix CIH0 (c : coseq (string * sort * st)) : str :=
      match c as c0 return (c = c0 -> str) with
      | [||] => fun _ : c = [||] => str_receive "q" (fun _ : string => None)
      | cocons p c0 =>
          fun H1 : c = cocons p c0 =>
          (let (p0, s) as p0 return (c = cocons p0 c0 -> str) := p in
           (let (s0, s1) as p1 return (forall s0 : st, c = cocons (p1, s0) c0 -> str) := p0 in
            fun (t1 : st) (_ : c = cocons (s0, s1, t1) c0) =>
            match c0 as c1 return (c0 = c1 -> str) with
            | [||] => fun _ : c0 = [||] => str_receive "q" (fun x : string => if (x =? s0)%string then Some (s1, str2st t1) else None)
            | cocons p1 c1 =>
                fun H2 : c0 = cocons p1 c1 =>
                (let (p2, s2) as p2 return (c0 = cocons p2 c1 -> str) := p1 in
                 (let (s3, s4) as p3 return (forall s3 : st, c0 = cocons (p3, s3) c1 -> str) := p2 in
                  fun (t2 : st) (_ : c0 = cocons (s3, s4, t2) c1) =>
                  str_receive "q"
                    (fun x : string => if (x =? s0)%string then Some (s1, str2st t1) else if (x =? s3)%string then Some (s4, CIH0 c0) else None))
                   s2) H2
            end eq_refl) s) H1
      end eq_refl) [|("l9"%string, N, et2F)|])).
      simpl.
      left. pfold.
       rewrite(str_eq Et2F). simpl.
       constructor.
       intros.
       case_eq((l0 =? "l9")%string); intros.
       case_eq((l0 =? "l8")%string); intros.
       
      rewrite(str_eq Et2F).
      simpl.
      admit.
      split. easy. right. exact CIH.
      
      
 *)
CoFixpoint st2soFF (t: str) (l: coseq label) (F: label -> option (coseq label)): str :=
  match t with
    | str_send p f    =>
      match l with
        | cocons a xs =>
          match f a with
            | Some (s,t') => str_send p (fun l1 => if String.eqb l1 a then Some(s,st2soFF t' xs F) else None) 
            | None        => str_send p (fun _ => None)
          end
        | _           => str_send p (fun _ => None)
      end
    | str_receive p f => 
(*       match l with
        | conil => *)
          str_receive p
          (fun l1 =>
           match f l1 with
             | None        => None
             | Some (s,t') => 
               match (F l1) with
                 | None    => None
                 | Some xs => Some(s, st2soFF t' xs F)
               end
           end
         )
(*         | _     => str_receive p (fun _ => None)
      end *)
    | str_end         => str_end
  end.

CoFixpoint st2siFF (t: str) (l: coseq label) (F: label -> option (coseq label)): str :=
  match t with
    | str_receive p f     =>
      match l with
        | cocons a xs =>
          match f a with
            | Some (s,t') => str_receive p (fun l1 => if String.eqb l1 a then Some(s,st2siFF t' xs F) else None) 
            | None        => str_receive p (fun _ => None)
          end
        | _           => str_receive p (fun _ => None)
      end
    | str_send p f        => 
(*       match l with
        | conil => *)
          str_send p
          (fun l1 =>
           match f l1 with
             | None        => None
             | Some (s,t') => 
             match F l1 with
               | None    => None
               | Some xs => Some(s, st2siFF t' xs F)
             end
           end
          )
(*         | _     => str_send p (fun _ => None)
      end *)
    | _             => str_end
  end.

CoFixpoint st2sisoLL (t: str) (l1 l2: coseq label) : str :=
  match t with
    | str_send p f     =>
      match l1 with
        | cocons a xs =>
          match f a with
            | Some (s,t') => str_send p (fun l1 => if String.eqb l1 a then Some(s,st2sisoLL t' xs l2) else None)
            | None        => str_send p (fun _ => None)
          end
        | _           => str_send p (fun _ => None)
      end
    | str_receive p f  =>
      match l2 with
        | cocons a xs =>
          match f a with
            | Some (s,t') => str_receive p (fun l2  => if String.eqb l2 a then Some(s,st2sisoLL t' l1 xs) else None) 
            | None        => str_receive p (fun _ => None)
          end
        | _           => str_receive p (fun _ => None)
      end
    | str_end          => str_end
  end.

CoFixpoint st2sisoFF (t: str) (l1: coseq label) (F1: label -> option (coseq label)) (l2: coseq label) (F2: label -> option (coseq label)): str :=
  match t with
    | str_send p f    =>
      match l1 with
        | cocons a xs =>
          match f a with
            | Some (s,t') => str_send p (fun l => (if String.eqb l a then 
                                                   match (F2 a) with
                                                     | Some ys => Some (s, st2sisoFF t' xs F1 ys F2) 
                                                     | _       => None
                                                   end
                                                   else None
                                                  )
                                         )
            | None        => str_send p (fun _ => None)
          end
        | _           => str_send p (fun _ => None)
      end
    | str_receive p f    =>
      match l2 with
        | cocons a xs =>
          match f a with
            | Some (s,t') => str_receive p (fun l => (if String.eqb l a then 
                                                      match (F1 a) with
                                                        | Some ys => Some (s, st2sisoFF t' ys F1 xs F2) 
                                                        | _       => None
                                                      end
                                                      else None
                                                     )
                                           )
            | None        => str_receive p (fun _ => None)
          end
        | _           => str_receive p (fun _ => None)
      end
    | _ => str_end
  end.

Inductive feqso (R: str -> (label -> option (coseq label)) -> (label -> option (coseq label)) -> Prop): 
  str -> (label -> option (coseq label)) -> (label -> option (coseq label)) -> Prop :=
  | seqe: forall F1 F2, feqso R str_end F1 F2
  | seqs: forall p f F1 F2, (forall l, (exists s t, f l = Some(s,t) /\ F1 l = F2 l /\ R t F1 F2) \/ f l = None) -> feqso R (str_send p f) F1 F2
  | seqr: forall p f F1 F2, (forall l, (exists s t, f l = Some(s,t) /\ R t F1 F2) \/ f l = None) -> feqso R (str_receive p f) F1 F2.

Definition feqsoc t F1 F2 := paco3 feqso bot3 t F1 F2.

Lemma eqsoffl: forall t l F1 F2, feqsoc t F1 F2 -> str_equivC (st2siFF t l F1) (st2siFF t l F2).
Proof. pcofix CIH.
       intros.
       destruct t.
       - pinversion H0. subst.
         rewrite(str_eq(st2siFF str_end l F2)).
         rewrite(str_eq(st2siFF str_end l F1)). simpl.
         pfold. constructor.
         admit.
       - pinversion H0. subst.
         pfold.
         rewrite(str_eq(st2siFF (str_receive s o) l F1)).
         rewrite(str_eq(st2siFF (str_receive s o) l F2)). simpl.
         case_eq l; intros.
         + constructor. easy.
         + case_eq(o s0); intros.
           destruct p as (s1, t1).
           specialize(H4 s0).
           destruct H4 as [(s4,(t4,(H4a,H4b))) | H4].
           constructor.
           intros l2.
           case_eq((l2 =? s0)%string); intros.
           ++ split. easy. right. apply CIH.
              rewrite H4a in H1. inversion H1. subst.
              destruct H4b; easy.
           ++ easy. 
           rewrite H1 in H4. easy.
           constructor. easy. admit.
       - pinversion H0. subst.
         rewrite(str_eq(st2siFF (str_send s o) l F1)).
         rewrite(str_eq(st2siFF (str_send s o) l F2)). simpl.
         pfold. constructor.
         intro l1.
         case_eq(o l1); intros.
         + destruct p as (s1, t1).
           case_eq(F1 l1); intros.
           ++ case_eq(F2 l1); intros.
              specialize(H4 l1).
              destruct H4 as [(s4,(t4,(H4a,(H4b,H4c)))) | H4].
              rewrite H1 H2 in H4b.
              inversion H4b. subst.
              split. easy. right. apply CIH.
              rewrite H in H4a. inversion H4a. subst.
              destruct H4c; easy.
              rewrite H4 in H. easy.
              specialize(H4 l1).
              destruct H4 as [(s4,(t4,(H4a,(H4b,H4c)))) | H4].
              rewrite H1 H2 in H4b. easy.
              rewrite H4 in H. easy.
           ++ case_eq(F2 l1); intros.
              specialize(H4 l1).
              destruct H4 as [(s4,(t4,(H4a,(H4b,H4c)))) | H4].
              rewrite H1 H2 in H4b. easy.
              rewrite H4 in H. easy. easy. easy.
              admit.
Admitted.

Lemma fsame: forall {a b: Type} (f1 f2: a -> b), f1 = f2 -> (forall x, f1 x = f2 x).
Proof. intros. subst. easy. Qed.

Lemma eqs: forall t l1 F1 l2 F2, str_equivC (st2siFF (st2soFF t l1 F1) l2 F2) (st2sisoFF t l1 F1 l2 F2).
Proof. pcofix CIH. intros.
       destruct t.
       - rewrite(str_eq(st2sisoFF str_end l1 F1 l2 F2)). simpl.
         rewrite(str_eq(st2siFF (st2soFF str_end l1 F1) l2 F2)). simpl.
         pfold. constructor.
       - rewrite(str_eq(st2siFF (st2soFF (str_receive s o) l1 F1) l2 F2)). simpl.
         rewrite(str_eq(st2sisoFF (str_receive s o) l1 F1 l2 F2)). simpl.
         case_eq l2; intros.
         + pfold. constructor. easy.
         + case_eq(o s0); intros.
           ++ destruct p.
              case_eq(F1 s0); intros.
              * pfold. constructor.
                intros.
                case_eq((l =? s0)%string); intros.
                ** split. easy. right. apply CIH. easy.
                ** pfold. constructor. intros.
                   destruct((l =? s0)%string); easy.
           ++ pfold. constructor. easy.
       - rewrite(str_eq(st2sisoFF (str_send s o) l1 F1 l2 F2)). simpl.
         rewrite(str_eq(st2siFF (st2soFF (str_send s o) l1 F1) l2 F2)). simpl.
         case_eq l1; intros.
         + pfold. constructor. easy.
         + case_eq(o s0); intros.
           ++ destruct p.
              pfold. constructor.
              intros.
              case_eq((l =? s0)%string); intros.
              ** rewrite String.eqb_eq in H1. subst.
                 case_eq(F2 s0); intros.
                 *** split. easy. right. apply CIH. easy. easy.
           ++ pfold. constructor. easy.
Qed.

Lemma Eqs: forall t l1 F1 l2 F2, (st2siFF (st2soFF t l1 F1) l2 F2) = (st2sisoFF t l1 F1 l2 F2).
Proof. intros.
       apply strExt, eqs.
Qed.

Inductive sodec (R: str -> coseq label -> (label -> option (coseq label)) -> Prop): str -> coseq label -> (label -> option (coseq label)) -> Prop :=
  | sodec_end: forall F, sodec R str_end conil F
  | sodec_snd: forall p f x xs F, (F x = Some conil /\ exists s t, f x = Some(s,t) /\ R t xs F) -> sodec R (str_send p f) (cocons x xs) F
  | sodec_rcv: forall p f F, (forall l, (exists s t xs, f l = Some(s,t) /\ F l = Some xs /\ R t xs F) \/ f l = None) -> sodec R (str_receive p f) conil F.

Definition sodecc t l1 F1 := paco3 sodec bot3 t l1 F1.

Inductive sidec (R: str -> coseq label -> (label -> option (coseq label)) -> Prop): str -> coseq label -> (label -> option (coseq label)) -> Prop :=
  | sidec_end: forall F, sidec R str_end conil F
  | sidec_rcv: forall p f x xs F, (F x = Some conil /\ exists s t, f x = Some(s,t) /\ R t xs F) -> sidec R (str_receive p f) (cocons x xs) F
  | sidec_snd: forall p f F, (forall l, (exists s t xs, f l = Some(s,t) /\ F l = Some xs /\ R t xs F) \/ f l = None) -> sidec R (str_send p f) conil F.

Definition sidecc t l1 F1 := paco3 sidec bot3 t l1 F1.

Inductive sisodec (R: str -> coseq label -> (label -> option (coseq label)) -> coseq label -> (label -> option (coseq label)) -> Prop): str -> coseq label -> (label -> option (coseq label)) -> coseq label -> (label -> option (coseq label)) -> Prop :=
  | dec_end: forall F1 F2, sisodec R str_end conil F1 conil F2
  | dec_snd1: forall p f x xs F1 F2, xs <> conil -> (F1 x = None /\ exists s t, f x = Some(s,t) /\ F2 x = Some conil /\ R t xs F1 conil F2) -> sisodec R (str_send p f) (cocons x xs) F1 conil F2
  | dec_snd2: forall p f x F1 F2, (F1 x = None /\ exists s t, f x = Some(s,t) /\ exists ys, F2 x = Some ys /\ R t conil F1 ys F2) -> sisodec R (str_send p f) (cocons x conil) F1 conil F2
  | dec_rcv1: forall p f F1 x xs F2, xs <> conil -> (F2 x = None /\ exists s t, f x = Some(s,t) /\ F1 x = Some conil /\ R t conil F1 xs F2) -> sisodec R (str_receive p f) conil F1 (cocons x xs) F2
  | dec_rcv2: forall p f F1 x F2, (F2 x = None /\ exists s t, f x = Some(s,t) /\ exists ys, F1 x = Some ys /\ R t ys F1 conil F2) -> sisodec R (str_receive p f) conil F1 (cocons x conil) F2.

Definition sisodecc t l1 F1 l2 F2 := paco5 sisodec bot5 t l1 F1 l2 F2.

Lemma mon_decs: monotone5 sisodec.
Proof. unfold monotone5.
       intros.
       induction IN; intros.
       - constructor.
       - constructor. easy.
         destruct H0 as (H0d,(s0,(t0,(H0a,(H0b,H0c))))).
         split. easy.
         exists s0. exists t0. split. easy. split. easy.
         apply LE. easy.
         destruct H as (H0d,(s0,(t0,(H0a,(ys,(H0b,H0c)))))).
         apply dec_snd2. split. easy.
         exists s0. exists t0. split. easy. exists ys. split. easy.
         apply LE. easy.
       - constructor. easy.
         destruct H0 as (H0d,(s0,(t0,(H0a,(H0b,H0c))))).
         split. easy.
         exists s0. exists t0. split. easy. split. easy.
         apply LE. easy.
         destruct H as (H0d,(s0,(t0,(H0a,(ys,(H0b,H0c)))))).
         apply dec_rcv2. split. easy.
         exists s0. exists t0. split. easy. exists ys. split. easy.
         apply LE. easy.
Qed.

Inductive wfT (R: str -> Prop): str -> Prop :=
  | wft_end: wfT R str_end
  | wft_rcv: forall p f, (forall l s t, f l = Some(s,t) -> R t) -> wfT R (str_receive p f)
  | wft_snd: forall p f, (forall l s t, f l = Some(s,t) -> R t) -> wfT R (str_send p f).

Definition wfTC t := paco1 wfT bot1 t.

Require Import Setoid.
Require Import Morphisms JMeq.
Parameter P: relation str.
Axiom transP: Transitive P.

Inductive substr: str -> str -> Prop :=
  | csubstr: forall T T',
             wfTC T ->
             wfTC T' ->
             (forall l1 F1, sodecc T l1 F1 /\
              forall l2 F2, sidecc T' l2 F2 /\
              exists l3 F3, sidecc (st2siFF T l1 F1) l3 F3 /\
              exists l4 F4, sodecc (st2soFF T' l2 F2) l4 F4 /\
              P (st2sisoFF T l1 F1 l3 F3) (st2sisoFF T' l4 F4 l2 F2)
             ) ->
             substr T T'.

Inductive recvsingl (R: str -> Prop): str -> Prop :=
  | endr : recvsingl R str_end
  | recvr: forall p f, (forall l, (exists s t, (f l) = Some(s,t) /\ R t) \/ f l = None) -> recvsingl R (str_receive p f)
  | sendr: forall p f, (exists l s t, f l = Some(s,t) /\ (forall l1 s1 t1, f l1 = Some(s1, t1) -> l = l1) /\ R t) -> recvsingl R (str_send p f).

Definition recvsinglc t  := paco1 recvsingl bot1 t.

Lemma singlSo: forall t l F, sodecc t l F -> recvsinglc(st2soFF t l F).
Proof. pcofix CIH.
       intros.
       pinversion H0.
       - subst. rewrite(str_eq(st2soFF str_end [||] F)). simpl.
         pfold. constructor.
       - subst. 
         destruct H as (Ha,(s,(t,(Hc,Hd)))).
         rewrite(str_eq(st2soFF (str_send p f) (cocons x xs) F)). simpl.
         rewrite Hc. pfold.
         constructor.
         exists x. exists s. exists (st2soFF t xs F).
         split.
         rewrite String.eqb_refl. easy.
         split.
         intros.
         case_eq((l1 =? x)%string); intros.
         + rewrite String.eqb_eq in H1. easy.
         + rewrite H1 in H. easy.
         right. apply CIH. 
         destruct Hd; easy.
       - subst.
         rewrite(str_eq(st2soFF (str_receive p f) [||] F)). simpl.
         pfold. constructor.
         intros l.
         specialize(H l).
         destruct H as [(s1,(t1,(xs1,(Ha,(Hb,Hc)))))|H]. 
         + left. exists s1. exists (st2soFF t1 xs1 F). rewrite Ha Hb.
           split. easy. 
           right. apply CIH.
           destruct Hc; easy.
         + right. rewrite H. easy.
         admit.
Admitted.

Lemma wftsnd: forall t l F, wfTC t -> sodecc t l F -> wfTC (st2soFF t l F).
Proof. pcofix CIH.
       intros.
       specialize(singlSo t l F H1); intros HH.
       pinversion H0.
       - subst. pfold.
         rewrite(str_eq(st2soFF str_end l F)). simpl.
         constructor.
       - subst.
         rewrite(str_eq(st2soFF (str_receive p f) l F)). simpl.
         pinversion H1. subst.
         pfold. constructor.
         intros.
         specialize(H6 l).
         destruct H6 as [(s5,(t5,(xs5,(H5a,(H5b,H5c)))))|H5].
         rewrite H5a H5b in H2.
         inversion H2. subst.
         right. apply CIH.
         specialize(H l s t5 H5a).
         destruct H; easy.
         destruct H5c; easy.
         rewrite H5 in H2. easy.
         admit.
       - subst.
         pinversion H1. subst.
         rewrite(str_eq(st2soFF (str_send p f) (cocons x xs) F)). simpl.
         pfold.
         destruct H6 as (H6a,(s,(t,(H6b,H6c)))).
         rewrite(str_eq(st2soFF (str_send p f) (cocons x xs) F)) in HH. simpl in HH.
         rewrite H6b in HH.
         pinversion HH.
         subst.
         rewrite H6b.
         constructor.
         destruct H3 as (l1,(s1,(t1,(H3a,(H3b,H3c))))).
         intros.
         specialize(H3b x s (st2soFF t xs F)).
         rewrite String.eqb_refl in H3b.
         specialize(H3b eq_refl). subst.
         rewrite String.eqb_refl in H3a. inversion H3a. subst.
         case_eq((l =? x)%string); intros.
         + rewrite H3 in H2.
           inversion H2. subst.
           right. apply CIH.
           specialize(H x s0 t H6b).
           rewrite String.eqb_eq in H3. subst.
           destruct H; easy.
           destruct H6c; easy.
         + rewrite H3 in H2. easy.
         admit.
         admit.
         admit.
Admitted.

Inductive sendsingl (R: str -> Prop): str -> Prop :=
  | ends : sendsingl R str_end
  | sends: forall p f, (forall l, (exists s t, (f l) = Some(s,t) /\ R t) \/ f l = None) -> sendsingl R (str_send p f)
  | recvs: forall p f, (exists l s t, f l = Some(s,t) /\ (forall l1 s1 t1, f l1 = Some(s1, t1) -> l = l1) /\ R t) -> sendsingl R (str_receive p f).

Definition sendsinglc t  := paco1 sendsingl bot1 t.

Lemma singlSi: forall t l F, sidecc t l F -> sendsinglc(st2siFF t l F).
Proof. pcofix CIH.
       intros.
       pinversion H0.
       - subst. rewrite(str_eq(st2siFF str_end [||] F)). simpl.
         pfold. constructor.
       - subst. 
         destruct H as (Ha,(s,(t,(Hc,Hd)))).
         rewrite(str_eq(st2siFF (str_receive p f) (cocons x xs) F)). simpl.
         rewrite Hc. pfold.
         constructor.
         exists x. exists s. exists (st2siFF t xs F).
         split.
         rewrite String.eqb_refl. easy.
         split.
         intros.
         case_eq((l1 =? x)%string); intros.
         + rewrite String.eqb_eq in H1. easy.
         + rewrite H1 in H. easy.
         right. apply CIH. 
         destruct Hd; easy.
       - subst.
         rewrite(str_eq(st2siFF (str_send p f) [||] F)). simpl.
         pfold. constructor.
         intros l.
         specialize(H l).
         destruct H as [(s1,(t1,(xs1,(Ha,(Hb,Hc)))))|H]. 
         + left. exists s1. exists (st2siFF t1 xs1 F). rewrite Ha Hb.
           split. easy. 
           right. apply CIH.
           destruct Hc; easy.
         + right. rewrite H. easy.
         admit.
Admitted.

Lemma wftrcv: forall t l F, wfTC t -> sidecc t l F -> wfTC (st2siFF t l F).
Proof. pcofix CIH.
       intros.
       specialize(singlSi t l F H1); intros HH.
       pinversion H0.
       - subst. pfold.
         rewrite(str_eq(st2siFF str_end l F)). simpl.
         constructor.
       - subst.
         pinversion H1. subst.
         rewrite(str_eq(st2siFF (str_receive p f) (cocons x xs) F)). simpl.
         pfold.
         destruct H6 as (H6a,(s,(t,(H6b,H6c)))).
         rewrite(str_eq(st2siFF (str_receive p f) (cocons x xs) F)) in HH. simpl in HH.
         rewrite H6b in HH.
         pinversion HH.
         subst.
         rewrite H6b.
         constructor.
         destruct H3 as (l1,(s1,(t1,(H3a,(H3b,H3c))))).
         intros.
         specialize(H3b x s (st2siFF t xs F)).
         rewrite String.eqb_refl in H3b.
         specialize(H3b eq_refl). subst.
         rewrite String.eqb_refl in H3a. inversion H3a. subst.
         case_eq((l =? x)%string); intros.
         + rewrite H3 in H2.
           inversion H2. subst.
           right. apply CIH.
           specialize(H x s0 t H6b).
           rewrite String.eqb_eq in H3. subst.
           destruct H; easy.
           destruct H6c; easy.
         + rewrite H3 in H2. easy.
         admit.
         admit.
       - subst.
         rewrite(str_eq(st2siFF (str_send p f) l F)). simpl.
         pinversion H1. subst.
         pfold. constructor.
         intros.
         specialize(H6 l).
         destruct H6 as [(s5,(t5,(xs5,(H5a,(H5b,H5c)))))|H5].
         rewrite H5a H5b in H2.
         inversion H2. subst.
         right. apply CIH.
         specialize(H l s t5 H5a).
         destruct H; easy.
         destruct H5c; easy.
         rewrite H5 in H2. easy.
         admit.
         admit.
Admitted.


Inductive singletonH (R: str -> Prop): str -> Prop :=
  | endsr : singletonH R str_end
  | sendsr: forall p f, (exists !l s t, (f l) = Some(s,t) /\ R t) -> singletonH R (str_send p f)
  | recvsr: forall p f, (exists !l s t, (f l) = Some(s,t) /\ R t) -> singletonH R (str_receive p f).

Definition singleton s := paco1 (singletonH) bot1 s.

CoFixpoint mergeLL (l: list label) (w: coseq label): coseq label :=
  match l with
    | x::xs => cocons x (mergeLL xs w)
    | []    => w
  end.

Inductive coseqInG {A: Type}: A -> coseq A -> Prop :=
  | CoInSplit1G x xs y ys: xs = cocons y ys -> x = y  -> coseqInG x xs
  | CoInSplit2G x xs y ys: xs = cocons y ys -> x <> y -> coseqInG x ys -> coseqInG x xs.

Lemma invert0: forall t x xs F1 F2, sisodecc t (cocons x xs) F1 conil F2 -> 
  (xs <> conil /\ (F1 x = None /\ exists p f, t = str_send p f /\ exists s' t', f x = Some (s', t') /\ F2 x = Some conil /\ sisodecc t' xs F1 conil F2))
    \/
  (xs = conil /\ F1 x = None /\ exists p f, t = str_send p f /\ exists s' t', f x = Some (s', t') /\ exists ys, F2 x = Some ys /\ sisodecc t' conil F1 ys F2).
Proof. intros.
       pinversion H. subst.
       destruct H5 as (H5d,(s5,(t5,(H5a,(H5b,H5c))))).
       left. split. easy. split. easy.
       exists p. exists f.
       split. easy.
       exists s5. exists t5. split. easy.
       destruct H5c; easy.

       subst.
       right. 
       destruct H4 as (H5d,(s5,(t5,(H5a,(ys,(H5b,H5c)))))).
       split. easy. split. easy.
       exists p. exists f.
       split. easy.
       exists s5. exists t5. split. easy.
       exists ys. split. easy. destruct H5c; easy.
       apply mon_decs.
Qed.

Lemma invert1: forall t x xs y ys F1 F2, sisodecc t (cocons x xs) F1 (cocons y ys) F2 -> False.
Proof. intros.
       pinversion H.
       apply mon_decs.
Qed.

Lemma invert2: forall t x xs F1 F2, sisodecc t conil F1 (cocons x xs) F2 -> 
  (xs <> conil /\ (F2 x = None /\ exists p f, t = str_receive p f /\ exists s' t', f x = Some (s', t') /\ F1 x = Some conil /\ sisodecc t' conil F1 xs F2))
    \/
  (xs = conil  /\ F2 x = None /\ exists p f, t = str_receive p f /\ exists s' t', f x = Some (s', t') /\ exists ys, F1 x = Some ys /\ sisodecc t' ys F1 conil F2).
Proof. intros.
       pinversion H. subst.
       destruct H5 as (H5d,(s5,(t5,(H5a,(H5b,H5c))))).
       left. intros. split. easy. split. easy.
       exists p. exists f.
       split. easy.
       exists s5. exists t5. split. easy.
       destruct H5c; easy.

       subst.
       right.
       destruct H4 as (H5d,(s5,(t5,(H5a,(ys,(H5b,H5c)))))).
       split. easy. split. easy.
       exists p. exists f.
       split. easy.
       exists s5. exists t5. split. easy.
       exists ys. split. easy. destruct H5c; easy.
       apply mon_decs.
Qed.

Lemma invSingl: forall t l1 F1 l2 F2, sisodecc t l1 F1 l2 F2 -> singleton(st2sisoFF t l1 F1 l2 F2).
Proof. pcofix CIH.
       intros.
       case_eq l1; case_eq l2; intros.
       - subst. pinversion H0. subst. pfold.
         rewrite(str_eq(st2sisoFF str_end [||] F1 [||] F2)). simpl. constructor.
         apply mon_decs.
       - subst.
         apply invert2 in H0.
         destruct H0 as [H0 | H0].
         + destruct H0 as (Hu,(Hv,(p,(f,(H0a,(s0,(t0,(H0b,(H0c,H0d))))))))).
           subst.
           rewrite(str_eq(st2sisoFF (str_receive p f) [||] F1 (cocons s c) F2)). simpl.
           rewrite H0b. pfold. constructor.
           exists s. unfold unique. rewrite String.eqb_refl.
           split.
           exists s0. split.
           exists(st2sisoFF t0 [||] F1 c F2).
           split. split. rewrite H0c. easy. right. apply CIH. easy.
           intros. rewrite H0c in H.
           destruct H as (Ha,Hb).
           inversion Ha. subst. easy.
           intros. destruct H as (x,(Ha,Hb)).
           rewrite H0c in Ha.
           destruct Ha as (Ha,Hc). inversion Ha. easy.
           intros. destruct H as (x,((x0,(Ha,Hb)),Hc)).
           rewrite H0c in Ha.
           case_eq((x' =? s)%string); intros.
           rewrite String.eqb_eq in H. easy.
           rewrite H in Ha. easy.
         + destruct H0 as (Hu,(Hv,(p,(f,(H0a,(s0,(t0,(H0b,(ys,(H0c,H0d)))))))))).
           subst.
           rewrite(str_eq(st2sisoFF (str_receive p f) [||] F1 [|s|] F2)). simpl.
           rewrite H0b.
           pfold. constructor.
           exists s. unfold unique. rewrite String.eqb_refl.
           split.
           exists s0. split.
           rewrite H0c.
           exists(st2sisoFF t0 ys F1 [||] F2).
           split. split. easy. right. apply CIH. easy.
           intros.
           destruct H as (Ha,Hc). inversion Ha. easy.
           intros. destruct H as (x,((Ha,Hb),Hc)).
           rewrite H0c in Ha.
           inversion Ha. easy.
           intros. destruct H as (x,((x0,(Ha,Hb)),Hc)).
           rewrite H0c in Ha.
           case_eq((x' =? s)%string); intros.
           rewrite String.eqb_eq in H. easy.
           rewrite H in Ha. easy.
       - subst.
         apply invert0 in H0.
         destruct H0 as [H0 | H0].
         + destruct H0 as (Hu,(Hv,(p,(f,(H0a,(s0,(t0,(H0b,(H0c,H0d))))))))).
           subst.
           rewrite(str_eq(st2sisoFF (str_send p f) (cocons s c) F1 [||] F2)). simpl.
           rewrite H0b. pfold. constructor.
           exists s. unfold unique. rewrite String.eqb_refl.
           split.
           exists s0. split.
           exists(st2sisoFF t0 c F1 [||] F2).
           split. split. rewrite H0c. easy. right. apply CIH. easy.
           intros. rewrite H0c in H.
           destruct H as (Ha,Hb).
           inversion Ha. subst. easy.
           intros. destruct H as (x,(Ha,Hb)).
           rewrite H0c in Ha.
           destruct Ha as (Ha,Hc). inversion Ha. easy.
           intros. destruct H as (x,((x0,(Ha,Hb)),Hc)).
           rewrite H0c in Ha.
           case_eq((x' =? s)%string); intros.
           rewrite String.eqb_eq in H. easy.
           rewrite H in Ha. easy.
         + destruct H0 as (Hu,(Hv,(p,(f,(H0a,(s0,(t0,(H0b,(ys,(H0c,H0d)))))))))).
           subst.
           rewrite(str_eq(st2sisoFF (str_send p f) [|s|] F1 [||] F2)). simpl.
           rewrite H0b.
           pfold. constructor.
           exists s. unfold unique. rewrite String.eqb_refl.
           split.
           exists s0. split.
           rewrite H0c.
           exists(st2sisoFF t0 [||] F1 ys F2).
           split. split. easy. right. apply CIH. easy.
           intros.
           destruct H as (Ha,Hc). inversion Ha. easy.
           intros. destruct H as (x,((Ha,Hb),Hc)).
           rewrite H0c in Ha.
           inversion Ha. easy.
           intros. destruct H as (x,((x0,(Ha,Hb)),Hc)).
           rewrite H0c in Ha.
           case_eq((x' =? s)%string); intros.
           rewrite String.eqb_eq in H. easy.
           rewrite H in Ha. easy.
       - subst. apply invert1 in H0. easy.
Qed.

Lemma eq00: forall t l1 F1 l2 F2,
  str_equivC (st2soFF (st2siFF t l1 F1) l2 F2) (st2siFF (st2soFF t l2 F2) l1 F1).
Proof. pcofix CIH.
       intros.
       destruct t.
       - rewrite(str_eq(st2soFF (st2siFF str_end l1 F1) l2 F2) ).
         rewrite(str_eq(st2siFF (st2soFF str_end l2 F2) l1 F1)). simpl.
         pfold. constructor.
       - rewrite(str_eq((st2soFF (st2siFF (str_receive s o) l1 F1) l2 F2))).
         rewrite(str_eq(st2siFF (st2soFF (str_receive s o) l2 F2) l1 F1)). simpl.
         destruct l1. pfold. constructor. easy.
         destruct(o s0). destruct p.
         case_eq(F2 s0); intros.
         pfold. constructor.
         intros.
         case_eq((l =? s0)%string); intros.
         + rewrite String.eqb_eq in H0. subst.
           rewrite H. split. easy.
           right. apply CIH.
         + easy.
         pfold. constructor.
         intros.
         case_eq((l =? s0)%string); intros.
         + rewrite String.eqb_eq in H0. subst.
           rewrite H. easy. easy.
           pfold. constructor. easy.
       - rewrite(str_eq(st2soFF (st2siFF (str_send s o) l1 F1) l2 F2)).
         rewrite(str_eq(st2siFF (st2soFF (str_send s o) l2 F2) l1 F1)). simpl.
         destruct l2.
         pfold. constructor. easy.
         case_eq(o s0); intros.
         + destruct p. 
           case_eq(F1 s0); intros.
           ++ pfold. constructor.
              intros.
              case_eq((l =? s0)%string); intros.
              * rewrite String.eqb_eq in H1. subst.
                rewrite H0.
                split. easy. right. apply CIH.
              * easy.
           ++ pfold. constructor.
              intros.
              case_eq((l =? s0)%string); intros.
              * rewrite String.eqb_eq in H1. subst.
                rewrite H0. easy.
              * easy.
         + pfold. constructor.
           easy.
Qed.

Lemma eq11: forall t l1 F1 l2 F2,
  str_equivC (st2siFF (st2soFF t l1 F1) l2 F2) (st2soFF (st2siFF t l2 F2) l1 F1).
Proof. pcofix CIH.
       intros.
       destruct t.
       - rewrite(str_eq(st2siFF (st2soFF str_end l1 F1) l2 F2) ).
         rewrite(str_eq(st2soFF (st2siFF str_end l2 F2) l1 F1)). simpl.
         pfold. constructor.
       - rewrite(str_eq((st2siFF (st2soFF (str_receive s o) l1 F1) l2 F2))).
         rewrite(str_eq(st2soFF (st2siFF (str_receive s o) l2 F2) l1 F1)). simpl.
         destruct l2. pfold. constructor. easy.
         destruct(o s0). destruct p.
         case_eq(F1 s0); intros.
         pfold. constructor.
         intros.
         case_eq((l =? s0)%string); intros.
         + rewrite String.eqb_eq in H0. subst.
           rewrite H. split. easy.
           right. apply CIH.
         + easy.
         pfold. constructor.
         intros.
         case_eq((l =? s0)%string); intros.
         + rewrite String.eqb_eq in H0. subst.
           rewrite H. easy. easy.
           pfold. constructor. easy.
       - rewrite(str_eq(st2siFF (st2soFF (str_send s o) l1 F1) l2 F2)).
         rewrite(str_eq(st2soFF (st2siFF (str_send s o) l2 F2) l1 F1)). simpl.
         destruct l1.
         pfold. constructor. easy.
         case_eq(o s0); intros.
         + destruct p. 
           case_eq(F2 s0); intros.
           ++ pfold. constructor.
              intros.
              case_eq((l =? s0)%string); intros.
              * rewrite String.eqb_eq in H1. subst.
                rewrite H0.
                split. easy. right. apply CIH.
              * easy.
           ++ pfold. constructor.
              intros.
              case_eq((l =? s0)%string); intros.
              * rewrite String.eqb_eq in H1. subst.
                rewrite H0. easy.
              * easy.
         + pfold. constructor.
           easy.
Qed.

Lemma _3_15: forall t l1 l2 F1 F2,
  (st2siFF (st2soFF t l1 F1) l2 F2) = (st2soFF (st2siFF t l2 F2) l1 F1).
Proof. intros.
       apply strExt, eq11.
Qed.


CoFixpoint Et1F := str_receive "q" 
(fun l =>
   if String.eqb l "l7"%string then Some (sint, Et1F)
   else None
).

CoFixpoint Et2F := str_receive "q" 
(fun l =>
   if String.eqb l "l8"%string then Some (sint, Et2F)
   else None
).

CoFixpoint eT1F := str_receive "p" 
  (fun l =>
     if String.eqb l "l1"%string then
          Some(sint, str_send "p"
            (fun l =>
               if String.eqb l "l4"%string then Some(sint, Et1F) else if String.eqb l "l5"%string then Some(sint, Et2F) else if String.eqb l "l6"%string then Some(sint, eT1F) else None
            )
          )
     else if String.eqb l "l2"%string then
          Some(sint, str_send "q"
            (fun l =>
               if String.eqb l "l9"%string then Some(sint, eT1F) else None
            )
          )
     else if String.eqb l "l3"%string then
         Some(sint, str_receive "q"
            (fun l =>
               if String.eqb l "l10"%string then Some(sint, eT1F) else None
            )
          )
     else None 
  ).

CoFixpoint eT2F := str_receive "p" 
  (fun l =>
     if String.eqb l "l1"%string then
          Some(sint, str_send "p"
            (fun l =>
               if String.eqb l "l6"%string then Some(sint, eT2F) else None
            )
          )
     else if String.eqb l "l2"%string then
          Some(sint, str_send "q"
            (fun l =>
               if String.eqb l "l9"%string then Some(sint, eT2F) else None
            )
          )
     else if String.eqb l "l3"%string then
          Some(sint, str_receive "q"
            (fun l =>
               if String.eqb l "l10"%string then Some(sint, eT2F) else None
            )
          )
     else None 
  ).

CoFixpoint col6 := cocons "l6"%string col6.
CoFixpoint col9 := cocons "l9"%string col9.

Definition FF: label -> option (coseq label) :=
  fun l => 
    if String.eqb l "l1"%string then Some col6 
    else if String.eqb l "l2"%string then Some col9 
    else if String.eqb l "l3"%string then Some conil 
    else if String.eqb l "l10"%string then Some conil
    else None.

Lemma sodecex: forall c, str_equivC eT2F (st2soFF eT1F c FF).
Proof. pcofix CIH. intros.
       rewrite(str_eq(eT2F)). simpl.
       rewrite(str_eq(st2soFF eT1F c FF)). simpl.
       pfold. constructor.
       intros.
       case_eq (String.eqb l "l1"%string); intros.
       - rewrite String.eqb_eq in H. rewrite H.
         simpl.
         split. easy.
         left.
         pfold.
         rewrite(str_eq(st2soFF
                       (str_send "p"
                          (fun l0 : string =>
                           if (l0 =? "l4")%string
                           then Some (I, Et1F)
                           else if (l0 =? "l5")%string then Some (I, Et2F) else if (l0 =? "l6")%string then Some (I, eT1F) else None)) col6
                       FF)). simpl.
         constructor.
         intros.
         case_eq (String.eqb l0 "l6"%string); intros. split. easy.
         right. apply CIH. easy.
       - case_eq (String.eqb l "l2"%string); intros.
         rewrite String.eqb_eq in H0. rewrite H0.
         simpl.
         split. easy.
         left.
         pfold.
         rewrite(str_eq(st2soFF (str_send "q" (fun l0 : string => if (l0 =? "l9")%string then Some (I, eT1F) else None)) col9 FF)).
         simpl. constructor.
         intros.
         case_eq (String.eqb l0 "l9"%string); intros.
         split. easy. right. apply CIH. easy.
       - case_eq (String.eqb l "l3"%string); intros.
         rewrite String.eqb_eq in H1. rewrite H1.
         simpl.
         split. easy.
         left.
         pfold.
         rewrite(str_eq(st2soFF (str_receive "q" (fun l0 : string => if (l0 =? "l10")%string then Some (I, eT1F) else None)) [||] FF)).
         simpl. constructor.
         intros.
         case_eq (String.eqb l0 "l10"%string); intros.
         rewrite String.eqb_eq in H2. rewrite H2.
         simpl.
         
         split. easy. right. apply CIH. easy. easy.
Qed.





