Require Import ST.processes.unscoped.
(* From mathcomp Require Import all_ssreflect. *)
From Paco Require Import paco.
Require Import String List ZArith.
Local Open Scope string_scope.
Import ListNotations.

Notation participant := string.
Notation label := string.

Inductive value: Type :=
 | vint : Z    -> value
 | vbool: bool -> value
 | vunit: unit -> value.

Inductive expr: Type :=
  | eval : value  -> expr
  | evar : string -> expr
  | esucc: expr   -> expr
  | einv : expr   -> expr
  | eneg : expr   -> expr
  | eisgt: expr   -> expr
  | eistt: expr   -> expr.

Inductive mqueue: Type := 
  | nilq: mqueue
  | mesq: participant -> label -> value -> mqueue -> mqueue.

Fixpoint conq (m1 m2: mqueue): mqueue :=
  match m1 with
    | nilq         => m2
    | mesq p l v q => mesq p l v (conq q m2)
  end.

Inductive process  : Type :=
  | ps_var    : fin -> process 
  | ps_end    : process 
  | ps_send   : participant -> label -> expr -> process -> process 
  | ps_receive: participant -> list(label*expr*process) -> process 
  | ps_ite    : expr -> process -> process -> process 
  | ps_mu     : process -> process.

Lemma congr_ps_end  : ps_end  = ps_end.
Proof. congruence. Qed.

Lemma congr_ps_send  { s0 : participant   } { s1 : label   } { s2 : expr   } { s3 : process   } { t0 : participant   } { t1 : label   } { t2 : expr   } { t3 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : ps_send  s0 s1 s2 s3 = ps_send  t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_ps_receive  { s0 : participant   } { s1 : list (prod (prod (label  ) (expr  )) (process  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (expr  )) (process  )) } (H1 : s0 = t0) (H2 : s1 = t1) : ps_receive  s0 s1 = ps_receive  t0 t1 .
Proof. congruence. Qed.

Lemma congr_ps_ite  { s0 : expr   } { s1 : process   } { s2 : process   } { t0 : expr   } { t1 : process   } { t2 : process   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ps_ite  s0 s1 s2 = ps_ite  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ps_mu  { s0 : process   } { t0 : process   } (H1 : s0 = t0) : ps_mu  s0 = ps_mu  t0 .
Proof. congruence. Qed.

Definition upRen_process_process   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_process   (xiprocess : ( fin ) -> fin) (s : process ) : process  :=
    match s return process  with
    | ps_var  s => (ps_var ) (xiprocess s)
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((ren_process xiprocess) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_process xiprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((ren_process xiprocess) s1) ((ren_process xiprocess) s2)
    | ps_mu  s0 => ps_mu  ((ren_process (upRen_process_process xiprocess)) s0)
    end.

Definition up_process_process   (sigma : ( fin ) -> process ) : ( fin ) -> process  :=
  (scons) ((ps_var ) (var_zero)) ((funcomp) (ren_process (unscoped.shift)) sigma).

Fixpoint subst_process   (sigmaprocess : ( fin ) -> process ) (s : process ) : process  :=
    match s return process  with
    | ps_var  s => sigmaprocess s
    | ps_end   => ps_end 
    | ps_send  s0 s1 s2 s3 => ps_send  ((fun x => x) s0) ((fun x => x) s1) ((fun x => x) s2) ((subst_process sigmaprocess) s3)
    | ps_receive  s0 s1 => ps_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_process sigmaprocess))) s1)
    | ps_ite  s0 s1 s2 => ps_ite  ((fun x => x) s0) ((subst_process sigmaprocess) s1) ((subst_process sigmaprocess) s2)
    | ps_mu  s0 => ps_mu  ((subst_process (up_process_process sigmaprocess)) s0)
    end.

Definition upId_process_process  (sigma : ( fin ) -> process ) (Eq : forall x, sigma x = (ps_var ) x) : forall x, (up_process_process sigma) x = (ps_var ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_process (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_process  (sigmaprocess : ( fin ) -> process ) (Eqprocess : forall x, sigmaprocess x = (ps_var ) x) (s : process ) : subst_process sigmaprocess s = s :=
    match s return subst_process sigmaprocess s = s with
    | ps_var  s => Eqprocess s
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((idSubst_process sigmaprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (idSubst_process sigmaprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((idSubst_process sigmaprocess Eqprocess) s1) ((idSubst_process sigmaprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((idSubst_process (up_process_process sigmaprocess) (upId_process_process (_) Eqprocess)) s0)
    end.

Definition upExtRen_process_process   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_process_process xi) x = (upRen_process_process zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (unscoped.shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_process   (xiprocess : ( fin ) -> fin) (zetaprocess : ( fin ) -> fin) (Eqprocess : forall x, xiprocess x = zetaprocess x) (s : process ) : ren_process xiprocess s = ren_process zetaprocess s :=
    match s return ren_process xiprocess s = ren_process zetaprocess s with
    | ps_var  s => (ap) (ps_var ) (Eqprocess s)
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((extRen_process xiprocess zetaprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (extRen_process xiprocess zetaprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((extRen_process xiprocess zetaprocess Eqprocess) s1) ((extRen_process xiprocess zetaprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((extRen_process (upRen_process_process xiprocess) (upRen_process_process zetaprocess) (upExtRen_process_process (_) (_) Eqprocess)) s0)
    end.

Definition upExt_process_process   (sigma : ( fin ) -> process ) (tau : ( fin ) -> process ) (Eq : forall x, sigma x = tau x) : forall x, (up_process_process sigma) x = (up_process_process tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_process (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_process   (sigmaprocess : ( fin ) -> process ) (tauprocess : ( fin ) -> process ) (Eqprocess : forall x, sigmaprocess x = tauprocess x) (s : process ) : subst_process sigmaprocess s = subst_process tauprocess s :=
    match s return subst_process sigmaprocess s = subst_process tauprocess s with
    | ps_var  s => Eqprocess s
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((ext_process sigmaprocess tauprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (ext_process sigmaprocess tauprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((ext_process sigmaprocess tauprocess Eqprocess) s1) ((ext_process sigmaprocess tauprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((ext_process (up_process_process sigmaprocess) (up_process_process tauprocess) (upExt_process_process (_) (_) Eqprocess)) s0)
    end.

Definition up_ren_ren_process_process    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_process_process tau) (upRen_process_process xi)) x = (upRen_process_process theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_process    (xiprocess : ( fin ) -> fin) (zetaprocess : ( fin ) -> fin) (rhoprocess : ( fin ) -> fin) (Eqprocess : forall x, ((funcomp) zetaprocess xiprocess) x = rhoprocess x) (s : process ) : ren_process zetaprocess (ren_process xiprocess s) = ren_process rhoprocess s :=
    match s return ren_process zetaprocess (ren_process xiprocess s) = ren_process rhoprocess s with
    | ps_var  s => (ap) (ps_var ) (Eqprocess s)
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((compRenRen_process xiprocess zetaprocess rhoprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenRen_process xiprocess zetaprocess rhoprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((compRenRen_process xiprocess zetaprocess rhoprocess Eqprocess) s1) ((compRenRen_process xiprocess zetaprocess rhoprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((compRenRen_process (upRen_process_process xiprocess) (upRen_process_process zetaprocess) (upRen_process_process rhoprocess) (up_ren_ren (_) (_) (_) Eqprocess)) s0)
    end.

Definition up_ren_subst_process_process    (xi : ( fin ) -> fin) (tau : ( fin ) -> process ) (theta : ( fin ) -> process ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_process_process tau) (upRen_process_process xi)) x = (up_process_process theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_process (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_process    (xiprocess : ( fin ) -> fin) (tauprocess : ( fin ) -> process ) (thetaprocess : ( fin ) -> process ) (Eqprocess : forall x, ((funcomp) tauprocess xiprocess) x = thetaprocess x) (s : process ) : subst_process tauprocess (ren_process xiprocess s) = subst_process thetaprocess s :=
    match s return subst_process tauprocess (ren_process xiprocess s) = subst_process thetaprocess s with
    | ps_var  s => Eqprocess s
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((compRenSubst_process xiprocess tauprocess thetaprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenSubst_process xiprocess tauprocess thetaprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((compRenSubst_process xiprocess tauprocess thetaprocess Eqprocess) s1) ((compRenSubst_process xiprocess tauprocess thetaprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((compRenSubst_process (upRen_process_process xiprocess) (up_process_process tauprocess) (up_process_process thetaprocess) (up_ren_subst_process_process (_) (_) (_) Eqprocess)) s0)
    end.

Definition up_subst_ren_process_process    (sigma : ( fin ) -> process ) (zetaprocess : ( fin ) -> fin) (theta : ( fin ) -> process ) (Eq : forall x, ((funcomp) (ren_process zetaprocess) sigma) x = theta x) : forall x, ((funcomp) (ren_process (upRen_process_process zetaprocess)) (up_process_process sigma)) x = (up_process_process theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_process (unscoped.shift) (upRen_process_process zetaprocess) ((funcomp) (unscoped.shift) zetaprocess) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_process zetaprocess (unscoped.shift) ((funcomp) (unscoped.shift) zetaprocess) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_process (unscoped.shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_process    (sigmaprocess : ( fin ) -> process ) (zetaprocess : ( fin ) -> fin) (thetaprocess : ( fin ) -> process ) (Eqprocess : forall x, ((funcomp) (ren_process zetaprocess) sigmaprocess) x = thetaprocess x) (s : process ) : ren_process zetaprocess (subst_process sigmaprocess s) = subst_process thetaprocess s :=
    match s return ren_process zetaprocess (subst_process sigmaprocess s) = subst_process thetaprocess s with
    | ps_var  s => Eqprocess s
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((compSubstRen_process sigmaprocess zetaprocess thetaprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstRen_process sigmaprocess zetaprocess thetaprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((compSubstRen_process sigmaprocess zetaprocess thetaprocess Eqprocess) s1) ((compSubstRen_process sigmaprocess zetaprocess thetaprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((compSubstRen_process (up_process_process sigmaprocess) (upRen_process_process zetaprocess) (up_process_process thetaprocess) (up_subst_ren_process_process (_) (_) (_) Eqprocess)) s0)
    end.

Definition up_subst_subst_process_process    (sigma : ( fin ) -> process ) (tauprocess : ( fin ) -> process ) (theta : ( fin ) -> process ) (Eq : forall x, ((funcomp) (subst_process tauprocess) sigma) x = theta x) : forall x, ((funcomp) (subst_process (up_process_process tauprocess)) (up_process_process sigma)) x = (up_process_process theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_process (unscoped.shift) (up_process_process tauprocess) ((funcomp) (up_process_process tauprocess) (unscoped.shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_process tauprocess (unscoped.shift) ((funcomp) (ren_process (unscoped.shift)) tauprocess) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_process (unscoped.shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_process    (sigmaprocess : ( fin ) -> process ) (tauprocess : ( fin ) -> process ) (thetaprocess : ( fin ) -> process ) (Eqprocess : forall x, ((funcomp) (subst_process tauprocess) sigmaprocess) x = thetaprocess x) (s : process ) : subst_process tauprocess (subst_process sigmaprocess s) = subst_process thetaprocess s :=
    match s return subst_process tauprocess (subst_process sigmaprocess s) = subst_process thetaprocess s with
    | ps_var  s => Eqprocess s
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((compSubstSubst_process sigmaprocess tauprocess thetaprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstSubst_process sigmaprocess tauprocess thetaprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((compSubstSubst_process sigmaprocess tauprocess thetaprocess Eqprocess) s1) ((compSubstSubst_process sigmaprocess tauprocess thetaprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((compSubstSubst_process (up_process_process sigmaprocess) (up_process_process tauprocess) (up_process_process thetaprocess) (up_subst_subst_process_process (_) (_) (_) Eqprocess)) s0)
    end.

Definition rinstInst_up_process_process   (xi : ( fin ) -> fin) (sigma : ( fin ) -> process ) (Eq : forall x, ((funcomp) (ps_var ) xi) x = sigma x) : forall x, ((funcomp) (ps_var ) (upRen_process_process xi)) x = (up_process_process sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_process (unscoped.shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_process   (xiprocess : ( fin ) -> fin) (sigmaprocess : ( fin ) -> process ) (Eqprocess : forall x, ((funcomp) (ps_var ) xiprocess) x = sigmaprocess x) (s : process ) : ren_process xiprocess s = subst_process sigmaprocess s :=
    match s return ren_process xiprocess s = subst_process sigmaprocess s with
    | ps_var  s => Eqprocess s
    | ps_end   => congr_ps_end 
    | ps_send  s0 s1 s2 s3 => congr_ps_send ((fun x => (eq_refl) x) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((rinst_inst_process xiprocess sigmaprocess Eqprocess) s3)
    | ps_receive  s0 s1 => congr_ps_receive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (rinst_inst_process xiprocess sigmaprocess Eqprocess))) s1)
    | ps_ite  s0 s1 s2 => congr_ps_ite ((fun x => (eq_refl) x) s0) ((rinst_inst_process xiprocess sigmaprocess Eqprocess) s1) ((rinst_inst_process xiprocess sigmaprocess Eqprocess) s2)
    | ps_mu  s0 => congr_ps_mu ((rinst_inst_process (upRen_process_process xiprocess) (up_process_process sigmaprocess) (rinstInst_up_process_process (_) (_) Eqprocess)) s0)
    end.

Lemma rinstInst_process   (xiprocess : ( fin ) -> fin) : ren_process xiprocess = subst_process ((funcomp) (ps_var ) xiprocess) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_process xiprocess (_) (fun n => eq_refl) x)). Qed.

Lemma instId_process  : subst_process (ps_var ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_process (ps_var ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_process  : @ren_process   (id) = id .
Proof. exact ((eq_trans) (rinstInst_process ((id) (_))) instId_process). Qed.

Lemma varL_process   (sigmaprocess : ( fin ) -> process ) : (funcomp) (subst_process sigmaprocess) (ps_var ) = sigmaprocess .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_process   (xiprocess : ( fin ) -> fin) : (funcomp) (ren_process xiprocess) (ps_var ) = (funcomp) (ps_var ) xiprocess .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_process    (sigmaprocess : ( fin ) -> process ) (tauprocess : ( fin ) -> process ) (s : process ) : subst_process tauprocess (subst_process sigmaprocess s) = subst_process ((funcomp) (subst_process tauprocess) sigmaprocess) s .
Proof. exact (compSubstSubst_process sigmaprocess tauprocess (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_process    (sigmaprocess : ( fin ) -> process ) (tauprocess : ( fin ) -> process ) : (funcomp) (subst_process tauprocess) (subst_process sigmaprocess) = subst_process ((funcomp) (subst_process tauprocess) sigmaprocess) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_process sigmaprocess tauprocess n)). Qed.

Lemma compRen_process    (sigmaprocess : ( fin ) -> process ) (zetaprocess : ( fin ) -> fin) (s : process ) : ren_process zetaprocess (subst_process sigmaprocess s) = subst_process ((funcomp) (ren_process zetaprocess) sigmaprocess) s .
Proof. exact (compSubstRen_process sigmaprocess zetaprocess (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_process    (sigmaprocess : ( fin ) -> process ) (zetaprocess : ( fin ) -> fin) : (funcomp) (ren_process zetaprocess) (subst_process sigmaprocess) = subst_process ((funcomp) (ren_process zetaprocess) sigmaprocess) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_process sigmaprocess zetaprocess n)). Qed.

Lemma renComp_process    (xiprocess : ( fin ) -> fin) (tauprocess : ( fin ) -> process ) (s : process ) : subst_process tauprocess (ren_process xiprocess s) = subst_process ((funcomp) tauprocess xiprocess) s .
Proof. exact (compRenSubst_process xiprocess tauprocess (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_process    (xiprocess : ( fin ) -> fin) (tauprocess : ( fin ) -> process ) : (funcomp) (subst_process tauprocess) (ren_process xiprocess) = subst_process ((funcomp) tauprocess xiprocess) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_process xiprocess tauprocess n)). Qed.

Lemma renRen_process    (xiprocess : ( fin ) -> fin) (zetaprocess : ( fin ) -> fin) (s : process ) : ren_process zetaprocess (ren_process xiprocess s) = ren_process ((funcomp) zetaprocess xiprocess) s .
Proof. exact (compRenRen_process xiprocess zetaprocess (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_process    (xiprocess : ( fin ) -> fin) (zetaprocess : ( fin ) -> fin) : (funcomp) (ren_process zetaprocess) (ren_process xiprocess) = ren_process ((funcomp) zetaprocess xiprocess) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_process xiprocess zetaprocess n)). Qed.


Global Instance Subst_process   : Subst1 (( fin ) -> process ) (process ) (process ) := @subst_process   .

Global Instance Ren_process   : Ren1 (( fin ) -> fin) (process ) (process ) := @ren_process   .

Global Instance VarInstance_process  : Var (fin) (process ) := @ps_var  .

Notation "x '__process'" := (ps_var x) (at level 5, format "x __process") : subst_scope.

Notation "x '__process'" := (@ids (_) (_) VarInstance_process x) (at level 5, only printing, format "x __process") : subst_scope.

Notation "'var'" := (ps_var) (only printing, at level 1) : subst_scope.

Class Up_process X Y := up_process : ( X ) -> Y.

Notation "↑__process" := (up_process) (only printing) : subst_scope.

Notation "↑__process" := (up_process_process) (only printing) : subst_scope.

Global Instance Up_process_process   : Up_process (_) (_) := @up_process_process   .

Notation "s [ sigmaprocess ]" := (subst_process sigmaprocess s) (at level 7, left associativity, only printing) : subst_scope.

(* Notation "[ sigmaprocess ]" := (subst_process sigmaprocess) (at level 1, left associativity, only printing) : fscope. *)

Notation "s ⟨ xiprocess ⟩" := (ren_process xiprocess s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiprocess ⟩" := (ren_process xiprocess) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_process,  Ren_process,  VarInstance_process.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_process,  Ren_process,  VarInstance_process in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_process| progress rewrite ?compComp_process| progress rewrite ?compComp'_process| progress rewrite ?rinstId_process| progress rewrite ?compRen_process| progress rewrite ?compRen'_process| progress rewrite ?renComp_process| progress rewrite ?renComp'_process| progress rewrite ?renRen_process| progress rewrite ?renRen'_process| progress rewrite ?varL_process| progress rewrite ?varLRen_process| progress (unfold up_ren, upRen_process_process, up_process_process)| progress (cbn [subst_process ren_process])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_process in *| progress rewrite ?compComp_process in *| progress rewrite ?compComp'_process in *| progress rewrite ?rinstId_process in *| progress rewrite ?compRen_process in *| progress rewrite ?compRen'_process in *| progress rewrite ?renComp_process in *| progress rewrite ?renComp'_process in *| progress rewrite ?renRen_process in *| progress rewrite ?renRen'_process in *| progress rewrite ?varL_process in *| progress rewrite ?varLRen_process in *| progress (unfold up_ren, upRen_process_process, up_process_process in *)| progress (cbn [subst_process ren_process] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_process).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_process).
