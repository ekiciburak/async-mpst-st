Require Import ST.processes.unscoped ST.processes.process.
From Paco Require Import paco.
Require Import ST.src.stream.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.

(* Notation label := string. *)
(* Notation participant := string. *)

Inductive sort: Type :=
  | sunit: sort
  | sbool: sort
  | sint : sort
  | snat : sort.

Inductive subsort: sort -> sort -> Prop :=
  | sni  : subsort snat sint
  | srefl: forall s, subsort s s.

Inductive nsubsort: sort -> sort -> Prop :=
  | nsin: nsubsort sint snat
  | nsbi: nsubsort sbool sint
  | nsib: nsubsort sint sbool
  | nsbn: nsubsort sbool snat
  | nsnb: nsubsort snat sbool
  | nsun: nsubsort sunit snat
  | nsnu: nsubsort snat sunit
  | nsbu: nsubsort sbool sunit
  | nsub: nsubsort sunit sbool
  | nsui: nsubsort sunit sint
  | nsiu: nsubsort sint sunit.

Lemma sort_dec: forall s s', subsort s s' \/ nsubsort s s'.
Proof. intro s.
       induction s; intros.
       case_eq s'; intros.
       left. apply srefl.
       right. apply nsub.
       right. apply nsui.
       right. apply nsun.
       case_eq s'; intros.
       right. apply nsbu.
       left. apply srefl.
       right. apply nsbi.
       right. apply nsbn.
       case_eq s'; intros.
       right. apply nsiu.
       right. apply nsib.
       left. apply srefl.
       right. apply nsin.
       case_eq s'; intros.
       right. apply nsnu.
       right. apply nsnb.
       left. apply sni.
       left. apply srefl.
Qed.

Lemma ssnssL: forall s t, subsort s t -> (nsubsort s t -> False).
Proof. intro s.
       induction s; intros; case_eq t; intros; subst; try easy.
Qed.

Lemma ssnssR: forall s t, nsubsort s t -> (subsort s t -> False).
Proof. intro s.
       induction s; intros; case_eq t; intros; subst; try easy.
Qed.

Lemma ssTrans: forall s1 s2 s3, subsort s1 s2 -> subsort s2 s3 -> subsort s1 s3.
Proof. intros.
       case_eq s1; intros.
       - subst. inversion H. subst. easy.
       - subst. inversion H. subst. easy.
       - subst. inversion H. subst. easy.
       - subst. inversion H. subst. inversion H0. subst. easy.
         subst. easy.
Qed.

Inductive local: Type :=
  | lt_var    : nat -> local 
  | lt_end    : local 
  | lt_send   : participant -> list(label*sort*local) -> local 
  | lt_receive: participant -> list(label*sort*local) -> local 
  | lt_mu     : local -> local.

Lemma congr_lt_end  : lt_end  = lt_end  .
Proof. congruence. Qed.

Lemma congr_lt_send  { s0 : participant   } { s1 : list (prod (prod (label  ) (sort  )) (local  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (sort  )) (local  )) } (H1 : s0 = t0) (H2 : s1 = t1) : lt_send  s0 s1 = lt_send  t0 t1 .
Proof. congruence. Qed.

Lemma congr_lt_receive  { s0 : participant   } { s1 : list (prod (prod (label  ) (sort  )) (local  )) } { t0 : participant   } { t1 : list (prod (prod (label  ) (sort  )) (local  )) } (H1 : s0 = t0) (H2 : s1 = t1) : lt_receive  s0 s1 = lt_receive  t0 t1 .
Proof. congruence. Qed.

Lemma congr_lt_mu  { s0 : local   } { t0 : local   } (H1 : s0 = t0) : lt_mu  s0 = lt_mu  t0 .
Proof. congruence. Qed.

Definition upRen_local_local   (xi : nat -> nat): nat  -> nat :=
  (up_ren) xi.

Fixpoint ren_local   (xilocal : ( nat ) -> nat) (s : local ) : local  :=
    match s return local  with
    | lt_var  s => (lt_var ) (xilocal s)
    | lt_end   => lt_end 
    | lt_send  s0 s1 => lt_send  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_local xilocal))) s1)
    | lt_receive  s0 s1 => lt_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (ren_local xilocal))) s1)
    | lt_mu  s0 => lt_mu  ((ren_local (upRen_local_local xilocal)) s0)
    end.

Definition up_local_local   (sigma : ( nat ) -> local ) : ( nat ) -> local  :=
  (scons) ((lt_var ) (var_zero)) ((funcomp) (ren_local (shift)) sigma).

Fixpoint subst_local   (sigmalocal : ( nat ) -> local ) (s : local ) : local  :=
    match s return local  with
    | lt_var  s => sigmalocal s
    | lt_end   => lt_end 
    | lt_send  s0 s1 => lt_send  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_local sigmalocal))) s1)
    | lt_receive  s0 s1 => lt_receive  ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (subst_local sigmalocal))) s1)
    | lt_mu  s0 => lt_mu  ((subst_local (up_local_local sigmalocal)) s0)
    end.

Fixpoint unfold_muL (l: local): local :=
  match l with
    | lt_mu l          => subst_local ((lt_mu l) .: lt_var) l
    | lt_send s0 s1    => lt_send ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (unfold_muL))) s1)
    | lt_receive s0 s1 => lt_receive ((fun x => x) s0) ((list_map (prod_map (prod_map (fun x => x) (fun x => x)) (unfold_muL))) s1)
    | _                => l
  end.

Local Open Scope list_scope.

Definition upId_local_local  (sigma : nat -> local ) (Eq : forall x, sigma x = (lt_var ) x) : 
  forall x, (up_local_local sigma) x = (lt_var ) x :=
  fun n => match n with
  | S nat_n => (ap) (ren_local (shift)) (Eq nat_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_local  (sigmalocal : ( nat ) -> local ) (Eqlocal : forall x, sigmalocal x = (lt_var ) x) (s : local ) : subst_local sigmalocal s = s :=
    match s return subst_local sigmalocal s = s with
    | lt_var  s => Eqlocal s
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (idSubst_local sigmalocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_id (prod_id (prod_id (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (idSubst_local sigmalocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((idSubst_local (up_local_local sigmalocal) (upId_local_local (_) Eqlocal)) s0)
    end.

Definition upExtRen_local_local   (xi : ( nat ) -> nat) (zeta : ( nat ) -> nat) (Eq : forall x, xi x = zeta x) : forall x, (upRen_local_local xi) x = (upRen_local_local zeta) x :=
  fun n => match n with
  | S nat_n => (ap) (shift) (Eq nat_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_local   (xilocal : ( nat ) -> nat) (zetalocal : ( nat ) -> nat) (Eqlocal : forall x, xilocal x = zetalocal x) (s : local ) : ren_local xilocal s = ren_local zetalocal s :=
    match s return ren_local xilocal s = ren_local zetalocal s with
    | lt_var  s => (ap) (lt_var ) (Eqlocal s)
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (extRen_local xilocal zetalocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (extRen_local xilocal zetalocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((extRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upExtRen_local_local (_) (_) Eqlocal)) s0)
    end.

Definition upExt_local_local   (sigma : ( nat ) -> local ) (tau : ( nat ) -> local ) (Eq : forall x, sigma x = tau x) : forall x, (up_local_local sigma) x = (up_local_local tau) x :=
  fun n => match n with
  | S nat_n => (ap) (ren_local (shift)) (Eq nat_n)
  | 0  => eq_refl
  end.

Fixpoint ext_local   (sigmalocal : ( nat ) -> local ) (taulocal : ( nat ) -> local ) (Eqlocal : forall x, sigmalocal x = taulocal x) (s : local ) : subst_local sigmalocal s = subst_local taulocal s :=
    match s return subst_local sigmalocal s = subst_local taulocal s with
    | lt_var  s => Eqlocal s
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (ext_local sigmalocal taulocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (ext_local sigmalocal taulocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((ext_local (up_local_local sigmalocal) (up_local_local taulocal) (upExt_local_local (_) (_) Eqlocal)) s0)
    end.

Definition up_ren_ren_local_local    (xi : ( nat ) -> nat) (tau : ( nat ) -> nat) (theta : ( nat ) -> nat) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_local_local tau) (upRen_local_local xi)) x = (upRen_local_local theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_local    (xilocal : ( nat ) -> nat) (zetalocal : ( nat ) -> nat) (rholocal : ( nat ) -> nat) (Eqlocal : forall x, ((funcomp) zetalocal xilocal) x = rholocal x) (s : local ) : ren_local zetalocal (ren_local xilocal s) = ren_local rholocal s :=
    match s return ren_local zetalocal (ren_local xilocal s) = ren_local rholocal s with
    | lt_var  s => (ap) (lt_var ) (Eqlocal s)
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenRen_local xilocal zetalocal rholocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((compRenRen_local (upRen_local_local xilocal) (upRen_local_local zetalocal) (upRen_local_local rholocal) (up_ren_ren (_) (_) (_) Eqlocal)) s0)
    end.

Definition up_ren_subst_local_local    (xi : ( nat ) -> nat) (tau : ( nat ) -> local ) (theta : ( nat ) -> local ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_local_local tau) (upRen_local_local xi)) x = (up_local_local theta) x :=
  fun n => match n with
  | S nat_n => (ap) (ren_local (shift)) (Eq nat_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_local    (xilocal : ( nat ) -> nat) (taulocal : ( nat ) -> local ) (thetalocal : ( nat ) -> local ) (Eqlocal : forall x, ((funcomp) taulocal xilocal) x = thetalocal x) (s : local ) : subst_local taulocal (ren_local xilocal s) = subst_local thetalocal s :=
    match s return subst_local taulocal (ren_local xilocal s) = subst_local thetalocal s with
    | lt_var  s => Eqlocal s
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compRenSubst_local xilocal taulocal thetalocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((compRenSubst_local (upRen_local_local xilocal) (up_local_local taulocal) (up_local_local thetalocal) (up_ren_subst_local_local (_) (_) (_) Eqlocal)) s0)
    end.

Definition up_subst_ren_local_local    (sigma : ( nat ) -> local ) (zetalocal : ( nat ) -> nat) (theta : ( nat ) -> local ) (Eq : forall x, ((funcomp) (ren_local zetalocal) sigma) x = theta x) : forall x, ((funcomp) (ren_local (upRen_local_local zetalocal)) (up_local_local sigma)) x = (up_local_local theta) x :=
  fun n => match n with
  | S nat_n => (eq_trans) (compRenRen_local (shift) (upRen_local_local zetalocal) ((funcomp) (shift) zetalocal) (fun x => eq_refl) (sigma nat_n)) ((eq_trans) ((eq_sym) (compRenRen_local zetalocal (shift) ((funcomp) (shift) zetalocal) (fun x => eq_refl) (sigma nat_n))) ((ap) (ren_local (shift)) (Eq nat_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_local    (sigmalocal : ( nat ) -> local ) (zetalocal : ( nat ) -> nat) (thetalocal : ( nat ) -> local ) (Eqlocal : forall x, ((funcomp) (ren_local zetalocal) sigmalocal) x = thetalocal x) (s : local ) : ren_local zetalocal (subst_local sigmalocal s) = subst_local thetalocal s :=
    match s return ren_local zetalocal (subst_local sigmalocal s) = subst_local thetalocal s with
    | lt_var  s => Eqlocal s
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstRen_local sigmalocal zetalocal thetalocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((compSubstRen_local (up_local_local sigmalocal) (upRen_local_local zetalocal) (up_local_local thetalocal) (up_subst_ren_local_local (_) (_) (_) Eqlocal)) s0)
    end.

Definition up_subst_subst_local_local    (sigma : ( nat ) -> local ) (taulocal : ( nat ) -> local ) (theta : ( nat ) -> local ) (Eq : forall x, ((funcomp) (subst_local taulocal) sigma) x = theta x) : forall x, ((funcomp) (subst_local (up_local_local taulocal)) (up_local_local sigma)) x = (up_local_local theta) x :=
  fun n => match n with
  | S nat_n => (eq_trans) (compRenSubst_local (shift) (up_local_local taulocal) ((funcomp) (up_local_local taulocal) (shift)) (fun x => eq_refl) (sigma nat_n)) ((eq_trans) ((eq_sym) (compSubstRen_local taulocal (shift) ((funcomp) (ren_local (shift)) taulocal) (fun x => eq_refl) (sigma nat_n))) ((ap) (ren_local (shift)) (Eq nat_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_local    (sigmalocal : ( nat ) -> local ) (taulocal : ( nat ) -> local ) (thetalocal : ( nat ) -> local ) (Eqlocal : forall x, ((funcomp) (subst_local taulocal) sigmalocal) x = thetalocal x) (s : local ) : subst_local taulocal (subst_local sigmalocal s) = subst_local thetalocal s :=
    match s return subst_local taulocal (subst_local sigmalocal s) = subst_local thetalocal s with
    | lt_var  s => Eqlocal s
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_comp (prod_comp (prod_comp (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (compSubstSubst_local sigmalocal taulocal thetalocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((compSubstSubst_local (up_local_local sigmalocal) (up_local_local taulocal) (up_local_local thetalocal) (up_subst_subst_local_local (_) (_) (_) Eqlocal)) s0)
    end.

Definition rinstInst_up_local_local   (xi : ( nat ) -> nat) (sigma : ( nat ) -> local ) (Eq : forall x, ((funcomp) (lt_var ) xi) x = sigma x) : forall x, ((funcomp) (lt_var ) (upRen_local_local xi)) x = (up_local_local sigma) x :=
  fun n => match n with
  | S nat_n => (ap) (ren_local (shift)) (Eq nat_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_local   (xilocal : ( nat ) -> nat) (sigmalocal : ( nat ) -> local ) (Eqlocal : forall x, ((funcomp) (lt_var ) xilocal) x = sigmalocal x) (s : local ) : ren_local xilocal s = subst_local sigmalocal s :=
    match s return ren_local xilocal s = subst_local sigmalocal s with
    | lt_var  s => Eqlocal s
    | lt_end   => congr_lt_end 
    | lt_send  s0 s1 => congr_lt_send ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1)
    | lt_receive  s0 s1 => congr_lt_receive ((fun x => (eq_refl) x) s0) ((list_ext (prod_ext (prod_ext (fun x => (eq_refl) x) (fun x => (eq_refl) x)) (rinst_inst_local xilocal sigmalocal Eqlocal))) s1)
    | lt_mu  s0 => congr_lt_mu ((rinst_inst_local (upRen_local_local xilocal) (up_local_local sigmalocal) (rinstInst_up_local_local (_) (_) Eqlocal)) s0)
    end.

Lemma rinstInst_local   (xilocal : ( nat ) -> nat) : ren_local xilocal = subst_local ((funcomp) (lt_var ) xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_local xilocal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_local  : subst_local (lt_var ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_local (lt_var ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_local  : @ren_local   (id) = id .
Proof. exact ((eq_trans) (rinstInst_local ((id) (_))) instId_local). Qed.

Lemma varL_local   (sigmalocal : ( nat ) -> local ) : (funcomp) (subst_local sigmalocal) (lt_var ) = sigmalocal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_local   (xilocal : ( nat ) -> nat) : (funcomp) (ren_local xilocal) (lt_var ) = (funcomp) (lt_var ) xilocal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_local    (sigmalocal : ( nat ) -> local ) (taulocal : ( nat ) -> local ) (s : local ) : subst_local taulocal (subst_local sigmalocal s) = subst_local ((funcomp) (subst_local taulocal) sigmalocal) s .
Proof. exact (compSubstSubst_local sigmalocal taulocal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_local    (sigmalocal : ( nat ) -> local ) (taulocal : ( nat ) -> local ) : (funcomp) (subst_local taulocal) (subst_local sigmalocal) = subst_local ((funcomp) (subst_local taulocal) sigmalocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_local sigmalocal taulocal n)). Qed.

Lemma compRen_local    (sigmalocal : ( nat ) -> local ) (zetalocal : ( nat ) -> nat) (s : local ) : ren_local zetalocal (subst_local sigmalocal s) = subst_local ((funcomp) (ren_local zetalocal) sigmalocal) s .
Proof. exact (compSubstRen_local sigmalocal zetalocal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_local    (sigmalocal : ( nat ) -> local ) (zetalocal : ( nat ) -> nat) : (funcomp) (ren_local zetalocal) (subst_local sigmalocal) = subst_local ((funcomp) (ren_local zetalocal) sigmalocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_local sigmalocal zetalocal n)). Qed.

Lemma renComp_local    (xilocal : ( nat ) -> nat) (taulocal : ( nat ) -> local ) (s : local ) : subst_local taulocal (ren_local xilocal s) = subst_local ((funcomp) taulocal xilocal) s .
Proof. exact (compRenSubst_local xilocal taulocal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_local    (xilocal : ( nat ) -> nat) (taulocal : ( nat ) -> local ) : (funcomp) (subst_local taulocal) (ren_local xilocal) = subst_local ((funcomp) taulocal xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_local xilocal taulocal n)). Qed.

Lemma renRen_local    (xilocal : ( nat ) -> nat) (zetalocal : ( nat ) -> nat) (s : local ) : ren_local zetalocal (ren_local xilocal s) = ren_local ((funcomp) zetalocal xilocal) s .
Proof. exact (compRenRen_local xilocal zetalocal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_local    (xilocal : ( nat ) -> nat) (zetalocal : ( nat ) -> nat) : (funcomp) (ren_local zetalocal) (ren_local xilocal) = ren_local ((funcomp) zetalocal xilocal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_local xilocal zetalocal n)). Qed.








Global Instance Subst_local   : Subst1 (( nat ) -> local ) (local ) (local ) := @subst_local   .

Global Instance Ren_local   : Ren1 (( nat ) -> nat) (local ) (local ) := @ren_local   .

Global Instance VarInstance_local  : Var (nat) (local ) := @lt_var  .

Notation "x '__local'" := (lt_var x) (at level 5, format "x __local") : subst_scope.

Notation "x '__local'" := (@ids (_) (_) VarInstance_local x) (at level 5, only printing, format "x __local") : subst_scope.

Notation "'var'" := (lt_var) (only printing, at level 1) : subst_scope.

Class Up_local X Y := up_local : ( X ) -> Y.

Notation "↑__local" := (up_local) (only printing) : subst_scope.

Notation "↑__local" := (up_local_local) (only printing) : subst_scope.

Global Instance Up_local_local   : Up_local (_) (_) := @up_local_local   .

Notation "s [ sigmalocal ]" := (subst_local sigmalocal s) (at level 7, left associativity, only printing) : subst_scope.

(* Notation "[ sigmalocal ]" := (subst_local sigmalocal) (at level 1, left associativity, only printing) : fscope. *)

Notation "s ⟨ xilocal ⟩" := (ren_local xilocal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xilocal ⟩" := (ren_local xilocal) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_local,  Ren_local,  VarInstance_local.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_local,  Ren_local,  VarInstance_local in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_local| progress rewrite ?compComp_local| progress rewrite ?compComp'_local| progress rewrite ?rinstId_local| progress rewrite ?compRen_local| progress rewrite ?compRen'_local| progress rewrite ?renComp_local| progress rewrite ?renComp'_local| progress rewrite ?renRen_local| progress rewrite ?renRen'_local| progress rewrite ?varL_local| progress rewrite ?varLRen_local| progress (unfold up_ren, upRen_local_local, up_local_local)| progress (cbn [subst_local ren_local])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_local in *| progress rewrite ?compComp_local in *| progress rewrite ?compComp'_local in *| progress rewrite ?rinstId_local in *| progress rewrite ?compRen_local in *| progress rewrite ?compRen'_local in *| progress rewrite ?renComp_local in *| progress rewrite ?renComp'_local in *| progress rewrite ?renRen_local in *| progress rewrite ?renRen'_local in *| progress rewrite ?varL_local in *| progress rewrite ?varLRen_local in *| progress (unfold up_ren, upRen_local_local, up_local_local in *)| progress (cbn [subst_local ren_local] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_local).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_local).


Require Import ST.processes.unscoped.
From mathcomp Require Import all_ssreflect.
Require Import Lia.

Fixpoint guarded (l: local) (i: nat) := 
  match l with
    | lt_var j        => negb (Nat.eqb j i)
    | lt_end          => true
    | lt_receive p xs => true
    | lt_send p xs    => true
    | lt_mu l0        => guarded l0 (S i)
  end.

Definition unf l := if l is lt_mu l' then l' [l .: lt_var]  else l.

(* Definition unf (l: local): local :=
  match l with
    | lt_mu l => l[lt_mu l .: lt_var]
    | _       => l
  end.
 *)
Fixpoint depth G :=
  match G with
    | lt_mu G => S (depth G)
    | _       => 0
  end.

Definition full_unf g := (iter (depth g) unf g).

Lemma mu_height_ren : forall g (sigma: nat -> nat), depth (g ⟨sigma⟩) = depth g.
Proof. intro g.
       induction g; intros.
       - simpl. easy.
       - simpl. easy.
       - simpl. easy.
       - simpl. easy.
       - simpl. 
         f_equal.
         rewrite IHg.
         easy.
Qed.

Lemma feqb_refl: forall (n: fin), Nat.eqb n n = true.
Proof. intro n.
       induction n; intros.
       - easy.
       - simpl. easy.
Qed.

Lemma neg_negb: forall b, ~~ ~~ b -> b.
Proof. intro b.
       induction b; easy.
Qed.

Lemma feqb_eq: forall (n m: fin), Nat.eqb n m = true <-> n = m.
Proof. intro n.
       induction n; intros.
       - case_eq m; intros.
         + easy.
         + easy.
       - case_eq m; intros.
         + simpl. easy.
         + simpl. rewrite IHn. 
           lia.
Qed.

Lemma mu_height_subst : forall l sigma, (forall n, ~~ guarded l n -> depth (sigma n) = 0) ->  depth (l[sigma]) = depth l.
Proof. intro l.
       induction l; intros.
       - simpl. asimpl. apply H. simpl.
         rewrite feqb_refl. easy.
       - simpl. easy.
       - simpl. easy.
       - simpl. easy.
       - simpl. 
         f_equal. 
         apply IHl.
         intros.
         asimpl.
         case_eq n; intros.
         + simpl. easy.
         + asimpl.
           unfold shift.
           asimpl.
           rewrite mu_height_ren.
           apply H.
           simpl. subst. easy.
Qed.

Lemma mu_height_unf : forall l, guarded l 0 -> depth l = depth (l[lt_mu l .: lt_var]).
Proof. intros. rewrite mu_height_subst. easy.
       intro n.
       induction n; intros.
       - asimpl.
         case_eq(guarded l 0); intros.
         + rewrite H1 in H H0. easy.
         + rewrite H1 in H. easy.
       - asimpl. simpl. easy.
Qed.

Lemma mu_height_unf2 : forall l sigma i, ~~ guarded l i -> (depth l) + depth (sigma i) = depth (l [sigma]).
Proof. intro l.
       induction l; intros.
       - asimpl. simpl. simpl in H.
         assert(n = i).
         { apply neg_negb in H.
           apply feqb_eq in H. easy.
         }
         subst. easy.
       - simpl in H. easy.
       - simpl in H. easy.
       - simpl in H. easy.
       - simpl in H. simpl in *.
         f_equal.
         asimpl.
         unfold shift.
         rewrite <- IHl with (i := i.+1).
         rewrite mu_height_ren. easy. easy.
Qed.

Lemma guarded_test : forall (e: local) sigma i, ~~ guarded e i -> ssrnat.iter (depth e) unf e [ sigma ] = sigma i.
Proof. intro e.
       induction e; intros.
       - asimpl. simpl.
         assert(n = i).
         { apply neg_negb in H.
           apply feqb_eq in H. easy.
         } subst. easy.
       - asimpl. simpl. simpl in H. easy.
       - simpl in H. easy.
       - simpl in H. easy.
       - simpl in H.
         rewrite iterSr.
         simpl.
         asimpl.
         fold depth.
         specialize(IHe (lt_mu e[lt_var 0;; sigma >> ⟨↑⟩];; sigma) (S i)).
         rewrite IHe. asimpl. easy. easy.
Qed.
 
  
Lemma full_unf_subst : forall e, full_unf (lt_mu e) = full_unf (e [lt_mu e .: lt_var]).
Proof. intro e.
       induction e; intros.
       - asimpl. unfold full_unf. asimpl.
         rewrite iterSr. simpl. asimpl.
         destruct n. asimpl. simpl.
         easy. 
         simpl. easy.
       - asimpl. unfold full_unf. simpl. easy.
       - asimpl. unfold full_unf. simpl. easy.
       - asimpl. unfold full_unf. simpl. easy.
       - unfold full_unf in *.
         rewrite iterS.
         rewrite iterSr.
         rewrite iterSr.
         rewrite iterSr in IHe.
         fold depth. fold subst_local. fold depth in IHe.
         case_eq(guarded e 0); intros.
         + admit.
         + erewrite <- mu_height_unf2 with (i := 0).
           asimpl.
           rewrite addnC.
           rewrite iterD. simpl. asimpl.
           erewrite guarded_test with (i := 0).
           simpl. 
(*            rewrite <- iterS. simpl.
           erewrite guarded_test.
           asimpl. simpl.
           erewrite guarded_test with (i := 0).
           easy.
           unfold negb. simpl in H. rewrite H. easy. *)
Admitted.
  
