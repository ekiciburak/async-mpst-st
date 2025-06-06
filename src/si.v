From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import ST.src.stream ST.processes.process ST.src.st ST.types.local.
Require Import String List.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Morphisms.

CoFixpoint st2siH (t: st): st :=
  match t with
    | st_receive p xs    =>
      match xs with
        | cocons (l,s,t') ys => st_receive p [|(l,s,st2siH t')|] 
        | conil              => st_receive p conil
      end
    | st_send p xs => 
       let cofix next xs :=
        match xs with
          | cocons (l,s,t') ys => cocons (l,s,st2siH t') (next ys)
          | conil              => conil
        end 
      in st_send p (next xs) 
    | _               => st_end
  end.

CoFixpoint next (xs: coseq(label*sort*st)) :=
  match xs with
    | cocons (l,s,t') ys => cocons (l,s,st2siH t') (next ys)
    | conil              => conil
  end.

Inductive st2si (R: st -> st -> Prop): st -> st -> Prop :=
  | st2si_end: st2si R st_end st_end
  | st2si_rcv: forall l s x xs y p,
               R x y ->
               copathsel l s xs y ->
               st2si R (st_receive p (cocons (l,s,x) conil)) (st_receive p xs)
  | st2si_snd: forall p xs ys,
               Forall2Co (fun u v => exists l s t t', u = (l,s,t) /\ v = (l,s,t') /\ R t t') ys xs ->
               st2si R (st_send p ys) (st_send p xs).

Definition st2siC s1 s2 := paco2 (st2si) bot2 s1 s2.

Lemma st2si_mon: monotone2 st2si.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2si_end.
       - specialize (st2si_rcv r'); intro HS.
         apply HS with (y := y). apply LE. easy. easy.
       - specialize (st2si_snd r'); intro HS.
         apply HS. 
         apply monHo2 with (r := r); easy.
Qed.
