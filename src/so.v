From mathcomp Require Import all_ssreflect.
From Paco Require Import paco.
Require Import ST.src.stream ST.src.st.
Require Import String List.
Local Open Scope string_scope.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

CoInductive so: Type :=
  | so_end    : so 
  | so_receive: participant -> list (label*sort*so) -> so 
  | so_send   : participant -> (label*sort*so)      -> so.

Definition so_id (s: so): so :=
  match s with
    | so_end            => so_end
    | so_receive p l    => so_receive p l
    | so_send p (l,s,t) => so_send p (l,s,t)
  end.

Lemma so_eq: forall (s: so), s = so_id s.
Proof. intro s; destruct s; simpl; try easy. destruct p as ((l,srt),t). easy. Defined.

Fixpoint pathselSo (u: label) (l: list (label*st.sort*st)): st :=
  match l with
    | (lbl,s,x)::xs => if eqb u lbl then x else pathselSo u xs
    | nil           => st_end
  end.

Inductive st2so (R: so -> st -> Prop): so -> st -> Prop :=
  | st2so_end: st2so R so_end st_end
  | st2so_snd: forall l s x xs p,
               R x (pathselSo l xs) ->
               st2so R (so_send p (l,s,x)) (st_send p xs)
  | st2so_rcv: forall p l s xs ys,
               length xs = length ys ->
               List.Forall (fun u => R (fst u) (snd u)) (zip ys xs) ->
               st2so R (so_receive p (zip (zip l s) ys)) (st_receive p (zip (zip l s) xs)).

Definition st2soC s1 s2 := paco2 (st2so) bot2 s1 s2.

Lemma st2so_mon: monotone2 st2so.
Proof. unfold monotone2.
       intros.
       induction IN; intros.
       - apply st2so_end.
       - specialize (st2so_snd r'); intro HS.
         apply HS with (l := l) (s := s) (x := x).
         apply LE, H.
       - specialize (st2so_rcv r'); intro HS.
         apply HS with (l := l) (s := s) (ys := ys). easy.
         apply Forall_forall.
         intros(x1,x2) Ha.
         simpl.
         apply LE.
         rewrite Forall_forall in H0.
         apply (H0 (x1,x2)).
         apply Ha.
Qed.

(*example so decomposition*)
CoFixpoint Et1 := st_receive "q" [("l7",sint,Et1)].
CoFixpoint Et2 := st_send "q" [("l8",sint,Et2)].

CoFixpoint Et1so := so_receive "q" [("l7",sint,Et1so)].
CoFixpoint Et2so := so_send "q" ("l8",sint,Et2so).

CoFixpoint eT1 := st_receive "p" [("l1",sint,st_send "p" [("l4",sint,Et1);
                                                         ("l5",sint,Et2);
                                                         ("l6",sint,eT1)]);
                                 ("l2",sint,st_send "q" [("l9",sint,eT1)]);
                                 ("l3",sint,st_receive "q" [("l10",sint,eT1)])].

CoFixpoint eT2 := so_receive "p" [("l1",sint,so_send "p" ("l4",sint,Et1so));
                                 ("l2",sint,so_send "q" ("l9",sint,eT2));
                                 ("l3",sint,so_receive "q" [("l10",sint,eT2)])].

Lemma T1soT2: st2soC eT2 eT1.
Proof. pcofix CIH.
       rewrite(st_eq eT1); rewrite(so_eq eT2); simpl.
       pfold.
       specialize (st2so_rcv (upaco2 st2so r) "p"
                              ["l1";"l2";"l3"]
                              [(I);(I);(I)]
                              ([(st_send "p" [("l4",sint,Et1);
                                              ("l5",sint,Et2);
                                              ("l6",sint,eT1)]);
                              (st_send "q" [("l9",sint,eT1)]);
                              (st_receive "q" [("l10",sint,eT1)])])
                              ([so_send "p" ("l4",sint,Et1so); 
                                so_send "q" ("l9",sint,eT2);
                                so_receive "q" [("l10",sint,eT2)]
                                ])
   
       ); intro Ha.
       simpl in Ha.
       apply Ha; clear Ha.
       simpl. easy.
       apply Forall_forall.
       intros (a,b) Hb.
       simpl in Hb.
       destruct Hb as [Hb | [Hb | [Hb | Hb ]]].
       simpl. inversion Hb. subst.
       left. pfold.
       apply st2so_snd. simpl.
       left. pcofix CIH2.
       pfold. rewrite(st_eq Et1). simpl.
       specialize (st2so_rcv (upaco2 st2so r) "q"
                             (["l7";"l7"])
                             [(I);(I)]
                             [Et1] [Et1so]
       ); intro Ha.
       simpl in Ha.
       rewrite(so_eq Et1so). simpl.
       apply Ha; clear Ha. easy.
       apply Forall_forall.
       intros (a,b) Hc.
       simpl in Hc.
       destruct Hc as [Hc | Hc].
       simpl. inversion Hc. subst. right. exact CIH2.
       easy.
       simpl. inversion Hb. subst.
       left. pfold.
       apply st2so_snd. simpl. right. exact CIH.
       simpl. inversion Hb. subst.
       left. pfold.
       specialize (st2so_rcv (upaco2 st2so r) "q"
                             (["l10";"l10"])
                             [(I);(I)]
                             [eT1] [eT2]
       ); intro Ha.
       simpl in Ha.
       apply Ha; clear Ha.
       simpl. easy.
       apply Forall_forall.
       intros (a,b) Hc.
       simpl in Hc.
       destruct Hc as [Hc | Hc].
       simpl. inversion Hc. subst. right. exact CIH.
       easy.
       easy.
Qed.










