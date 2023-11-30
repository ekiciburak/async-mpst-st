From ST Require Import stream st so si siso.
From mathcomp Require Import all_ssreflect seq.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Require Import Setoid.
Require Import Morphisms.

Inductive nRefinement: st -> st -> Prop :=
  | n_out  : forall w w' p l s, 
             CoNInR (p,"!"%string) (act w') -> nRefinement (st_send p [(l,s,w)]) w'
  | n_inp  : forall w w' p l s, 
             CoNInR (p,"?"%string) (act w') -> nRefinement (st_receive p [(l,s,w)]) w'
  | n_out_r: forall w w' p l s, 
             CoNInR (p,"!"%string) (act w) -> nRefinement w (st_send p [(l,s,w')])
  | n_inp_r: forall w w' p l s, 
             CoNInR (p,"?"%string) (act w) -> nRefinement w (st_receive p [(l,s,w')])
  | n_inp_l: forall w w' p l l' s s',
             l <> l' -> nRefinement (st_receive p [(l,s,w)]) (st_receive p [(l',s',w')])
  | n_inp_s: forall w w' p l s s',
             nsubsort s' s -> nRefinement (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])
  | n_inp_w: forall w w' p l s s',
             subsort s' s -> nRefinement w w' -> nRefinement (st_receive p [(l,s,w)]) (st_receive p [(l,s',w')])
  | n_a_l  : forall w w' p l l' s s' a n,
             l <> l' -> nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l',s',w')]) n)
  | n_a_s  : forall w w' p l s s' a n,
             nsubsort s' s -> 
             nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | n_a_w  : forall w w' p l s s' a n,
             subsort s' s ->
             nRefinement w (merge_ap_contn p a w' n) ->
             nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_receive p [(l,s',w')]) n)
  | n_i_o_1: forall w w' p q l l' s s', nRefinement (st_receive p [(l,s,w)]) (st_send q [(l',s',w')])
  | n_i_o_2: forall w w' p q l l' s s' (a: Ap p) n, nRefinement (st_receive p [(l,s,w)]) (merge_ap_contn p a (st_send q [(l',s',w')]) n)
  | n_out_l: forall w w' p l l' s s',
             l <> l' -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l',s',w')])
  | n_out_s: forall w w' p l s s',
             nsubsort s' s -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l,s',w')])
  | n_out_w: forall w w' p l s s',
             subsort s s' -> nRefinement w w' -> nRefinement (st_send p [(l,s,w)]) (st_send p [(l,s',w')])
  | n_b_l  : forall w w' p l l' s s' b n,
             l <> l' -> nRefinement (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l',s',w')]) n)
  | n_b_s  : forall w w' p l s s' b n,
             nsubsort s s' -> 
             nRefinement (st_send p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n)
  | n_b_w  : forall w w' p l s s' b n,
             subsort s s' ->
             nRefinement w (merge_bp_contn p b w' n) ->
             nRefinement (st_receive p [(l,s,w)]) (merge_bp_contn p b (st_send p [(l,s',w')]) n).

Notation "x '/~<' y" := (nRefinement x y) (at level 50, left associativity).

Lemma nrefL: forall w w',  w ~< w' -> (w /~< w' -> False).
Proof. intros w w' H.
       unfold refinement in H.
       punfold H; [ | apply refinementR_mon].
       intro Ha.
       induction Ha; intros.
       { inversion H.
         subst.
         apply inOutL in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s', w'0)]))).
         specialize(CoInSplit1 (p, "!"%string)
         (Delay(cocons (p, "!"%string) (act w'0)))
         (p, "!"%string) 
         (act w'0)
         ); intro Hb.
         apply Hb. simpl. easy. easy.
         subst.
         apply inOutL in H0. easy.
         admit.
       }
       { inversion H.
         subst.
         apply inOutL in H0. easy.
         rewrite(coseq_eq(act (p & [(l, s', w'0)]))).
         specialize(CoInSplit1 (p, "?"%string)
         (Delay(cocons (p, "?"%string) (act w'0)))
         (p, "?"%string) 
         (act w'0)
         ); intro Hb.
         apply Hb. simpl. easy. easy.
         subst.
         apply inOutL in H0. easy.
         admit.
       }
       { inversion H.
         subst.
         apply inOutL in H0. easy.
         rewrite(coseq_eq(act (p ! [(l, s0, w0)]))).
         unfold coseq_id. simpl.
         specialize(CoInSplit1 (p, "!"%string)
         (Delay(cocons (p, "!"%string) (act w0)))
         (p, "!"%string) 
         (act w0)
         ); intro Hb.
         apply Hb. simpl. easy. easy.
         subst.
         admit.
         admit.
       }
Admitted.
