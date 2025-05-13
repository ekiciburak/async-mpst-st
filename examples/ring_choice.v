Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.acteqfacts ST.src.nondepro ST.src.siso ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From mathcomp Require Import all_ssreflect seq ssrnat.
From Paco Require Import paco.
Require Import String List.
Import ListNotations.
Import CoListNotations.
Require Import Setoid.
Require Import Coq.Arith.Arith.
Require Import Morphisms.
Require Import Coq.Logic.Classical_Prop Coq.Logic.ClassicalFacts.

Local Open Scope string_scope.

Definition ltB := lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, (lt_var 0));
                                                                 ("sub", I, (lt_var 0))])]).

Definition ltBOp := lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, (lt_var 0))]); 
                                        ("sub", I, lt_receive "A" [("add", I, (lt_var 0))])]).

CoFixpoint rcp := st_receive "A" [|("add", I, st_send "C" [|("add", I, rcp);
                                                          ("sub", I, rcp)|])|].

CoFixpoint rcop := st_send "C" [|("add", I, st_receive "A" [|("add", I, rcop)|]); 
                                ("sub", I, st_receive "A" [|("add", I, rcop)|])|].


CoFixpoint w1 := st_receive "A" [|("add", I, st_send "C" [|("add", I, w1)|])|].
CoFixpoint w2 := st_send "C" [|("add", I, st_receive "A" [|("add", I, w2)|])|].

CoFixpoint w3 := st_receive "A" [|("add", I, st_send "C" [|("sub", I, w3)|])|].
CoFixpoint w4 := st_send "C" [|("sub", I, st_receive "A" [|("add", I, w4)|])|].

Definition d1: Dpf := dpf_receive "A" "add" (I) (dpf_send "C" "add" (I) dpf_end).
Definition d2: Dpf := dpf_receive "A" "add" (I) (dpf_send "C" "sub" (I) dpf_end).
Definition d3: Dpf := dpf_send "C" "add" (I) (dpf_receive "A" "add" (I) dpf_end).
Definition d4: Dpf := dpf_send "C" "sub" (I) (dpf_receive "A" "add" (I) dpf_end).

Definition w5 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) w1 k.
Definition w6 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) w3 k.
Definition w7 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) w2 k.
Definition w8 (n m k: nat): st := merge_dpf_contn (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) w4 k.

Fixpoint rShape (l: list bool): Dpf :=
  match l with
    | nil   => dpf_end
    | x::xs => if x then 
               dpf_receive "A" "add" (I) (dpf_send "C" "add" (I) (rShape xs))
               else
               dpf_receive "A" "add" (I) (dpf_send "C" "sub" (I) (rShape xs))
  end.

Fixpoint sShape (l: list bool): Dpf :=
  match l with
    | nil   => dpf_end
    | x::xs => if x then 
               dpf_send "C" "add" (I) (dpf_receive "A" "add" (I) (sShape xs))
               else
               dpf_send "C" "sub" (I) (dpf_receive "A" "add" (I) (sShape xs))
  end.

Lemma refmG1: forall l W1 W2,
  refinement W1 W2 ->
  refinement (merge_dpf_cont (sShape l) W1) (merge_dpf_cont (rShape l) W2).
Proof. intro l.
       induction l; intros.
       - simpl. rewrite !dpfend_dn. easy.
       - case_eq a; intros.
         + subst. simpl.
           apply IHl in H.
           pfold.
           rewrite(st_eq(merge_dpf_cont (dpf_send "C" "add" (I) (dpf_receive "A" "add" (I) (sShape l))) W1)). 
           rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (dpf_send "C" "add" (I) (rShape l))) W2)). simpl.
           rewrite(st_eq(merge_dpf_cont (dpf_send "C" "add" (I) (rShape l)) W2)). simpl.
           specialize(ref_b (upaco2 refinementR bot2)
           (merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)
           (merge_dpf_cont (rShape l) W2)
           "C" "add" (I) (I)
           (bp_receivea "A" "add" (I)) 1
           ); intro HS.
           simpl in HS.
           rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [|("add", I, merge_dpf_cont (rShape l) W2)|]))) in HS. simpl in HS.
           apply HS.
           constructor.
           left.
           rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_dpf_cont (rShape l) W2))). simpl.
           rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
           pfold.
           specialize(ref_a (upaco2 refinementR bot2)
           (merge_dpf_cont (sShape l) W1)
           (merge_dpf_cont (rShape l) W2)
           "A" "add" (I) (I)
           (ap_end) 1
           ); intro HR.
           simpl in HR. rewrite !apend_an in HR.
           apply HR.
           constructor.
           left. easy.
           
           clear HS HR.
           
(*        apply IHl in H. *)
       apply refEquivR in H.
       pinversion H.
       (*receive*)
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       subst.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [|(l0, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l0, s, w)|]))).
       { rewrite apfend_an. easy. }
       assert(isInA (ApnA3 a n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5. apply actdRER. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply actdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.

         easy.
         split.
         rewrite H5.
         apply IactdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply IactdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, rcv)::l1). exists ((p, rcv)::l2).
         split.
         rewrite(coseq_eq(act (p & [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdRNER. simpl. easy. easy. rewrite apfend_an. easy.
         split.
         apply IactdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       assert((p ! [|(l0, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l0, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       assert(isInB (BpnB3 b n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5.
         apply actdSER. simpl. easy. easy.
         rewrite bpfend_bn. easy.
         split.
         apply actdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         split.
         apply coseqSendIn. easy.
         split.
         apply IactdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, snd)::l1). exists ((p, snd)::l2).
         split.
         rewrite(coseq_eq(act (p ! [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdSNER. simpl. easy. easy. rewrite bpfend_bn. easy.
         split.
         apply IactdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy. easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
         
       (*end*)
       exists nil. exists nil.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       split. pfold. constructor.
       split. pfold. constructor.
       split. constructor.
       split. constructor. easy.
       apply refinementR3_mon.

       (*2nd goal*)
           clear HS.
 (*receive*)
       apply refEquivR in H.
       pinversion H.
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|])))). simpl.
       rewrite <- H0.
       assert((p & [|(l0, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l0, s, w)|]))).
       { rewrite apfend_an. easy. }
       assert(isInA (ApnA3 a n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split. 
         rewrite(coseq_eq (act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         rewrite H5.
         apply actdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdRER. simpl.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l0, s, w)|]))). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdRER.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,rcv)::l1). exists(("A",rcv)::(p,rcv)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p & [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdRNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l0, s, w)|]))). simpl. easy. easy.
         constructor.
         case_eq(eqb p "A"); intro Heq.
         ++ rewrite eqb_eq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, "A" & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := ("A",rcv)) (ys := (act ("A" & [|(l0, s, w)|]))). simpl. easy. easy.
         ++ rewrite eqb_neq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p & [|(l0, s, w)|]))). simpl. easy.
            intro Hn. apply Heq. inversion Hn. easy.
            rewrite(coseq_eq (act (p & [|(l0, s, w)|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := (p,rcv)) (ys := (act w)). simpl. easy. easy.
         apply coseqRecvIn. apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdRNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.

       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       rewrite(st_eq (merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|])))). simpl.
       rewrite <- H0.
       assert((p ! [|(l0, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l0, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       assert(isInB (BpnB3 b n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         rewrite H5.
         apply actdSER. simpl. easy. easy. rewrite bpfend_bn.
         apply coseqINGA.  easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdSER. 
         easy. 
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l0, s, w)|])) ). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdSER. easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         simpl. 
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,snd)::l1). exists(("A",rcv)::(p,snd)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p ! [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdSNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l0, s, w)|])) ). simpl. easy. easy.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p ! [|(l0, s, w)|])) ). simpl. easy. easy.
         rewrite(coseq_eq(act (p ! [|(l0, s, w)|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p,snd)) (ys := (act w) ). simpl. easy. easy.
         apply coseqRecvIn. apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys :=  (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdSNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
       (*end*)
       rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (end))). simpl.
       rewrite <- H1.
       rewrite(coseq_eq(act ("A" & [|("add", I, end)|]))). unfold coseq_id. simpl.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       exists[("A",rcv)]. exists[("A",rcv)].
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       split. constructor.
       simpl.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil). simpl. easy. easy.
       constructor.
       split. constructor.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil). simpl. easy. easy.
       constructor.
       easy.
       apply refinementR3_mon.
         + subst. simpl.
           apply IHl in H.
           pfold.
           rewrite(st_eq(merge_dpf_cont (dpf_send "C" "sub" (I) (dpf_receive "A" "add" (I) (sShape l))) W1)).
           rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (dpf_send "C" "sub" (I) (rShape l))) W2)). simpl.
           rewrite(st_eq(merge_dpf_cont (dpf_send "C" "sub" (I) (rShape l)) W2)). simpl.
           specialize(ref_b (upaco2 refinementR bot2)
           (merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)
           (merge_dpf_cont (rShape l) W2)
           "C" "sub" (I) (I)
           (bp_receivea "A" "add" (I)) 1
           ); intro HS.
           simpl in HS.
           rewrite(st_eq((merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [|("sub", I, merge_dpf_cont (rShape l) W2)|])))) in HS. simpl in HS.
           apply HS.
           constructor.
           left.
           rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_dpf_cont (rShape l) W2))). simpl.
           rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
           pfold.
           specialize(ref_a (upaco2 refinementR bot2)
           (merge_dpf_cont (sShape l) W1)
           (merge_dpf_cont (rShape l) W2)
           "A" "add" (I) (I)
           (ap_end) 1
           ); intro HR.
           simpl in HR. rewrite !apend_an in HR.
           apply HR.
           constructor. left. easy.
           clear HS HR.
           
(*        apply IHl in H. *)
       apply refEquivR in H.
       pinversion H.
       (*receive*)
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       subst.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [|(l0, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l0, s, w)|]))).
       { rewrite apfend_an. easy. }
       assert(isInA (ApnA3 a n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5. apply actdRER. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply actdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.

         easy.
         split.
         rewrite H5.
         apply IactdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply IactdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, rcv)::l1). exists ((p, rcv)::l2).
         split.
         rewrite(coseq_eq(act (p & [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdRNER. simpl. easy. easy. rewrite apfend_an. easy.
         split.
         apply IactdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       assert((p ! [|(l0, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l0, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       assert(isInB (BpnB3 b n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5.
         apply actdSER. simpl. easy. easy.
         rewrite bpfend_bn. easy.
         split.
         apply actdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         split.
         apply coseqSendIn. easy.
         split.
         apply IactdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, snd)::l1). exists ((p, snd)::l2).
         split.
         rewrite(coseq_eq(act (p ! [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdSNER. simpl. easy. easy. rewrite bpfend_bn. easy.
         split.
         apply IactdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy. easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
         
       (*end*)
       exists nil. exists nil.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       split. pfold. constructor.
       split. pfold. constructor.
       split. constructor.
       split. constructor. easy.
       apply refinementR3_mon.

       (*2nd goal*)
           clear HS.
 (*receive*)
       apply refEquivR in H.
       pinversion H.
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|])))). simpl.
       rewrite <- H0.
       assert((p & [|(l0, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l0, s, w)|]))).
       { rewrite apfend_an. easy. }
       assert(isInA (ApnA3 a n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split. 
         rewrite(coseq_eq (act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         rewrite H5.
         apply actdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdRER. simpl.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l0, s, w)|]))). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdRER.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,rcv)::l1). exists(("A",rcv)::(p,rcv)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p & [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdRNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l0, s, w)|]))). simpl. easy. easy.
         constructor.
         case_eq(eqb p "A"); intro Heq.
         ++ rewrite eqb_eq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, "A" & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := ("A",rcv)) (ys := (act ("A" & [|(l0, s, w)|]))). simpl. easy. easy.
         ++ rewrite eqb_neq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p & [|(l0, s, w)|]))). simpl. easy.
            intro Hn. apply Heq. inversion Hn. easy.
            rewrite(coseq_eq (act (p & [|(l0, s, w)|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := (p,rcv)) (ys := (act w)). simpl. easy. easy.
         apply coseqRecvIn. apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdRNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.

       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       rewrite(st_eq (merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|])))). simpl.
       rewrite <- H0.
       assert((p ! [|(l0, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l0, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       assert(isInB (BpnB3 b n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         rewrite H5.
         apply actdSER. simpl. easy. easy. rewrite bpfend_bn.
         apply coseqINGA.  easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdSER. 
         easy. 
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l0, s, w)|])) ). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdSER. easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         simpl. 
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,snd)::l1). exists(("A",rcv)::(p,snd)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p ! [|(l0, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdSNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l0, s, w)|])) ). simpl. easy. easy.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l0, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p ! [|(l0, s, w)|])) ). simpl. easy. easy.
         rewrite(coseq_eq(act (p ! [|(l0, s, w)|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p,snd)) (ys := (act w) ). simpl. easy. easy.
         apply coseqRecvIn. apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys :=  (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l0, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdSNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
       (*end*)
       rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (sShape l)) W1)). simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (end))). simpl.
       rewrite <- H1.
       rewrite(coseq_eq(act ("A" & [|("add", I, end)|]))). unfold coseq_id. simpl.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       exists[("A",rcv)]. exists[("A",rcv)].
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       split. constructor.
       simpl.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil ). simpl. easy. easy.
       constructor.
       split. constructor.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil ). simpl. easy. easy.
       constructor.
       easy.
       apply refinementR3_mon.
Qed.

Fixpoint consK {A} (k: nat) (l: list A): list A :=
  match k with
    | 0   => nil
    | S m => l ++ (consK m l)
  end. 


Definition actL := [("A",rcv); ("C",snd)].

Lemma acteqr1: coseqInLC (act w2) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("C" ! [|("add", I, "A" & [|("add", I, w2)|])|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. 
       rewrite(coseq_eq(act ("A" & [|("add", I, w2)|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr9: coseqInLC (act w3) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w3). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("sub", I, w3)|])|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl.  left. easy.
       left. 
       rewrite(coseq_eq(act ("C" ! [|("sub", I, w3)|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr2: coseqInLC (act w1) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("add", I, w1)|])|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. 
       rewrite(coseq_eq(act ("C" ! [|("add", I, w1)|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr10: coseqInLC (act w4) actL.
Proof. unfold actL.
       pcofix CIH.
       rewrite(st_eq w4). simpl.
       rewrite(coseq_eq(act ("C" ! [|("sub", I, "A" & [|("add", I, w4)|])|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. right. left. easy.
       left. 
       rewrite(coseq_eq(act ("A" & [|("add", I, w4)|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       right. exact CIH.
Qed.

Lemma acteqr3: coseqInR actL (act w2).
Proof. unfold actL.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("C" ! [|("add", I, "A" & [|("add", I, w2)|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("C", snd)) (ys := (act ("A" & [|("add", I, w2)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("A" & [|("add", I, w2)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w2)). simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [|("add", I, w2)|]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr11: coseqInR actL (act w3).
Proof. unfold actL.
       rewrite(st_eq w3). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("sub", I, w3)|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [|("sub", I, w3)|]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [|("sub", I, w3)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [|("sub", I, w3)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w3)). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr4: coseqInR actL (act w1).
Proof. unfold actL.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("add", I, w1)|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [|("add", I, w1)|]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [|("add", I, w1)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [|("add", I, w1)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w1)). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr12: coseqInR actL (act w4).
Proof. unfold actL.
       rewrite(st_eq w4). simpl.
       rewrite(coseq_eq(act ("C" ! [|("sub", I, "A" & [|("add", I, w4)|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit2 with (y := ("C", snd)) (ys := (act ("A" & [|("add", I, w4)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("A" & [|("add", I, w4)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w4)). simpl. easy. easy.
       constructor.
       apply CoInSplit1 with (y := ("C", snd)) (ys :=  (act ("A" & [|("add", I, w4)|]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr5: coseqInLC (act ("A" & [|("add", I, w2)|])) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act ("A" & [|("add", I, w2)|]))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr1.
Qed.

Lemma acteqr13: coseqInLC (act ("A" & [|("add", I, w4)|])) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act ("A" & [|("add", I, w4)|]))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr10.
Qed.

Lemma acteqr6: coseqInLC (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr2.
Qed.

Lemma acteqr14: coseqInLC (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w3)) actL.
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w3))). unfold coseq_id. simpl.
       pfold.
       constructor. simpl. left. easy.
       left.
       apply acteqr9.
Qed.

Lemma acteqr7: coseqInR actL (act ("A" & [|("add", I, w2)|])).
Proof. unfold actL.
       rewrite(st_eq w2). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("add", I, "A" & [|("add", I, w2)|])|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [|("add", I, "A" & [|("add", I, w2)|])|]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [|("add", I, "A" & [|("add", I, w2)|])|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [|("add", I, "A" & [|("add", I, w2)|])|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [|("add", I, w2)|]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr15: coseqInR actL (act ("A" & [|("add", I, w4)|])).
Proof. unfold actL.
       rewrite(st_eq w4). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("sub", I, "A" & [|("add", I, w4)|])|])|]))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act ("C" ! [|("sub", I, "A" & [|("add", I, w4)|])|]))). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [|("sub", I, "A" & [|("add", I, w4)|])|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [|("sub", I, "A" & [|("add", I, w4)|])|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act ("A" & [|("add", I, w4)|]))). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr8: coseqInR actL (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)).
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w1)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act w1)). simpl. easy. easy.
       rewrite(st_eq w1). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("add", I, w1)|])|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [|("add", I, w1)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [|("add", I, w1)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w1)). simpl. easy. easy.
       constructor.
Qed.

Lemma acteqr16: coseqInR actL (act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w3)).
Proof. unfold actL.
       rewrite(coseq_eq(act (merge_bp_cont "C" (bp_receivea "A" "add" (I)) w3))). unfold coseq_id. simpl.
       constructor.
       apply CoInSplit1 with (y := ("A", rcv)) (ys := (act w3)). simpl. easy. easy.
       constructor.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act w3)). simpl. easy. easy.
       rewrite(st_eq w3). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, "C" ! [|("sub", I, w3)|])|]))). unfold coseq_id. simpl.
       apply CoInSplit2 with (y := ("A", rcv)) (ys := (act ("C" ! [|("sub", I, w3)|]))). simpl. easy. easy.
       rewrite(coseq_eq(act ("C" ! [|("sub", I, w3)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("C", snd)) (ys := (act w3)). simpl. easy. easy.
       constructor.
Qed.

Lemma refm1: forall m W1 W2, 
  refinement W1 W2 ->
  refinement (merge_dpf_cont (DpnD3 d4 m) W1) (merge_dpf_cont (DpnD3 d2 m) W2).
Proof. intro m.
       induction m; intros.
       - simpl. rewrite !dpfend_dn. easy.
       - rewrite !DpnD3C !merge_mergeD.
         unfold d4 at 1.
         unfold d2 at 1.
         rewrite(st_eq((merge_dpf_cont (dpf_send "C" "sub" (I) (dpf_receive "A" "add" (I) dpf_end)) (merge_dpf_cont (DpnD3 d4 m) W1)))).
         simpl.
         rewrite(st_eq  (merge_dpf_cont (dpf_receive "A" "add" (I) (dpf_send "C" "sub" (I) dpf_end)) (merge_dpf_cont (DpnD3 d2 m) W2))).
         simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) dpf_end) (merge_dpf_cont (DpnD3 d4 m) W1))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "C" "sub" (I) dpf_end) (merge_dpf_cont (DpnD3 d2 m) W2))). simpl.
         rewrite !dpfend_dn.
         pfold.
         specialize(ref_b (upaco2 refinementR bot2)
                          ("A" & [|("add", I, merge_dpf_cont (DpnD3 d4 m) W1)|])
                          (merge_dpf_cont (DpnD3 d2 m) W2)
                          "C" "sub" (I) (I)
                          (bp_receivea "A" "add" (I)) 1
                           ); intro HS.
        simpl in HS.
        rewrite(st_eq((merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [|("sub", I, merge_dpf_cont (DpnD3 d2 m) W2)|])))) in HS. simpl in HS.
        apply HS.
        constructor.
        left.
        rewrite(st_eq((merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_dpf_cont (DpnD3 d2 m) W2)))). simpl.
        pfold.
        specialize(ref_a (upaco2 refinementR bot2)
                         (merge_dpf_cont (DpnD3 d4 m) W1)
                         (merge_dpf_cont (DpnD3 d2 m) W2)
                         "A" "add" (I) (I)
                         (ap_end) 1
                          ); intro HR.
       simpl in HR.
       rewrite !apend_an in HR.
       apply HR.
       constructor.
       left. apply IHm. easy.
       
       
       apply IHm in H.
       apply refEquivR in H.
       pinversion H.

       (*receive*)
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [|(l, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l, s, w)|]))).
       { rewrite apfend_an. easy. }
       assert(isInA (ApnA3 a n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5. apply actdRER. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply actdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.

         easy.
         split.
         rewrite H5.
         apply IactdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply IactdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, rcv)::l1). exists ((p, rcv)::l2).
         split.
         rewrite(coseq_eq(act (p & [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdRNER. simpl. easy. easy. rewrite apfend_an. easy.
         split.
         apply IactdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.

       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       assert((p ! [|(l, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       assert(isInB (BpnB3 b n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5.
         apply actdSER. simpl. easy. easy.
         rewrite bpfend_bn. easy.
         split.
         apply actdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         split.
         apply coseqSendIn. easy.
         split.
         apply IactdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, snd)::l1). exists ((p, snd)::l2).
         split.
         rewrite(coseq_eq(act (p ! [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdSNER. simpl. easy. easy. rewrite bpfend_bn. easy.
         split.
         apply IactdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy. easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
         
       (*end*)
       exists nil. exists nil.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       split. pfold. constructor.
       split. pfold. constructor.
       split. constructor.
       split. constructor. easy.
       apply refinementR3_mon.
       
       (*2nd goal*)
       
       (*receive*)
       apply IHm in H.
       apply refEquivR in H.
       pinversion H.
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [|(l, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l, s, w)|]))).
       { rewrite apfend_an. easy. }
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|])))). simpl.
       assert(isInA (ApnA3 a n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split. 
         rewrite(coseq_eq (act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         rewrite H5.
         apply actdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdRER. simpl.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l, s, w)|]))). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdRER.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,rcv)::l1). exists(("A",rcv)::(p,rcv)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p & [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdRNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l, s, w)|]))). simpl. easy. easy.
         constructor.
         case_eq(eqb p "A"); intro Heq.
         ++ rewrite eqb_eq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, "A" & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := ("A",rcv)) (ys := (act ("A" & [|(l, s, w)|]))). simpl. easy. easy.
         ++ rewrite eqb_neq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p & [|(l, s, w)|]))). simpl. easy.
            intro Hn. apply Heq. inversion Hn. easy.
            rewrite(coseq_eq (act (p & [|(l, s, w)|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := (p,rcv)) (ys := (act w)). simpl. easy. easy.
         apply coseqRecvIn. apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdRNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.

       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       assert((p ! [|(l, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|])))). simpl.
       assert(isInB (BpnB3 b n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         rewrite H5.
         apply actdSER. simpl. easy. easy. rewrite bpfend_bn.
         apply coseqINGA.  easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdSER. 
         easy. 
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l, s, w)|])) ). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdSER. easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         simpl. 
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,snd)::l1). exists(("A",rcv)::(p,snd)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p ! [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdSNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l, s, w)|])) ). simpl. easy. easy.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p ! [|(l, s, w)|])) ). simpl. easy. easy.
         rewrite(coseq_eq(act (p ! [|(l, s, w)|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p,snd)) (ys := (act w) ). simpl. easy. easy.
         apply coseqRecvIn. apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys :=  (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdSNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
       (*end*)
       rewrite(coseq_eq(act ("A" & [|("add", I, end)|]))). unfold coseq_id. simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (end))). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, end)|]))). unfold coseq_id. simpl.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       exists[("A",rcv)]. exists[("A",rcv)].
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       split. constructor.
       simpl.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil ). simpl. easy. easy.
       constructor.
       split. constructor.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil ). simpl. easy. easy.
       constructor.
       easy.
       apply refinementR3_mon.
Qed.

(*here*)
Lemma refm2: forall m W1 W2, 
  refinement W1 W2 ->
  refinement (merge_dpf_cont (DpnD3 d3 m) W1) (merge_dpf_cont (DpnD3 d1 m) W2).
Proof. intro m.
       induction m; intros.
       - simpl. rewrite !dpfend_dn. easy.
       - rewrite !DpnD3C !merge_mergeD.
         unfold d3 at 1.
         unfold d1 at 1.
         rewrite(st_eq((merge_dpf_cont (dpf_send "C" "add" (I) (dpf_receive "A" "add" (I) dpf_end)) (merge_dpf_cont (DpnD3 d3 m) W1)))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) (dpf_send "C" "add" (I) dpf_end)) (merge_dpf_cont (DpnD3 d1 m) W2))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_receive "A" "add" (I) dpf_end) (merge_dpf_cont (DpnD3 d3 m) W1))). simpl.
         rewrite(st_eq(merge_dpf_cont (dpf_send "C" "add" (I) dpf_end) (merge_dpf_cont (DpnD3 d1 m) W2))). simpl.
         rewrite !dpfend_dn.
         pfold.
         specialize(ref_b (upaco2 refinementR bot2)
                          ("A" & [|("add", I, merge_dpf_cont (DpnD3 d3 m) W1)|])
                          (merge_dpf_cont (DpnD3 d1 m) W2)
                          "C" "add" (I) (I)
                          (bp_receivea "A" "add" (I)) 1
                           ); intro HS.
        simpl in HS.
        rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [|("add", I, merge_dpf_cont (DpnD3 d1 m) W2)|]))) in HS.
        simpl in HS.
        apply HS.
        constructor.
        left.
        pfold.
        rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_dpf_cont (DpnD3 d1 m) W2))). simpl.
        specialize(ref_a (upaco2 refinementR bot2)
                         (merge_dpf_cont (DpnD3 d3 m) W1)
                         (merge_dpf_cont (DpnD3 d1 m) W2)
                         "A" "add" (I) (I)
                         (ap_end) 1
                          ); intro HR.
       simpl in HR.
       rewrite !apend_an in HR.
       apply HR.
       constructor.
       left. apply IHm. easy.

       apply IHm in H.
       apply refEquivR in H.
       pinversion H.

       (*receive*)
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [|(l, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l, s, w)|]))).
       { rewrite apfend_an. easy. }
       assert(isInA (ApnA3 a n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5. apply actdRER. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply actdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.

         easy.
         split.
         rewrite H5.
         apply IactdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         apply IactdRER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.

         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, rcv)::l1). exists ((p, rcv)::l2).
         split.
         rewrite(coseq_eq(act (p & [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdRNER. simpl. easy. easy. rewrite apfend_an. easy.
         split.
         apply IactdRNER.
         case_eq n; intros Hn.
         easy. rewrite <- InN; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.

       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       assert((p ! [|(l, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       assert(isInB (BpnB3 b n) p = false) as Hnin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists l1. exists l2.
         split.
         rewrite H5.
         apply actdSER. simpl. easy. easy.
         rewrite bpfend_bn. easy.
         split.
         apply actdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         split.
         apply coseqSendIn. easy.
         split.
         apply IactdSER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hnin in Hac. destruct Hac; easy.
         easy.
         easy.
       + exists ((p, snd)::l1). exists ((p, snd)::l2).
         split.
         rewrite(coseq_eq(act (p ! [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. left. easy.
         left.
         apply coseqINGA. easy.
         split.
         apply actdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         rewrite H5.
         apply IactdSNER. simpl. easy. easy. rewrite bpfend_bn. easy.
         split.
         apply IactdSNER.
         case_eq n; intros Hn.
         easy. rewrite <- InNS; easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy. easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
         
       (*end*)
       exists nil. exists nil.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       split. pfold. constructor.
       split. pfold. constructor.
       split. constructor.
       split. constructor. easy.
       apply refinementR3_mon.

       (*2nd goal*)
       
       (*receive*)
       apply IHm in H.
       apply refEquivR in H.
       pinversion H.
       rewrite <- meqAp3 in H1, H4, H5.
       rewrite <- meqAp3.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       specialize(classic (coseqIn (p, rcv) (act w))); intro Hc.
       assert((p & [|(l, s, w)|]) = 
              (merge_apf_cont apf_end (p & [|(l, s, w)|]))).
       { rewrite apfend_an. easy. }
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|])))). simpl.
       assert(isInA (ApnA3 a n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InN; easy.
       }
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split. 
         rewrite(coseq_eq (act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         rewrite H5.
         apply actdRER. simpl. easy. easy.
         rewrite apfend_an. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdRER. simpl.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l, s, w)|]))). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdRER.
         easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInRAG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,rcv)::l1). exists(("A",rcv)::(p,rcv)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p & [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdRNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p & [|(l, s, w)|]))). simpl. easy. easy.
         constructor.
         case_eq(eqb p "A"); intro Heq.
         ++ rewrite eqb_eq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, "A" & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := ("A",rcv)) (ys := (act ("A" & [|(l, s, w)|]))). simpl. easy. easy.
         ++ rewrite eqb_neq in Heq. subst.
            rewrite(coseq_eq(act ("A" & [|("add", I, p & [|(l, s, w)|])|]))). unfold coseq_id. simpl.
            apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p & [|(l, s, w)|]))). simpl. easy.
            intro Hn. apply Heq. inversion Hn. easy.
            rewrite(coseq_eq (act (p & [|(l, s, w)|]))). unfold coseq_id. simpl.
            apply CoInSplit1 with (y := (p,rcv)) (ys := (act w)). simpl. easy. easy.
         apply coseqRecvIn. apply coseqRecvIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_apf_cont (ApnA3 a n) (p & [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdRNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInRARevG. right. easy. 
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.

       (*send*)
       rewrite <- meqBp3.
       rewrite <- meqBp3 in H1, H4, H5.
       destruct H5 as (l1,(l2,(Hu,(Hv,(Hw,(Hy,Hz)))))).
       assert((p ! [|(l, s, w)|]) = 
              (merge_bpf_cont bpf_end (p ! [|(l, s, w)|]))).
       { rewrite bpfend_bn. easy. }
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|])))). simpl.
       assert(isInB (BpnB3 b n) p = false) as Hin.
       { case_eq n; intros.
         - easy.
         - rewrite <- InNS; easy.
       }
       specialize(classic (coseqIn (p, snd) (act w))); intro Hc.
       destruct Hc as [Hc | Hc].
       + exists (("A", rcv)::l1). exists (("A", rcv)::l2).
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         rewrite H5.
         apply actdSER. simpl. easy. easy. rewrite bpfend_bn.
         apply coseqINGA.  easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply actdSER. 
         easy. 
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         apply coseqINGA. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l, s, w)|])) ). simpl. easy. easy.
         apply coseqRecvIn.
         apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn.
         apply IactdSER. easy.
         specialize(actionExL _ _ _ Hc H4); intro Hac.
         apply csInSBG in Hac.
         rewrite Hin in Hac. destruct Hac; easy.
         easy.
         simpl. 
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. right. apply Hz. easy.
         simpl. intro Hx. 
         destruct Hx. left. easy. right. apply Hz. easy.
       + exists(("A",rcv)::(p,snd)::l1). exists(("A",rcv)::(p,snd)::l2).
         split. pfold.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         constructor. simpl. left. easy.
         left.
         rewrite(coseq_eq(act (p ! [|(l, s, w)|]))). unfold coseq_id. simpl.
         pfold.
         constructor. simpl. right. left. easy.
         left.
         apply coseqINGA. apply coseqINGA. easy.
         split.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|])) ). unfold coseq_id. simpl.
         pfold. constructor. simpl. left. easy.
         left.
         apply coseqINGA.
         apply actdSNER.
         easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys := (act (p ! [|(l, s, w)|])) ). simpl. easy. easy.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, p ! [|(l, s, w)|])|]))). unfold coseq_id. simpl.
         apply CoInSplit2 with (y := ("A",rcv)) (ys := (act (p ! [|(l, s, w)|])) ). simpl. easy. easy.
         rewrite(coseq_eq(act (p ! [|(l, s, w)|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := (p,snd)) (ys := (act w) ). simpl. easy. easy.
         apply coseqRecvIn. apply coseqSendIn. easy.
         split.
         constructor.
         rewrite(coseq_eq(act ("A" & [|("add", I, merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|]))|]))). unfold coseq_id. simpl.
         apply CoInSplit1 with (y := ("A",rcv)) (ys :=  (act (merge_bpf_cont (BpnB3 b n) (p ! [|(l, s', w')|])))). simpl. easy. easy.
         apply coseqRecvIn. 
         apply IactdSNER. easy.
         specialize(actionExLN _ _ _ Hc H4); intro Hac.
         intro HH. apply Hac.
         apply csInSBRevG. right. easy.
         easy. simpl.
         intro x. split. simpl. intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
         intro Hx.
         destruct Hx. left. easy. destruct H6. right. left. easy. right. right. apply Hz. easy.
       (*end*)
       rewrite(coseq_eq(act ("A" & [|("add", I, end)|]))). unfold coseq_id. simpl.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) (end))). simpl.
       rewrite(coseq_eq(act ("A" & [|("add", I, end)|]))). unfold coseq_id. simpl.
       rewrite(coseq_eq(act (end))). unfold coseq_id. simpl.
       exists[("A",rcv)]. exists[("A",rcv)].
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       
       split. pfold. constructor. simpl. left. easy.
       left. pfold. constructor.
       split. constructor.
       simpl.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil ). simpl. easy. easy.
       constructor.
       split. constructor.
       apply CoInSplit1 with (y := ("A",rcv)) (ys := conil ). simpl. easy. easy.
       constructor.
       easy.
       apply refinementR3_mon.
Qed.

Lemma refw2w1: refinement w2 w1.
Proof. pcofix CIH.
       pfold.
       rewrite(st_eq w2). rewrite(st_eq w1). simpl.
       specialize(ref_b (upaco2 refinementR r) ("A" & [|("add", I, w2)|]) (w1)
                          "C" "add" (I) (I) (@bp_receivea "C" "A" "add" (I)) 1
                          ); intro Hb.
       simpl in Hb.
       rewrite(st_eq (merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [|("add", I, w1)|]))) in Hb. simpl in Hb.
       apply Hb.
       constructor.
       left. pfold.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) w1)). simpl.
       clear Hb.

       specialize(ref_a (upaco2 refinementR r) (w2) (w1)
                          "A" "add" (I) (I) (ap_end) 1
                          ); intro Ha.
       simpl in Ha.
       rewrite(st_eq(merge_ap_cont "A" ap_end ("A" & [|("add", I, w1)|]))) in Ha. simpl in Ha.
       apply Ha. constructor.
       rewrite apend_an.
       right. exact CIH.
       
       rewrite apend_an.
       exists actL. exists actL.
       split.
       apply acteqr1.
       split.
       apply acteqr2.
       split.
       apply acteqr3.
       split.
       apply acteqr4.
       easy.
       
       exists actL. exists actL.
       split.
       apply acteqr5.
       split.
       apply acteqr6.
       split.
       apply acteqr7.
       split.
       apply acteqr8.
       easy.
Qed.

Lemma refw7w5: forall k n m, refinement (w7 n m k) (w5 n m k).
Proof. unfold w5, w7.
       intro k.
       induction k; intros.
       - simpl. apply refw2w1.
       - rewrite <- !meqDpf. rewrite DpnD3C.
         rewrite DpnD3C.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k)) w1) =
                (merge_dpf_cont (DpnD3 d1 n) (merge_dpf_cont (DpnD3 d2 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k) w1)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k)) w2) =
                (merge_dpf_cont (DpnD3 d3 n) (merge_dpf_cont (DpnD3 d4 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k) w2)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H0.
         apply refm2.
         apply refm1.
         specialize(IHk n m).
         rewrite <- !meqDpf in IHk. easy.
Qed.

Lemma refw4w3: refinement w4 w3.
Proof. pcofix CIH.
       pfold.
       rewrite(st_eq w4). rewrite(st_eq w3). simpl.
       specialize(ref_b (upaco2 refinementR r) ("A" & [|("add", I, w4)|]) (w3)
                          "C" "sub" (I) (I) (@bp_receivea "C" "A" "add" (I)) 1
                          ); intro Hb.
       simpl in Hb.
       rewrite(st_eq (merge_bp_cont "C" (bp_receivea "A" "add" (I)) ("C" ! [|("sub", I, w3)|]))) in Hb. simpl in Hb.
       apply Hb.
       constructor.
       left. pfold.
       rewrite(st_eq(merge_bp_cont "C" (bp_receivea "A" "add" (I)) w3)). simpl.
       clear Hb.

       specialize(ref_a (upaco2 refinementR r) (w4) (w3)
                          "A" "add" (I) (I) (ap_end) 1
                          ); intro Ha.
       simpl in Ha.
       rewrite(st_eq(merge_ap_cont "A" ap_end ("A" & [|("add", I, w3)|]))) in Ha. simpl in Ha.
       apply Ha. constructor.
       rewrite apend_an.
       right. exact CIH.

       rewrite apend_an.
       exists actL. exists actL.
       split.
       apply acteqr10.
       split.
       apply acteqr9.
       split.
       apply acteqr12.
       split.
       apply acteqr11.
       easy.

       exists actL. exists actL.
       split.
       apply acteqr13.
       split.
       apply acteqr14.
       split.
       apply acteqr15.
       split.
       apply acteqr16.
       easy.
Qed.

Lemma refw8w6: forall k n m, refinement (w8 n m k) (w6 n m k).
Proof. unfold w8, w6.
       intro k.
       induction k; intros.
       - simpl. apply refw4w3.
       - rewrite <- !meqDpf. rewrite DpnD3C.
         rewrite DpnD3C.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k)) w4) =
                (merge_dpf_cont (DpnD3 d3 n) (merge_dpf_cont (DpnD3 d4 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d3 n) (DpnD3 d4 m)) k) w4)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H.
         assert((merge_dpf_cont (Dpf_merge (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k)) w3) =
                (merge_dpf_cont (DpnD3 d1 n) (merge_dpf_cont (DpnD3 d2 m) (merge_dpf_cont (DpnD3 (Dpf_merge (DpnD3 d1 n) (DpnD3 d2 m)) k) w3)))).
         { rewrite !merge_mergeD. easy. }
         rewrite H0.
         apply refm2.
         apply refm1.
         specialize(IHk n m).
         rewrite <- !meqDpf in IHk. easy.
Qed.

Lemma refmG1w2w1k: forall k l,
  refinement (merge_dpf_contn (sShape l) w2 k) (merge_dpf_contn (rShape l) w1 k).
Proof. intros.
       rewrite <- !meqDpf.
       revert l.
       induction k; intros.
       - simpl. rewrite !dpfend_dn. apply refw2w1.
       - rewrite !DpnD3C !merge_mergeD.
         apply refmG1.
         easy.
Qed.

Lemma refmG1w4w3k: forall k l,
  refinement (merge_dpf_contn (sShape l) w4 k) (merge_dpf_contn (rShape l) w3 k).
Proof. intros.
       rewrite <- !meqDpf.
       revert l.
       induction k; intros.
       - simpl. rewrite !dpfend_dn. apply refw4w3.
       - rewrite !DpnD3C !merge_mergeD.
         apply refmG1.
         easy.
Qed.

Lemma st_rcp: forall (l: list bool), subtype rcop rcp.
Proof. intro l.
       unfold subtype.
       assert (singleton w2) as Hw2.
       { pcofix CIH. rewrite(st_eq w2). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w1) as Hw1.
       { pcofix CIH. rewrite(st_eq w1). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w3) as Hw3.
       { pcofix CIH. rewrite(st_eq w3). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w4) as Hw4.
       { pcofix CIH. rewrite(st_eq w4). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       exists [((mk_siso w2 Hw2),(mk_siso w1 Hw1));((mk_siso w2 Hw2),(mk_siso w1 Hw1));
               ((mk_siso w4 Hw4),(mk_siso w3 Hw3));((mk_siso w4 Hw4),(mk_siso w3 Hw3))].
       simpl.
       split. split.

       pcofix CIH. pfold.
       rewrite(st_eq w2). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd with (y := "A" & [|("add", I, rcop)|]).
       left. pfold.
       apply st2siso_rcv with (y := rcop).
       simpl. right. apply CIH.
       constructor. 
       constructor.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w1). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv with (y := "C" ! [|("add", I, rcp); ("sub", I, rcp)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := rcp). simpl.
       right. exact CIH.
       constructor.
       constructor.

       split.
       pcofix CIH. pfold.
       rewrite(st_eq w2). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd with (y := ("A" & [|("add", I, rcop)|])).
       left. pfold. simpl.
       apply st2siso_rcv with (y := rcop).
       simpl. right. apply CIH.
       constructor.
       constructor.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w1). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv with (y := "C" ! [|("add", I, rcp); ("sub", I, rcp)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := rcp). simpl.
       right. exact CIH.
       constructor.
       constructor.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w4). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd with (y :=  "A" & [|("add", I, rcop)|]). simpl.
       left. pfold.
       apply st2siso_rcv with (y := rcop). simpl.
       right. exact CIH.
       constructor.
       constructor. easy.
       constructor.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w3). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv with (y := "C" ! [|("add", I, rcp); ("sub", I, rcp)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := rcp). simpl.
       right. exact CIH.
       constructor. easy.
       constructor.
       constructor.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w4). simpl.
       rewrite(st_eq rcop). simpl.
       apply st2siso_snd with (y :=  "A" & [|("add", I, rcop)|]). simpl.
       left. pfold.
       apply st2siso_rcv with (y := rcop). simpl.
       right. exact CIH.
       constructor. 
       constructor. easy.
       constructor.

       split.
       pcofix CIH. pfold. 
       rewrite(st_eq w3). simpl.
       rewrite(st_eq rcp). simpl.
       apply st2siso_rcv with (y := "C" ! [|("add", I, rcp); ("sub", I, rcp)|]). simpl.
       left. pfold.
       apply st2siso_snd with (y := rcp). simpl.
       right. exact CIH.
       constructor. easy.
       constructor.
       constructor. easy.
       
       split.
       exists dpf_end. exists dpf_end. intro k.
       rewrite <- !meqDpf.
       rewrite dpEnd.
       rewrite !dpfend_dn.
       apply refw2w1.
       
       split.
       exists (sShape l).
       exists (rShape l).
       intro k.
       apply refmG1w2w1k.

       split.
       exists dpf_end. exists dpf_end. intro k.
       rewrite <- !meqDpf.
       rewrite dpEnd.
       rewrite !dpfend_dn.
       apply refw4w3.

       split.
       exists (sShape l).
       exists (rShape l).
       intro k.
       apply refmG1w4w3k.

       easy.
Qed.

Lemma ltB_rcp: lt2st ltB = rcp.
Proof. apply stExt.
       pcofix CIH.
       rewrite(st_eq(lt2st ltB)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                          match xs with
                          | [] => [||]
                          | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                          end)
                         [("add", I,
                           lt_send "C"
                             [("add", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
                              ("sub", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))])])).
       simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                            match xs with
                            | [] => [||]
                            | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                            end) []))).
       simpl.
       pfold.
       rewrite (st_eq rcp). simpl.
       rewrite(st_eq(lt2st
        (lt_send "C"
           [("add", I,
             lt_mu
               (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
             ("sub", I,
             lt_mu
               (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                           match xs with
                           | [] => [||]
                           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                           end)
                          [("add", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]));
                           ("sub", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                           match xs with
                           | [] => [||]
                           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                           end) [("sub", I, lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))])). simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                           match xs with
                           | [] => [||]
                           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                           end) []))). simpl.
       constructor.
       constructor.
       exists "add". exists (I). exists("C" ! [|("add", I, lt2st (lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])])));
       ("sub", I, lt2st (lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])])))|]).
       exists "add". exists (I). exists("C" ! [|("add", I, rcp); ("sub", I, rcp)|]).
       split. easy. split. easy.
       split. easy. split. easy.
       left.
       pfold.
       constructor.
       constructor.
       exists "add". exists (I). exists( lt2st (lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))).
       exists "add". exists (I). exists rcp.
       split. easy. split. easy. split. easy. split. easy.
       right.
       unfold ltB in CIH. easy.
       constructor.
       exists "sub". exists (I). exists( lt2st (lt_mu (lt_receive "A" [("add", I, lt_send "C" [("add", I, lt_var 0); ("sub", I, lt_var 0)])]))).
       exists "sub". exists (I). exists rcp.
       split. easy. split. easy. split. easy. split. easy.
       right.
       unfold ltB in CIH. easy.
       constructor.
       constructor.
Qed.

Lemma ltBop_rcop: lt2st ltBOp = rcop.
Proof. apply stExt.
       pcofix CIH.
       rewrite(st_eq(lt2st ltBOp)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                          match xs with
                          | [] => [||]
                          | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                          end)
                         [("add", I,
                           lt_receive "A"
                             [("add", I,
                               lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))]);
                          ("sub", I,
                           lt_receive "A"
                             [("add", I,
                               lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                           match xs with
                           | [] => [||]
                           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                           end)
                          [("sub", I,
                            lt_receive "A"
                              [("add", I,
                                lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])])).
       simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                            match xs with
                            | [] => [||]
                            | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                            end) []))). simpl.
       rewrite(st_eq rcop). simpl.
       pfold.
       constructor.
       constructor.
       exists "add". exists (I). exists(lt2st (lt_receive "A" [("add", I, lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])).
       exists "add". exists (I). exists("A" & [|("add", I, rcop)|]).
       split. easy. split. easy. split. easy. split. easy.
       rewrite(st_eq((lt2st (lt_receive "A" [("add", I,lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                          match xs with
                          | [] => [||]
                          | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                          end)
                         [("add", I,
                           lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])). simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                           match xs with
                           | [] => [||]
                           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                           end) []))). simpl.
       left. pfold.
       constructor.
       constructor.
       exists "add". exists (I). exists(lt2st (lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))).
       exists "add". exists (I). exists rcop.
       split. easy. split. easy. split. easy. split. easy.
       right. easy.
       constructor.
       constructor.
       exists "sub". exists (I). exists(lt2st (lt_receive "A" [("add", I, lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])).
       exists "sub". exists (I). exists("A" & [|("add", I, rcop)|]).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold.
       rewrite(st_eq((lt2st (lt_receive "A" [("add", I, lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                          match xs with
                          | [] => [||]
                          | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                          end) [("add", I, lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))])). simpl.
       rewrite(coseq_eq(((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                           match xs with
                           | [] => [||]
                           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                           end) []))). simpl.
       constructor.
       constructor.
       exists "add". exists (I). exists(lt2st (lt_mu (lt_send "C" [("add", I, lt_receive "A" [("add", I, lt_var 0)]); ("sub", I, lt_receive "A" [("add", I, lt_var 0)])]))).
       exists "add". exists (I). exists rcop.
       split. easy. split. easy. split. easy. split. easy.
       right. easy.
       constructor.
       constructor.
Qed.

Lemma st: forall (l: list bool), subltype ltBOp ltB.
Proof. unfold subltype.
       intro l.
       unfold subtype.
       assert (singleton w2) as Hw2.
       { pcofix CIH. rewrite(st_eq w2). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w1) as Hw1.
       { pcofix CIH. rewrite(st_eq w1). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w3) as Hw3.
       { pcofix CIH. rewrite(st_eq w3). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       assert (singleton w4) as Hw4.
       { pcofix CIH. rewrite(st_eq w4). simpl.
         pfold. constructor. left. pfold. constructor.
         right. exact CIH.
       }
       exists [((mk_siso w2 Hw2),(mk_siso w1 Hw1));((mk_siso w2 Hw2),(mk_siso w1 Hw1));
               ((mk_siso w4 Hw4),(mk_siso w3 Hw3));((mk_siso w4 Hw4),(mk_siso w3 Hw3))].       
       simpl.
 
       split. split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltBOp)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
        match xs with
        | [] => [||]
        | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("add", I, lt_receive "A" [("add", I, ltBOp)]); ("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "A" [("add", I, ltBOp)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltBOp)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       
       pfold.
       rewrite(st_eq w2). simpl.
       apply st2siso_snd with (y := "A" & [|("add", I, (lt2st ltBOp))|]).
       left. pfold.
       apply st2siso_rcv with (y := (lt2st ltBOp)).
       simpl. right. apply CIH.
       constructor. 
       constructor.
       
       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltB)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                match xs with
                | [] => [||]
                | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                end) [("add", I, lt_send "C" [("add", I, ltB); ("sub", I, ltB)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
         match xs with
         | [] => [||]
         | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
         end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "C" [("add", I, ltB); ("sub", I, ltB)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltB); ("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                   coseq (string * local.sort * st) :=
                 match xs with
                 | [] => [||]
                 | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                 end) [])). simpl.
       rewrite(st_eq w1). simpl.
       pfold.
       apply st2siso_rcv with (y := "C" ! [|("add", I, lt2st ltB); ("sub", I, lt2st ltB)|]).
       left. pfold.
       apply st2siso_snd with (y := (lt2st ltB)).
       simpl. right. apply CIH.
       constructor. 
       constructor.
       
       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltBOp)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
        match xs with
        | [] => [||]
        | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("add", I, lt_receive "A" [("add", I, ltBOp)]); ("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "A" [("add", I, ltBOp)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltBOp)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       pfold.
       rewrite(st_eq w2). simpl.
       apply st2siso_snd with (y := "A" & [|("add", I, (lt2st ltBOp))|]).
       left. pfold.
       apply st2siso_rcv with (y := (lt2st ltBOp)).
       simpl. right. apply CIH.
       constructor. 
       constructor.
       

       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltB)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                match xs with
                | [] => [||]
                | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                end) [("add", I, lt_send "C" [("add", I, ltB); ("sub", I, ltB)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
         match xs with
         | [] => [||]
         | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
         end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "C" [("add", I, ltB); ("sub", I, ltB)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltB); ("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                   coseq (string * local.sort * st) :=
                 match xs with
                 | [] => [||]
                 | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                 end) [])). simpl.
       rewrite(st_eq w1). simpl.
       pfold.
       apply st2siso_rcv with (y := "C" ! [|("add", I, lt2st ltB); ("sub", I, lt2st ltB)|]).
       left. pfold.
       apply st2siso_snd with (y := (lt2st ltB)).
       simpl. right. apply CIH.
       constructor. 
       constructor.
       
       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltBOp)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
        match xs with
        | [] => [||]
        | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("add", I, lt_receive "A" [("add", I, ltBOp)]); ("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "A" [("add", I, ltBOp)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltBOp)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       pfold.
       rewrite(st_eq w4). simpl.
       apply st2siso_snd with (y := "A" & [|("add", I, (lt2st ltBOp))|]).
       left. pfold.
       apply st2siso_rcv with (y := (lt2st ltBOp)).
       simpl. right. apply CIH.
       constructor. 
       constructor. easy.
       constructor.

       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltB)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                match xs with
                | [] => [||]
                | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                end) [("add", I, lt_send "C" [("add", I, ltB); ("sub", I, ltB)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
         match xs with
         | [] => [||]
         | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
         end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "C" [("add", I, ltB); ("sub", I, ltB)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltB); ("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                   coseq (string * local.sort * st) :=
                 match xs with
                 | [] => [||]
                 | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                 end) [])). simpl.
       rewrite(st_eq w3). simpl.
       pfold.
       apply st2siso_rcv with (y := "C" ! [|("add", I, lt2st ltB); ("sub", I, lt2st ltB)|]).
       left. pfold.
       apply st2siso_snd with (y := (lt2st ltB)).
       simpl. right. apply CIH.
       constructor. easy. 
       constructor.
       constructor.

       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltBOp)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
        match xs with
        | [] => [||]
        | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
        end)
       [("add", I, lt_receive "A" [("add", I, ltBOp)]); ("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("sub", I, lt_receive "A" [("add", I, ltBOp)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "A" [("add", I, ltBOp)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltBOp)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       pfold.
       rewrite(st_eq w4). simpl.
       apply st2siso_snd with (y := "A" & [|("add", I, (lt2st ltBOp))|]).
       left. pfold.
       apply st2siso_rcv with (y := (lt2st ltBOp)).
       simpl. right. apply CIH.
       constructor. 
       constructor. easy.
       constructor.

       split.
       pcofix CIH.
       rewrite(st_eq(lt2st ltB)). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
                match xs with
                | [] => [||]
                | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                end) [("add", I, lt_send "C" [("add", I, ltB); ("sub", I, ltB)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
         match xs with
         | [] => [||]
         | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
         end) [])). simpl.
       rewrite(st_eq(lt2st (lt_send "C" [("add", I, ltB); ("sub", I, ltB)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) : coseq (string * local.sort * st) :=
           match xs with
           | [] => [||]
           | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
           end) [("add", I, ltB); ("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                coseq (string * local.sort * st) :=
              match xs with
              | [] => [||]
              | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
              end) [("sub", I, ltB)])). simpl.
       rewrite(coseq_eq((cofix next (xs : seq.seq (string * local.sort * local)) :
                   coseq (string * local.sort * st) :=
                 match xs with
                 | [] => [||]
                 | ((l1, s1, t1) :: ys)%SEQ => cocons (l1, s1, lt2st t1) (next ys)
                 end) [])). simpl.
       rewrite(st_eq w3). simpl.
       pfold.
       apply st2siso_rcv with (y := "C" ! [|("add", I, lt2st ltB); ("sub", I, lt2st ltB)|]).
       left. pfold.
       apply st2siso_snd with (y := (lt2st ltB)).
       simpl. right. apply CIH.
       constructor. easy. 
       constructor.
       constructor. 
       
       easy.

       split.
       exists dpf_end. exists dpf_end. intro k.
       rewrite <- !meqDpf.
       rewrite dpEnd.
       rewrite !dpfend_dn.
       apply refw2w1.
       
       split.
       exists (sShape l).
       exists (rShape l).
       intro k.
       apply refmG1w2w1k.

       split.
       exists dpf_end. exists dpf_end. intro k.
       rewrite <- !meqDpf.
       rewrite dpEnd.
       rewrite !dpfend_dn.
       apply refw4w3.

       split.
       exists (sShape l).
       exists (rShape l).
       intro k.
       apply refmG1w4w3k.

       easy.
Qed.


