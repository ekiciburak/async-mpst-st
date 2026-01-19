Require Import ST.src.stream ST.processes.process ST.src.st ST.src.so ST.src.si ST.src.reordering ST.src.siso ST.src.nondepro ST.types.local
               ST.subtyping.refinement ST.src.reorderingfacts ST.subtyping.subtyping.
From Stdlib Require Import Lia.
From Paco Require Import paco.
From Stdlib Require Import String List.
Import ListNotations.
Import CoListNotations.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.

Local Open Scope string_scope.

Definition ltype1: local := lt_send "p" [("l1",I,lt_receive "q" [("l3",I,lt_end);("l4",I,lt_end)])].

Definition ltype2: local := lt_send "p" [("l1",I,lt_receive "q" [("l3",I,lt_end)]);("l2",I,lt_end)].

Definition type1: st := st_send "p" [|("l1",I,st_receive "q" [|("l3",I,st_end);("l4",I,end)|])|].

Definition type2: st := st_send "p" [|("l1",I,st_receive "q" [|("l3",I,st_end)|]);("l2",I,end)|].

Definition dec12 := st_send "p" [|("l1",I,st_receive "q" [|("l3",I,end)|])|].

Lemma singl12: singleton dec12.
Proof. pfold.
       constructor. 
       left. pfold. constructor.
       left. pfold. constructor.
Qed.

Lemma act_eqt1t21:
exists L1 L2 : list (participant * dir),
  coseqInLC (act (end)) L1 /\
  coseqInLC (act (end)) L2 /\
  coseqInR L1 (act (end)) /\ coseqInR L2 (act (end)) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists nil.
       exists nil.
       split. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. constructor.
       split. constructor.
       easy.
Qed.

Lemma act_eqt1t22:
exists L1 L2 : list (participant * dir),
  coseqInLC (act ("q" & [|("l3", I, end)|])) L1 /\
  coseqInLC (act ("q" & [|("l3", I, end)|])) L2 /\
  coseqInR L1 (act ("q" & [|("l3", I, end)|])) /\
  coseqInR L2 (act ("q" & [|("l3", I, end)|])) /\ (forall x : participant * dir, In x L1 <-> In x L2).
Proof. exists [("q",rcv)].
       exists [("q",rcv)].
       split. rewrite(coseq_eq(act ("q" & [|("l3", I, end)|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. rewrite(coseq_eq(act ("q" & [|("l3", I, end)|]))). unfold coseq_id. simpl.
       pfold. constructor. simpl. left. easy.
       left. pfold. rewrite(coseq_eq(act (end))).
       unfold coseq_id. simpl. constructor.
       split. constructor. rewrite(coseq_eq(act ("q" & [|("l3", I, end)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("q", rcv)) (ys := (act (end))). simpl. easy. easy.
       constructor.
       split. constructor. rewrite(coseq_eq(act ("q" & [|("l3", I, end)|]))). unfold coseq_id. simpl.
       apply CoInSplit1 with (y := ("q", rcv)) (ys := (act (end))). simpl. easy. easy.
       constructor.
       easy.
Qed.

Lemma subtypet1t2: subtype type1 type2.
Proof. unfold subtype.
       exists [(mk_siso dec12 singl12, mk_siso dec12 singl12)].
       split.
       - simpl. split.
         + pfold.
           rewrite(st_eq(dec12)). simpl.
           rewrite(st_eq(type1)). simpl.
           apply st2siso_snd with (y := "q" & [|("l3", I, end); ("l4", I, end)|]).
           left. pfold.
           apply st2siso_rcv with (y := end). left. pfold. constructor.
           constructor.
           constructor.
           split.
           rewrite(st_eq(dec12)). simpl.
           rewrite(st_eq(type2)). simpl.
           pfold.
           apply st2siso_snd with (y := "q" & [|("l3", I, end)|]).
           left. pfold.
           apply st2siso_rcv with (y := end). left. pfold. constructor.
           constructor.
           constructor. easy.
       - simpl. split. exists dpf_end. exists dpf_end.
         intro n.
         rewrite <- !meqDpf.
         rewrite !dpEnd.
         rewrite !dpfend_dn.

         pfold. rewrite(st_eq(dec12)). simpl.
         specialize(ref_b (upaco2 refinementR bot2)
                          ("q" & [|("l3", I, end)|])
                          ("q" & [|("l3", I, end)|])
                          "p" "l1" (I) (I) (bp_end) 1
         ); intro Hb.
         simpl in Hb. rewrite !bpend_an in Hb.
         apply Hb; clear Hb.
         constructor.

         left. pfold.
         specialize(ref_a (upaco2 refinementR bot2)
                          (end)
                          (end)
                          "q" "l3" (I) (I) (ap_end) 1
         ); intro Ha.
         simpl in Ha. rewrite !apend_an in Ha.
         apply Ha; clear Ha.
         constructor.
         left. pfold. constructor.
         apply act_eqt1t21.
         apply act_eqt1t22.
         easy.
Qed.

Lemma lt1t1: lt2st ltype1 = type1.
Proof. apply stExt.
       pfold. unfold ltype1.
       rewrite(st_eq type1). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l1", I, lt_receive "q" [("l3", I, lt_end); ("l4", I, lt_end)])]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end) [("l1", I, lt_receive "q" [("l3", I, lt_end); ("l4", I, lt_end)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "q" [("l3", I, lt_end); ("l4", I, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_end); ("l4", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [("l4", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                 match xs with
                 | [] => [||]
                 | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                 end) [])). simpl.
       rewrite(st_eq(lt2st lt_end)). simpl.
       constructor.
       pfold.
       constructor.
       exists "l1". exists (I). exists("q" & [|("l3", I, end); ("l4", I, end)|]).
       exists "l1". exists (I). exists("q" & [|("l3", I, end); ("l4", I, end)|]).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       pfold.
       constructor.
       exists "l3". exists (I). exists(end).
       exists "l3". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       left. pfold.
       constructor.
       exists "l4". exists (I). exists(end).
       exists "l4". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       pfold.
       constructor.
       left. pfold. constructor.
Qed.

Lemma lt2t2: lt2st ltype2 = type2.
Proof. apply stExt.
       pfold. unfold ltype2.
       rewrite(st_eq type2). simpl.
       rewrite(st_eq(lt2st (lt_send "p" [("l1", I, lt_receive "q" [("l3", I, lt_end)]); ("l2", I, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end) [("l1", I, lt_receive "q" [("l3", I, lt_end)]); ("l2", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l2", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "q" [("l3", I, lt_end)]))). simpl.
       rewrite(st_eq(lt2st lt_end)). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st lt_end)). simpl.
       constructor.
       pfold.
       constructor.
       exists "l1". exists (I). exists("q" & [|("l3", I, end)|]).
       exists "l1". exists (I). exists("q" & [|("l3", I, end)|]).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       pfold.
       constructor.
       exists "l3". exists (I). exists(end).
       exists "l3". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       pfold.
       constructor.
       left. pfold. constructor.
       exists "l2". exists (I). exists(end).
       exists "l2". exists (I). exists(end).
       split. easy. split. easy. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       pfold. constructor.
Qed.

Lemma lT1_lT2: subltype ltype1 ltype2.
Proof. unfold subltype.
       unfold subtype.
       exists [(mk_siso dec12 singl12, mk_siso dec12 singl12)].
       simpl.
       split.
       split.
       pcofix CIH. pfold.
       unfold dec12. rewrite(st_eq(lt2st ltype1)). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end) [("l1", I, lt_receive "q" [("l3", I, lt_end); ("l4", I, lt_end)])])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "q" [("l3", I, lt_end); ("l4", I, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_end); ("l4", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [("l4", I, lt_end)])). simpl.
       rewrite(coseq_eq ((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
                 match xs with
                 | [] => [||]
                 | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
                 end) [])). simpl.
       rewrite(st_eq(lt2st lt_end)). simpl.
       apply st2siso_snd with (y := "q" & [|("l3", I, end); ("l4", I, end)|]).
       left. pfold.
       apply st2siso_rcv with (y := end). left. pfold. constructor.
       constructor.
       constructor.
       split.
       unfold dec12. rewrite(st_eq(lt2st ltype2)). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
        match xs with
        | [] => [||]
        | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
        end) [("l1", I, lt_receive "q" [("l3", I, lt_end)]); ("l2", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l2", I, lt_end)])). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) [])). simpl.
       rewrite(st_eq(lt2st (lt_receive "q" [("l3", I, lt_end)]))). simpl.
       rewrite(coseq_eq((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
           match xs with
           | [] => [||]
           | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
           end) [("l3", I, lt_end)])). simpl.
       rewrite(coseq_eq(((cofix next (xs : list (string * sort * local)) : coseq (string * sort * st) :=
              match xs with
              | [] => [||]
              | (l1, s1, t1) :: ys => cocons (l1, s1, lt2st t1) (next ys)
              end) []))). simpl.
       rewrite(st_eq(lt2st lt_end)). simpl.
       pfold.
       apply st2siso_snd with (y := "q" & [|("l3", I, end)|]).
       left. pfold.
       apply st2siso_rcv with (y := end). left. pfold. constructor.
       constructor.
       constructor.
       easy.
       
       split. exists dpf_end. exists dpf_end.
       intro n.
       rewrite <- !meqDpf.
       rewrite !dpEnd.
       rewrite !dpfend_dn.

       pfold. rewrite(st_eq(dec12)). simpl.
       specialize(ref_b (upaco2 refinementR bot2)
                        ("q" & [|("l3", I, end)|])
                        ("q" & [|("l3", I, end)|])
                        "p" "l1" (I) (I) (bp_end) 1
       ); intro Hb.
       simpl in Hb. rewrite !bpend_an in Hb.
       apply Hb; clear Hb.
       constructor.

       left. pfold.
       specialize(ref_a (upaco2 refinementR bot2)
                        (end)
                        (end)
                        "q" "l3" (I) (I) (ap_end) 1
       ); intro Ha.
       simpl in Ha. rewrite !apend_an in Ha.
       apply Ha; clear Ha.
       constructor.
       left. pfold. constructor.
       apply act_eqt1t21.
       apply act_eqt1t22.
       easy.
Qed.


