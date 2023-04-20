Require Export Denotations.
Require Import RTClosure.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Setoids.Setoid.

(*******************************************)
(************* Small Step ******************)
(*******************************************)

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : State -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum ((fst st) X))
  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2)).

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : State -> bexp -> bexp -> Prop :=
  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.

Section cstep.

Local Open Scope imp.

Inductive cstep : (com * State) -> list Z -> (com * State) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (X ::= a, st) [] (X ::= a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 = ((X  !-> n, (fst st1)) , snd st1) ->
      cstep (X ::= (ANum n), st1) [] (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2 l,
      cstep (c1, st) l (c1', st') ->
      cstep (c1 ;; c2 , st) l (c1' ;; c2, st')
  | CS_Seq : forall st c2,
      cstep (Skip ;; c2, st) [] (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st) []
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) [] (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) [] (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st) []
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st)
  | CS_Unit_SG : forall st1 st2 U q,
      st2 = ((fst st1),  ((u_1 U q) # (snd st1))) ->
      cstep (Unit_SG U q, st1) [] (Skip, st2)
  | CS_Unit_DB : forall st1 st2 U p q,
      st2 = ((fst st1), ((u_2 U q p) # (snd st1))) ->
      cstep (Unit_DB U q p, st1) [] (Skip, st2)
  | CS_Meas : forall st1 st2 l x q,
       (st2 = ((x !-> 0, (fst st1)), ((Mea0 q) # (snd st1))) /\ l = [0]) \/
       (st2 = ((x !-> 1, (fst st1)), ((Mea1 q) # (snd st1))) /\ l = [1]) ->
       cstep (Meas x q, st1) l (Skip, st2).

End cstep.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Inductive clos_refl_trans' (RE : com * State -> list Z -> com * State -> Prop) : com * State -> list Z -> com * State -> Prop :=
  | rt_step' : forall x l y, RE x l y -> clos_refl_trans' RE x l y
  | rt_refl' : forall x,  clos_refl_trans' RE x []  x
  | rt_trans' : forall x y z l1 l2, clos_refl_trans' RE x l1 y ->
                                              clos_refl_trans' RE y l2 z ->
                                              clos_refl_trans' RE x (l1++l2) z.

Inductive clos_refl_trans_1n' (RE : com * State -> list Z -> com * State -> Prop) : com * State -> list Z -> com * State -> Prop :=
    | rt1n_refl' : forall x, clos_refl_trans_1n' RE x [] x
    | rt1n_trans_1n' : forall x y z l1 l2,
          RE x l1 y ->
          clos_refl_trans_1n' RE y l2 z ->
          clos_refl_trans_1n' RE x (l1++l2) z.

Inductive clos_refl_trans_n1' (RE : com * State -> list Z -> com * State -> Prop) : com * State -> list Z -> com * State -> Prop :=
    | rtn1_refl' : forall x, clos_refl_trans_n1' RE x [] x
    | rtn1_trans_n1' : forall x y z l1 l2,
          RE y l2 z ->
          clos_refl_trans_n1' RE x l1 y ->
          clos_refl_trans_n1' RE x (l1++l2) z.


Lemma rt_trans_1n': forall (RE : com * State -> list Z -> com * State -> Prop) x y z l1 l2,
  RE x l1 y ->
  clos_refl_trans' RE y l2 z ->
  clos_refl_trans' RE x (l1++l2) z.
Proof.
  intros.
  eapply rt_trans' with y; [| exact H0].
  apply rt_step'.
  exact H.
Qed.

Lemma rt_trans_n1': forall (RE : com * State -> list Z -> com * State -> Prop) x y z l1 l2,
  RE y l2 z ->
  clos_refl_trans' RE x l1 y ->
  clos_refl_trans' RE x (l1 ++ l2) z.
Proof.
  intros.
  eapply rt_trans' with y; [exact H0 |].
  apply rt_step'.
  exact H.
Qed.

Lemma rt1n_step': forall (RE : com * State -> list Z -> com * State -> Prop) x y l,
  RE x l y ->
  clos_refl_trans_1n' RE x l y.
Proof.
  intros.
  pose proof rt1n_trans_1n' RE x y y l [] H.
  rewrite app_nil_r in H0.
  apply H0.
  apply rt1n_refl'.
Qed.

Lemma rtn1_step': forall (RE : com * State -> list Z -> com * State -> Prop) x y l,
  RE x l y ->
  clos_refl_trans_n1' RE x l y.
Proof.
  intros.
  pose proof rtn1_trans_n1' RE x x y [] l H.
  rewrite app_nil_l in H0.
  apply H0.
  apply rtn1_refl'.
Qed.

Lemma rt1n_trans': forall (RE : com * State -> list Z -> com * State -> Prop) a b c l1 l2,
  clos_refl_trans_1n' RE a l1 b ->
  clos_refl_trans_1n' RE b l2 c ->
  clos_refl_trans_1n' RE a (l1 ++ l2) c.
Proof.
  intros.
  revert H0.
  induction H.
  + rewrite app_nil_l. auto.
  + intros.
     rewrite <- app_assoc.
     apply rt1n_trans_1n' with y; tauto.
Qed.

Lemma rtn1_trans': forall (RE : com * State -> list Z -> com * State -> Prop) a b c l1 l2,
  clos_refl_trans_n1' RE a l1 b  ->
  clos_refl_trans_n1' RE b l2 c  ->
  clos_refl_trans_n1' RE a (l1++l2) c .
Proof.
  intros.
  induction H0.
  + rewrite app_nil_r. auto.
  + rewrite app_assoc.
      apply rtn1_trans_n1' with y; tauto.
Qed.

Lemma rt1n_rt': forall (RE : com * State -> list Z -> com * State -> Prop) a b l,
  clos_refl_trans_1n' RE a l b -> clos_refl_trans' RE a l b.
Proof.
  intros.
  induction H.
  + apply rt_refl'.
  + apply rt_trans_1n' with y; tauto.
Qed.

Lemma rt_rt1n': forall (RE : com * State -> list Z -> com * State -> Prop) a b l,
  clos_refl_trans' RE a l b -> clos_refl_trans_1n' RE a l b.
Proof.
  intros.
  induction H.
  + apply rt1n_step', H.
  + apply rt1n_refl'.
  + apply rt1n_trans' with y; tauto.
Qed.

Lemma rtn1_rt': forall (RE : com * State -> list Z -> com * State -> Prop) a b l,
  clos_refl_trans_n1' RE a l b -> clos_refl_trans' RE a l b.
Proof.
  intros.
  induction H.
  + apply rt_refl'.
  + apply rt_trans_n1' with y; tauto.
Qed.

Lemma rt_rtn1': forall (RE : com * State -> list Z -> com * State -> Prop) a b l,
  clos_refl_trans' RE a l b -> clos_refl_trans_n1' RE a l b.
Proof.
  intros.
  induction H.
  + apply rtn1_step', H.
  + apply rtn1_refl'.
  + apply rtn1_trans' with y; tauto.
Qed.

Lemma rt_rt1n_iff': forall (RE : com * State -> list Z -> com * State -> Prop) a b l,
  clos_refl_trans' RE a l b <-> clos_refl_trans_1n' RE a l b.
Proof.
  split; intros.
  + apply rt_rt1n'; auto.
  + apply rt1n_rt'; auto.
Qed.

Lemma rt_rtn1_iff': forall (RE : com * State -> list Z -> com * State -> Prop) a b l,
  clos_refl_trans' RE a l b <-> clos_refl_trans_n1' RE a l b.
Proof.
  split; intros.
  + apply rt_rtn1'; auto.
  + apply rtn1_rt'; auto.
Qed.

Lemma trans_1N': forall (RE RT_R: com * State -> list Z -> com * State -> Prop) l1 l2,
  (RT_R = clos_refl_trans' RE) ->
  forall x y z, RE x l1 y -> RT_R y l2 z -> RT_R x (l1++l2) z.
Proof.
  intros.
  subst.
  apply rt_trans_1n' with y; auto.
Qed.

Lemma trans_N1': forall (RE RT_R: com * State -> list Z -> com * State -> Prop) l1 l2,
  (RT_R = clos_refl_trans' RE) ->
  forall x y z, RT_R x l1 y -> RE y l2 z -> RT_R x (l1++l2) z.
Proof.
  intros.
  subst.
  apply rt_trans_n1' with y; auto.
Qed.

Definition multi_astep (st: State): aexp -> aexp -> Prop := clos_refl_trans (astep st).

Definition multi_bstep (st: State): bexp -> bexp -> Prop := clos_refl_trans (bstep st).

Definition multi_cstep: com * State -> list Z -> com * State -> Prop := clos_refl_trans' cstep.

(*******************************************)
(***** Denotations vs Small Step ***********)
(*******************************************)

Section DenotationSmallStep.

Local Open Scope imp.

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus1.
      exact H.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult1.
      exact H.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult2.
      * exact H.
      * exact H0.
Qed.


Theorem multi_congr_BEq1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 == a2) (a1' == a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq1.
      exact H.
Qed.

Theorem multi_congr_BEq2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 == a2) (a1 == a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BLe1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 <= a2) (a1' <= a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le1.
      exact H.
Qed.

Theorem multi_congr_BLe2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 <= a2) (a1 <= a2').
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BNot: forall st b b',
  multi_bstep st b b' ->
  multi_bstep st (BNot b) (BNot b').
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_NotStep.
      exact H.
Qed.

Theorem multi_congr_BAnd: forall st b1 b1' b2,
  multi_bstep st b1 b1' ->
  multi_bstep st (BAnd b1 b2) (BAnd b1' b2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_AndStep.
      exact H.
Qed.

Theorem multi_congr_CAss: forall st X a a',
  multi_astep st a a' ->
  multi_cstep (CAss X a, st) [] (CAss X a', st).
Proof.
  intros.
  induction_n1 H.
  + apply rt_refl'.
  + pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
  (CAss X a, st) (CAss X a', st) (CAss X a'0, st) IHrt.
  rewrite app_nil_l in H1. apply H1. apply CS_AssStep. auto.
Qed.

Theorem multi_congr_CSeq: forall st1 c1 st1' c1' c2 l,
  multi_cstep (c1, st1) l (c1', st1') ->
  multi_cstep (CSeq c1 c2, st1) l (CSeq c1' c2, st1').
Proof.
  intros.
  unfold multi_cstep in *.
  rewrite rt_rtn1_iff' in *.
  remember (c1, st1) as cs1 eqn:H1.
  remember (c1', st1') as cs1' eqn:H2.
  revert c1 st1 c1' st1' H1 H2.
  induction H.
  + intros. subst. inversion H2. subst.
     apply rtn1_refl'.
  + intros. destruct y as [c1'' st1'']. subst.
      pose proof rtn1_trans_n1' cstep  (c1;; c2, st1) (c1'' ;; c2 , st1'') (c1';; c2, st1') l1 l2.
      specialize (IHclos_refl_trans_n1' c1 st1 c1'' st1'' (ltac:(reflexivity)) (ltac:(reflexivity))).
      apply H1. - apply CS_SeqStep. auto. - auto.
Qed.

Theorem multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (CIf b c1 c2, st) []
    (CIf b' c1 c2, st).
Proof.
  intros.
  induction_n1 H.
  + apply rt_refl'.
  + pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
  (If b Then c1 Else c2 EndIf, st) (If b' Then c1 Else c2 EndIf, st) (If b'0 Then c1 Else c2 EndIf, st) IHrt.
  rewrite app_nil_l in H1. apply H1. apply CS_IfStep. auto.
Qed.

Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + unfold constant_func in H.
    rewrite H.
    reflexivity.
  + rewrite <- H.
    etransitivity_n1; [reflexivity |].
    apply AS_Id.
  + etransitivity.
    { apply multi_congr_APlus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_APlus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Plus.
  + etransitivity.
    { apply multi_congr_AMinus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMinus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Minus.
  + etransitivity.
    { apply multi_congr_AMult1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMult2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Mult.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      reflexivity.
    - unfold Sets.full.
      tauto.
  + split.
    - unfold Sets.empty.
      tauto.
    - intros.
      reflexivity.
  + assert (multi_bstep st (a1 == a2) (aeval a1 st == aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BEq1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BEq2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_eq; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Eq_True, H0.
    - apply BS_Eq_False, H0.
  + assert (multi_bstep st (a1 <= a2) (aeval a1 st <= aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BLe1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BLe2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_le; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Le_True, H0.
    - apply BS_Le_False.
      lia.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH2.
        unfold Sets.complement in H; exact H.
      * apply BS_NotFalse.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH1.
        unfold Sets.complement in H; tauto.
      * apply BS_NotTrue.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - assert (multi_bstep st (b1 && b2) b2).
      {
        etransitivity_n1.
        * apply multi_congr_BAnd, IHb11, H.
        * apply BS_AndTrue.
      }
      split; unfold Sets.intersect; intros;
      (etransitivity; [exact H0 |]).
      * apply IHb21; tauto.
      * apply IHb22; tauto.
    - split; unfold Sets.intersect; intros; [ tauto |].
      etransitivity_n1.
      * apply multi_congr_BAnd, IHb12, H.
      * apply BS_AndFalse.
Qed.

 Corollary semantic_equiv_bexp1_true: forall st b,
  beval b st -> multi_bstep st b BTrue.
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.
  
Corollary semantic_equiv_bexp1_false: forall st b,
  (Sets.complement (beval b) st -> multi_bstep st b BFalse).
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c l,
  (forall st1 st2 l', ceval c st1 l' st2 -> multi_cstep (c, st1) l' (Skip, st2)) ->
  iter_loop_body b (ceval c) n st1 l st2 ->
  multi_cstep (While b Do c EndWhile, st1) l (Skip, st2).
Proof.
  intros. unfold multi_cstep.
  revert st1 st2 l H0. induction n; intros.
  + simpl in H0.
    unfold TerRel.test_rel in H0.
    destruct H0 as [? [? ?]]. subst st2. subst.
    pose proof trans_1N' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
     (While b Do c EndWhile, st1) (If b Then c;; While b Do c EndWhile Else Skip EndIf, st1) (Skip, st1). 
     rewrite app_nil_l in H0. apply H0. apply CS_While.
    pose proof rt_trans' cstep (If b Then c;; While b Do c EndWhile Else Skip EndIf, st1)
     (If BFalse Then c;; While b Do c EndWhile Else Skip EndIf, st1) (Skip, st1) [] [].
      rewrite app_nil_l in H2. apply H2. apply multi_congr_CIf, semantic_equiv_bexp1_false, H1.
    pose proof trans_1N' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
     (If BFalse Then c;; While b Do c EndWhile Else Skip EndIf, st1) (Skip, st1) (Skip, st1). 
      rewrite app_nil_r in H3. apply H3. apply CS_IfFalse. apply rt_refl'.
  + simpl in H0.
    unfold TerRel.concat at 1,
           TerRel.test_rel in H0.
    destruct H0 as [st [l1 [l2 [[? [? ?]] [? ?]]]]]. subst st l1.
    unfold TerRel.concat in H3.
    destruct H3 as [st1' [l1 [l3 [? [? ?]]]]].
    pose proof trans_1N' cstep (clos_refl_trans' cstep) [] l (ltac:(reflexivity))
     (While b Do c EndWhile, st1) (If b Then c;; While b Do c EndWhile Else Skip EndIf, st1) (Skip, st2). 
     rewrite app_nil_l in H5. apply H5. apply CS_While.
    pose proof rt_trans' cstep (If b Then c;; While b Do c EndWhile Else Skip EndIf, st1)
     (If BTrue Then c;; While b Do c EndWhile Else Skip EndIf, st1) (Skip, st2) [] l.
      rewrite app_nil_l in H6. apply H6. apply multi_congr_CIf, semantic_equiv_bexp1_true, H1.
    pose proof trans_1N' cstep (clos_refl_trans' cstep) [] l (ltac:(reflexivity))
     (If BTrue Then c;; While b Do c EndWhile Else Skip EndIf, st1) (c;; While b Do c EndWhile, st1) (Skip, st2).
      rewrite app_nil_l in H7. apply H7. apply CS_IfTrue.
    pose proof rt_trans' cstep (c;; While b Do c EndWhile, st1) (Skip;; While b Do c EndWhile, st1') (Skip, st2) l1 l3.
    subst l2. rewrite app_nil_l in H4. rewrite H4.
      apply H8. apply multi_congr_CSeq. apply H. apply H0.
    pose proof trans_1N' cstep (clos_refl_trans' cstep) [] l3 (ltac:(reflexivity))
     (Skip;; While b Do c EndWhile, st1') (While b Do c EndWhile, st1') (Skip, st2).
      rewrite app_nil_l in H3. apply H3.  apply CS_Seq. apply IHn. apply H2.
Qed.

Theorem semantic_equiv_com1: forall st1 st2 c,
  forall l, ceval c st1 l st2 -> multi_cstep (c, st1) l (Skip, st2).
Proof.
  intros.
  revert st1 st2 l H; induction c; intros.
  + rewrite ceval_CSkip in H.
    unfold TerRel.id in H. destruct H as [? ?].
    subst. apply rt_refl'.
  + rewrite ceval_CAss in H.
      destruct H as [? ?]. subst.
      pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
        (CAss X a, st1) ( CAss X (aeval a st1), st1) (Skip, (X !-> aeval a st1, fst st1, snd st1)).
      rewrite app_nil_r in H. apply H.
      - apply (multi_congr_CAss st1). apply (semantic_equiv_aexp1). auto.
      - apply CS_Ass. auto.
  + rewrite ceval_CSeq in H.
    unfold TerRel.concat in H.
    destruct H as [st' [l1 [l2 [? [? ?]]]]].
    pose proof rt_trans' cstep (c1;; c2, st1) (Skip;; c2, st') (Skip, st2) l1 l2.
    rewrite H1. apply H2. apply multi_congr_CSeq. apply IHc1. apply H.
    pose proof trans_1N' cstep (clos_refl_trans' cstep) [] l2 (ltac:(reflexivity)) (Skip;; c2, st') (c2, st') (Skip, st2).
    rewrite app_nil_l in H3.
    apply H3. apply CS_Seq. apply IHc2. apply H0.
  + rewrite ceval_CIf in H.
    unfold if_sem in H.
    unfold TerRel.union,
           TerRel.concat,
           TerRel.test_rel in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H];
    destruct H as [st [l1 [l2 [[? [? ?]] [? ?]]]]];
    subst st l1; rewrite app_nil_l in H5; subst l2.
    - pose proof rt_trans' cstep (If b Then c1 Else c2 EndIf, st1) (If BTrue Then c1 Else c2 EndIf, st1) (Skip, st2) [] l.
     rewrite app_nil_l in H. apply H. apply multi_congr_CIf. apply H0. apply H2.
     pose proof trans_1N' cstep (clos_refl_trans' cstep) [] l (ltac:(reflexivity))
      (If BTrue Then c1 Else c2 EndIf, st1) (c1, st1) (Skip, st2).
     rewrite app_nil_l in H3. apply H3. apply CS_IfTrue. apply IHc1. apply H4.
    - pose proof rt_trans' cstep (If b Then c1 Else c2 EndIf, st1) (If BFalse Then c1 Else c2 EndIf, st1) (Skip, st2) [] l.
     rewrite app_nil_l in H. apply H. apply multi_congr_CIf. apply H1. apply H2.
     pose proof trans_1N' cstep (clos_refl_trans' cstep) [] l (ltac:(reflexivity))
      (If BFalse Then c1 Else c2 EndIf, st1) (c2, st1) (Skip, st2).
     rewrite app_nil_l in H3. apply H3. apply CS_IfFalse. apply IHc2. apply H4.
  + rewrite ceval_CWhile in H.
    unfold loop_sem in H.
    unfold TerRel.omega_union in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - apply IHc. - apply H.
  + rewrite ceval_Unit_SG in H.
      destruct H as [? ?]. subst.
      pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
      (Unit_SG U Q, st1) (Unit_SG U Q, st1) (Skip, (fst st1, u_1 U Q # snd st1)). rewrite app_nil_l in H. apply H.
    - apply rt_refl'.
    - apply CS_Unit_SG; tauto.
  + rewrite ceval_Unit_DB in H.
      destruct H as [? ?]. subst.
      pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [] (ltac:(reflexivity))
      (Unit_DB U Q P, st1) (Unit_DB U Q P, st1) (Skip, (fst st1, u_2 U Q P # snd st1)). rewrite app_nil_l in H. apply H.
    - apply rt_refl'.
    - apply CS_Unit_DB; tauto.
  + rewrite ceval_Meas in H.
      destruct H as [H|H]; destruct H as [? ?]; subst.
      - pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [0] (ltac:(reflexivity))
      (Meas X Q, st1) (Meas X Q, st1) (Skip, (X !-> 0, fst st1, Mea0 Q # snd st1)). rewrite app_nil_l in H. apply H.
      * apply rt_refl'. * apply CS_Meas. tauto.
      - pose proof trans_N1' cstep (clos_refl_trans' cstep) [] [1] (ltac:(reflexivity))
      (Meas X Q, st1) (Meas X Q, st1) (Skip, (X !-> 1, fst st1, Mea1 Q # snd st1)). rewrite app_nil_l in H. apply H.
      * apply rt_refl'. * apply CS_Meas. tauto.
Qed.

Local Open Scope Z.
Local Close Scope imp.

Lemma ANum_halt: forall st n a,
  multi_astep st (ANum n) a ->
  a = ANum n.
Proof.
  unfold_with_1n multi_astep.
  intros.
  inversion H; subst.
  + reflexivity.
  + inversion H0.
Qed.

Lemma APlus_path_spec: forall st a1 a2 n,
  multi_astep st (APlus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 + n2).
Proof.
  intros.
  remember (APlus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma AMinus_path_spec: forall st a1 a2 n,
  multi_astep st (AMinus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 - n2).
Proof.
  intros.
  remember (AMinus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma AMult_path_spec: forall st a1 a2 n,
  multi_astep st (AMult a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 * n2).
Proof.
  intros.
  remember (AMult a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.


Theorem semantic_equiv_aexp2: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  revert n H; induction a; intros; simpl.
  + apply ANum_halt in H.
    injection H as ?H.
    rewrite H.
    reflexivity.
  + unfold_with_1n multi_astep in H.
    inversion H; subst.
    inversion H0; subst.
    inversion H1; subst.
    - reflexivity.
    - inversion H2.
  + apply APlus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.add; lia.
  + apply AMinus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.sub; lia.
  + apply AMult_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.mul; nia.
Qed.


Lemma never_BFalse_to_BTrue: forall st,
  multi_bstep st BFalse BTrue -> False.
Proof.
  unfold_with_1n multi_bstep.
  intros.
  inversion H; subst.
  inversion H0.
Qed.

Lemma never_BTrue_to_BFalse: forall st,
  multi_bstep st BTrue BFalse -> False.
Proof.
  unfold_with_1n multi_bstep.
  intros.
  inversion H; subst.
  inversion H0.
Qed.

Lemma BEq_True_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 = n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      exists n2, n2.
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BEq_False_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <> n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
Qed.

Lemma BLe_True_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <= n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BLe_False_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 > n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
Qed.

Lemma BNot_True_path_spec: forall st b,
  multi_bstep st (BNot b) BTrue ->
  multi_bstep st b BFalse.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BTrue as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      etransitivity_1n; eassumption.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
    - reflexivity.
Qed.

Lemma BNot_False_path_spec: forall st b,
  multi_bstep st (BNot b) BFalse ->
  multi_bstep st b BTrue.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BFalse as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      etransitivity_1n; eassumption.
    - reflexivity.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
Qed.

Lemma BAnd_True_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BTrue ->
  multi_bstep st b1 BTrue /\
  multi_bstep st b2 BTrue.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BTrue as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt.
      assert (multi_bstep st b1 BTrue). { etransitivity_1n; eassumption. }
      tauto.
    - split.
      * reflexivity.
      * exact H0.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BAnd_False_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BFalse ->
  multi_bstep st b1 BFalse \/
  multi_bstep st b2 BFalse.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BFalse as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt.
      * assert (multi_bstep st b1 BFalse). { etransitivity_1n; eassumption. }
        tauto.
      * tauto.
    - right.
      exact H0.
    - left.
      reflexivity.
Qed.

Theorem semantic_equiv_bexp2: forall st b,
  (multi_bstep st b BTrue -> beval b st) /\
  (multi_bstep st b BFalse -> ~ beval b st).
Proof.
  intros.
  induction b; simpl.
  + split; intros.
    -  exact Logic.I.
    - apply never_BTrue_to_BFalse in H.
      destruct H.
  + split; intros.
    - apply never_BFalse_to_BTrue in H.
      destruct H.
    - tauto.
  + split; intros.
    - apply BEq_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_eq; lia.
    - apply BEq_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_eq; lia.
  + split; intros.
    - apply BLe_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_le; lia.
    - apply BLe_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_le; lia.
  + destruct IHb as [IHb1 IHb2].
    split; intros.
    - apply BNot_True_path_spec in H.
      unfold Sets.complement; tauto.
    - apply BNot_False_path_spec in H.
      unfold Sets.complement; tauto.
  + split; intros.
    - apply BAnd_True_path_spec in H.
      unfold Sets.intersect; tauto.
    - apply BAnd_False_path_spec in H.
      unfold Sets.intersect; tauto.
Qed.

Lemma CSkip_halt: forall st st' c l,
  multi_cstep (CSkip, st) l (c, st') ->
  c = CSkip /\ st = st' /\ l = [].
Proof.
  unfold multi_cstep.
  intros.
  rewrite rt_rt1n_iff' in H.
  inversion H; subst.
  + split. auto. auto.
  + inversion H0.
Qed.

Lemma CAss_path_spec: forall X a st1 st2 l,
  multi_cstep (CAss X a, st1) l (CSkip, st2) ->
  exists n,
  multi_astep st1 a (ANum n) /\
  st2 = ((X  !-> n, (fst st1)) , snd st1) /\ l=[].
Proof.
  intros.
  remember (CAss X a, st1) as c eqn:H0.
  remember (CSkip, st2) as c' eqn:H1.
  revert a H0 H1. unfold multi_cstep in *.
  rewrite rt_rt1n_iff' in H.
   induction H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHclos_refl_trans_1n' _ ltac:(reflexivity) ltac:(reflexivity)).
     destruct IHclos_refl_trans_1n' as [n [? ?]].
      exists n.
      assert (multi_astep st1 a n). { etransitivity_1n; eassumption. }
      firstorder.
    - clear IHclos_refl_trans_1n'.
      rewrite <- rt_rt1n_iff' in H0.
      apply CSkip_halt in H0.
      destruct H0 as [? [? ?]].
      exists n. firstorder. reflexivity.
Qed.

Lemma CSeq_path_spec: forall c1 st1 c2 st3 l,
  multi_cstep (CSeq c1 c2, st1) l (CSkip, st3) ->
  exists st2 l1 l2, l=l1++l2/\
  multi_cstep (c1, st1) l1 (CSkip, st2) /\
  multi_cstep (c2, st2) l2 (CSkip, st3).
Proof.
  intros.
  remember ((c1;; c2)%imp, st1) as cs eqn:H2.
  remember (Skip%imp, st3) as cs' eqn:H3.
  revert c1 c2 st1 st3 H2 H3.
  unfold multi_cstep in H.
  rewrite rt_rt1n_iff' in H.
  induction H; intros; subst.
  + inversion H3.
  + inversion H; subst.
    - specialize (IHclos_refl_trans_1n' _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHclos_refl_trans_1n' as [st2 [l3 [l4 [? [? ?]]]]].
      exists st2,(l1++l3),l4. subst. split. rewrite app_assoc. auto. split.
      pose proof trans_1N' cstep (clos_refl_trans' cstep) l1 l3 (ltac:(reflexivity))
      (c1, st1) (c1', st') (Skip%imp, st2). apply H1. auto. auto. auto.
    - exists st1,[],l2.
      split. auto. split. auto. apply rt_refl'. unfold multi_cstep. rewrite rt_rt1n_iff'. auto.
Qed.

Lemma CIf_path_spec: forall b c1 c2 st1 st2 l,
  multi_cstep (CIf b c1 c2, st1) l (CSkip, st2) ->
  multi_bstep st1 b BTrue /\
  multi_cstep (c1, st1) l (CSkip, st2) \/
  multi_bstep st1 b BFalse /\
  multi_cstep (c2, st1) l (CSkip, st2).
Proof.
  intros.
  remember ((CIf b c1 c2), st1) as c eqn:H1.
  remember (CSkip, st2) as c' eqn:H2.
  revert b c1 c2 st1 st2 H1 H2.
  unfold multi_cstep in H.
  rewrite rt_rt1n_iff' in H.
   induction H; intros; subst.
  + inversion H2.
  + inversion H; subst.
    - specialize (IHclos_refl_trans_1n' _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHclos_refl_trans_1n' as [[? ?] | [? ?]].
      * left. split. etransitivity_1n; eassumption.
      rewrite app_nil_l. auto.
      * right. split. etransitivity_1n; eassumption.
      rewrite app_nil_l. auto.
    - left. split. reflexivity. rewrite app_nil_l. unfold multi_cstep. rewrite rt_rt1n_iff'. auto.
    - right. split. reflexivity. rewrite app_nil_l. unfold multi_cstep. rewrite rt_rt1n_iff'. auto.
Qed.

Fixpoint CWhile_path b c1 st1 st2 (l:list Z) (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b BFalse /\ st1 = st2 /\ l=[]
  | S n' => exists st1' l1 l2,
            multi_bstep st1 b BTrue /\
            multi_cstep (c1, st1) l1 (CSkip, st1') /\
            CWhile_path b c1 st1' st2 l2 n' /\ l = l1 ++ l2
  end.

Definition CWhile_path' b' b c1 st1 st2 (l:list Z) (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b' BFalse /\ st1 = st2 /\ l=[]
  | S n' => exists st1' l1 l2,
            multi_bstep st1 b' BTrue /\
            multi_cstep (c1, st1) l1 (CSkip, st1') /\
            CWhile_path b c1 st1' st2 l2 n' /\ l = l1 ++ l2
  end.

Definition CWhile_path'' c1' b c1 st1 st2 l (n: nat): Prop:=
  exists st1' l1 l2,
    multi_cstep (c1', st1) l1 (CSkip, st1') /\
    CWhile_path b c1 st1' st2 l2 n /\ l = l1 ++ l2.

Lemma CWhile_path_spec_aux: forall st1 st2 c c' l,
  multi_cstep (c, st1) l (c', st2) ->
  (forall b c1,
     c = CWhile b c1 ->
     c' = Skip%imp ->
     exists n, CWhile_path b c1 st1 st2 l n) /\
  (forall b' b c1,
     c = CIf b' (CSeq c1 (CWhile b c1)) CSkip ->
     c' = Skip%imp ->
     exists n, CWhile_path' b' b c1 st1 st2 l n) /\
  (forall c1' b c1,
     c = CSeq c1' (CWhile b c1) ->
     c' = Skip%imp ->
     exists n, CWhile_path'' c1' b c1 st1 st2 l n).
Proof.
  intros.
  unfold multi_cstep in H.
  rewrite rt_rt1n_iff' in H.
  remember (c, st1) as cs eqn:H1.
  remember (c', st2) as cs' eqn:H2.
  revert c c' st1 st2 H1 H2.
  induction H; intros.
  + split.
    { intros; subst. inversion H2. }
    split.
    { intros; subst. inversion H2. }
    { intros; subst. inversion H2. }
  + split; [| split].
    - intros; subst.
      destruct y as [cc sstt].
      specialize (IHclos_refl_trans_1n' _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHclos_refl_trans_1n' as [_ [IHclos_refl_trans_1n' _]].
      inversion H; subst.
      specialize (IHclos_refl_trans_1n' _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHclos_refl_trans_1n' as [n ?].
      exists n.
      destruct n.
      simpl. simpl in H1. firstorder.
      firstorder.
    - intros; subst.
      inversion H; subst.
      * specialize (IHclos_refl_trans_1n' _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
       destruct IHclos_refl_trans_1n' as [_ [IHclos_refl_trans_1n' _]].
        specialize (IHclos_refl_trans_1n' _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHclos_refl_trans_1n' as [n ?].
        exists n.
        destruct n; unfold CWhile_path' in H1; simpl.
       ++ destruct H1 as [? [? ?]].
          split; [etransitivity_1n; eassumption | firstorder].
       ++ destruct H1 as [st1' [l1[l3[? ?]]]].
          exists st1',l1,l3.
          split; [etransitivity_1n; eassumption | tauto].
      * specialize (IHclos_refl_trans_1n' _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHclos_refl_trans_1n' as [_ [_ IHclos_refl_trans_1n']].
        specialize (IHclos_refl_trans_1n' _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHclos_refl_trans_1n' as [n ?].
        exists (S n).
        unfold CWhile_path'' in H1.
        simpl.
        destruct H1 as [st1' [l1[l3[? ?]]]].
        exists st1',l1,l3.
        split. reflexivity.  firstorder.
      * exists O.
        simpl.
        split. reflexivity. rewrite <- rt_rt1n_iff' in H0.
        apply CSkip_halt in H0. firstorder.
    - intros; subst.
      inversion H; subst.
      * specialize (IHclos_refl_trans_1n' _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
         destruct IHclos_refl_trans_1n' as [_ [_ IHclos_refl_trans_1n']].
        specialize (IHclos_refl_trans_1n' _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHclos_refl_trans_1n' as [n ?].
        exists n.
        unfold CWhile_path'' in H1.
        unfold CWhile_path''.
        destruct H1 as [st1' [l0 [l3 [? [? ?]]]]].
        exists st1',(l1++l0),l3. split.
        pose proof trans_1N' cstep (clos_refl_trans' cstep) l1 l0 (ltac:(reflexivity))
      (c1', st1) (c1'0, st') (Skip%imp, st1'). apply H4. auto. auto.
      subst. firstorder. rewrite app_assoc. auto.
      * specialize (IHclos_refl_trans_1n' _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHclos_refl_trans_1n' as [IHclos_refl_trans_1n' [? ?]].
        specialize (IHclos_refl_trans_1n' _ _ ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHclos_refl_trans_1n' as [n ?].
        exists n.
        unfold CWhile_path''.
        exists st1,[],l2.
        split. apply rt_refl'. firstorder.
Qed.

Lemma CWhile_path_spec: forall b c1 st1 st2 l,
  multi_cstep (CWhile b c1, st1) l (CSkip, st2) ->
  exists n, CWhile_path b c1 st1 st2 l n.
Proof.
  intros.
  remember (CWhile b c1) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 H0 H1.
  pose proof CWhile_path_spec_aux st1 st2 c c' l.
  tauto.
Qed.

Lemma Unit_SG_path_spec: forall U q st1 st2 l,
  multi_cstep (Unit_SG U q, st1) l (CSkip, st2) ->
  st2 = ((fst st1),  ((u_1 U q) # (snd st1))) /\ l = [].
Proof.
  intros.
  remember (Unit_SG U q, st1) as c eqn:H0.
  remember (CSkip, st2) as c' eqn:H1.
  revert st1 st2 H0 H1. 
  unfold multi_cstep in *.
  rewrite rt_rt1n_iff' in H.
   induction H; intros; subst.
  + inversion H1.
  + clear IHclos_refl_trans_1n'.
      inversion H. subst.
      rewrite <- rt_rt1n_iff' in H0.
      apply CSkip_halt in H0.
      firstorder.
Qed.

Lemma Unit_DB_path_spec: forall U q p st1 st2 l,
  multi_cstep (Unit_DB U q p, st1) l (CSkip, st2) ->
  st2 = ((fst st1),  ((u_2 U q p) # (snd st1))) /\ l = [].
Proof.
  intros.
  remember (Unit_DB U q p, st1) as c eqn:H0.
  remember (CSkip, st2) as c' eqn:H1.
  revert st1 st2 H0 H1.
  unfold multi_cstep in *.
  rewrite rt_rt1n_iff' in H.
   induction H; intros; subst.
  + inversion H1.
  + clear IHclos_refl_trans_1n'.
      inversion H. subst.
      rewrite <- rt_rt1n_iff' in H0.
      apply CSkip_halt in H0.
      inversion H0. inversion H2. inversion H4. subst.
      rewrite app_nil_l. auto.
Qed.

Lemma Meas_path_spec: forall x q st1 st2 l,
  multi_cstep (Meas x q, st1) l (CSkip, st2) ->
  st2 = ((x !-> 0, (fst st1)), ((Mea0 q) # (snd st1))) /\ l=[0] \/
  st2 = ((x !-> 1, (fst st1)), ((Mea1 q) # (snd st1))) /\ l=[1].
Proof.
  intros.
  remember (Meas x q, st1) as c eqn:H0.
  remember (CSkip, st2) as c' eqn:H1.
  revert st1 st2 H0 H1.
  unfold multi_cstep in *.
  rewrite rt_rt1n_iff' in H.
   induction H; intros; subst.
  + inversion H1.
  + clear IHclos_refl_trans_1n'.
      inversion H. subst.
      rewrite <- rt_rt1n_iff' in H0.
      apply CSkip_halt in H0.
      destruct H0 as[? [? ?]]. subst.
      rewrite app_nil_r. auto.
Qed.

Theorem semantic_equiv_com2: forall c st1 st2 l,
  multi_cstep (c, st1) l (CSkip, st2) ->  ceval c st1 l st2.
Proof.
  intros.
  revert st1 st2 l H; induction c; intros.
  + apply CSkip_halt in H.
    destruct H as [? [? ?]].
    subst. unfold ceval.
    unfold TerRel.id. auto.
  + apply CAss_path_spec in H.
    destruct H as [n [? ?]].
    apply semantic_equiv_aexp2 in H.
    rewrite ceval_CAss,H.
    tauto.
  + apply CSeq_path_spec in H.
    destruct H as [st1' [l1 [l2 [? [? ?]]]]].
    apply IHc1 in H0.
    apply IHc2 in H1.
    rewrite ceval_CSeq.
    unfold TerRel.concat.
    exists st1',l1,l2.
    auto.
  + apply CIf_path_spec in H.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold TerRel.union,
           TerRel.concat,
           TerRel.test_rel.
    specialize (IHc1 st1 st2).
    specialize (IHc2 st1 st2).
    pose proof semantic_equiv_bexp2 st1 b.
    destruct H.
    left. exists st1,[],l. rewrite app_nil_l.
    split. split. auto. split. inversion H0. apply H1. apply H. auto. split. apply IHc1. apply H. auto.
    right. exists st1,[],l. rewrite app_nil_l. 
    split. split. auto. split. inversion H0. apply H2. apply H. auto. split. apply IHc2. apply H. auto.
  + apply CWhile_path_spec in H.
    rewrite ceval_CWhile.
    unfold loop_sem.
    unfold TerRel.omega_union.
    destruct H as [n ?].
    exists n.
    revert st1 l H; induction n; simpl; intros.
    - pose proof semantic_equiv_bexp2 st1 b.
      destruct H as [? [? ?]].
      subst.
      unfold TerRel.test_rel,
             Sets.complement.
      tauto.
    - destruct H as [st1' [l1 [l2 [? ?]]]].
      specialize (IHn st1').
      unfold TerRel.concat,
             TerRel.test_rel.
      apply semantic_equiv_bexp2 in H.
      exists st1,[],l.
      split.
      * tauto.
      * split. exists st1',l1,l2.
        specialize (IHc st1 st1' l1). split. apply IHc. destruct H0. auto.
        split. apply IHn. destruct H0. destruct H1. auto. destruct H0. destruct H1. auto.
        rewrite app_nil_l. auto.
  +  apply Unit_SG_path_spec in H.
    rewrite ceval_Unit_SG. auto.
  +  apply Unit_DB_path_spec in H.
    rewrite ceval_Unit_DB. auto.
  +  apply Meas_path_spec in H.
    rewrite ceval_Meas. auto.
Qed.

Theorem semantic_equiv: forall c st1 st2 l,
  ceval c st1 l st2 <-> multi_cstep (c, st1) l (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

