Require Export Preparation.

Section Deu.

Definition x : Cvar := O.
Definition k : Cvar :=S O.


Lemma p1 :
super (u_1 σX 1 2) (density (∣0⟩ ⊗ ∣0⟩)) ≡ density (∣0⟩ ⊗ ∣1⟩).
Proof.
unfold u_1. simpl.
repeat rewrite kron_1_r.
repeat rewrite <- I2_eq.
super_reduce.
Qed.

Lemma kr2 :  I 1 ⊗ H ≡ H.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p2 :
super (u_1 H 0 2) (density (∣0⟩ ⊗ ∣1⟩)) ≡ density (∣+⟩ ⊗ ∣1⟩).
Proof.
unfold u_1. simpl.
repeat rewrite <- I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p3 :
super (u_1 H 1 2) (density (∣+⟩ ⊗ ∣1⟩)) ≡ density (∣+⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
repeat rewrite kron_1_r.
repeat rewrite <- I2_eq.
super_reduce.
Qed.

Lemma kr4 :  I 1 ⊗ (B0 ⊗ I_2 .+ B3 ⊗ σX) ≡ B0 ⊗ I_2 .+ B3 ⊗ σX.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p4 :
super (u_2 σX 0 1 2) (density (∣+⟩ ⊗ ∣-⟩)) ≡ density (∣-⟩ ⊗ ∣-⟩).
Proof.
unfold u_2. simpl.
repeat rewrite kron_1_r.
unfold super. rewrite kr4.
super_reduce.
Qed.

Lemma p5 :
super (u_1 σX 1 2) (density (∣+⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣+⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
repeat rewrite kron_1_r.
repeat rewrite <- I2_eq.
super_reduce.
Qed.

Lemma p6 :
super (u_2 σX 0 1 2) (density (- C1 .* ∣+⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣-⟩ ⊗ ∣-⟩).
Proof.
unfold u_2. simpl.
repeat rewrite kron_1_r.
unfold super. rewrite kr4.
super_reduce.
Qed.

Lemma p7 :
super (u_1 H 0 2) (density (∣+⟩ ⊗ ∣-⟩)) ≡ density (∣0⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
repeat rewrite <- I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p8 :
super (u_1 H 0 2) (density (∣-⟩ ⊗ ∣-⟩)) ≡ density (∣1⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
repeat rewrite <- I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p9 :
super (u_1 H 0 2) (density (- C1 .* ∣-⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣1⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
repeat rewrite <- I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p10 :
super (u_1 H 0 2) (density (- C1 .* ∣+⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣0⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
repeat rewrite <- I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p11 :
density (- C1 .* ∣1⟩ ⊗ ∣-⟩) ≡ density (∣1⟩ ⊗ ∣-⟩).
Proof.
unfold density.
rewrite Mscale_kron_dist_l.
rewrite Mscale_adj.
reduce_scale.
rewrite Mscale_mult_dist_r.
rewrite Mscale_mult_dist_l.
rewrite Mscale_assoc.
assert (((-1)%R * (-1)%R)%C = C1). lca.
rewrite H. rewrite Mscale_1_l. reflexivity.
Qed.

Lemma p12 :
density (- C1 .* ∣0⟩ ⊗ ∣-⟩) ≡ density (∣0⟩ ⊗ ∣-⟩).
Proof.
unfold density.
rewrite Mscale_kron_dist_l.
rewrite Mscale_adj.
reduce_scale.
rewrite Mscale_mult_dist_r.
rewrite Mscale_mult_dist_l.
rewrite Mscale_assoc.
assert (((-1)%R * (-1)%R)%C = C1). lca.
rewrite H. rewrite Mscale_1_l. reflexivity.
Qed.


Definition deu00 : com :=
Unit_SG σX 1 2 ;;
Unit_SG H 0 2 ;;
Unit_SG H 1 2 ;;
Unit_SG H 0 2.

Lemma deu00_cor : @dceval 2 deu00
[(empty_CState, density (∣0⟩ ⊗ ∣0⟩))]
[(empty_CState, density (∣0⟩ ⊗ ∣-⟩))].
Proof.
unfold deu00.
rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣0⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p3. reflexivity.
apply eq_DS_nil.

rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p7. reflexivity.
apply eq_DS_nil.
Qed.




Definition deu01 : com :=
Unit_SG σX 1 2 ;;
Unit_SG H 0 2 ;;
Unit_SG H 1 2 ;;
Unit_DB σX 0 1 2 ;;
Unit_SG H 0 2.

Lemma deu01_cor : @dceval 2 deu01
[(empty_CState, density (∣0⟩ ⊗ ∣0⟩))]
[(empty_CState, density (∣1⟩ ⊗ ∣-⟩))].
Proof.
unfold deu01.
rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣0⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p3. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣-⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_DB.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p4. reflexivity.
apply eq_DS_nil.

rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p8. reflexivity.
apply eq_DS_nil.
Qed.




Definition deu10 : com :=
Unit_SG σX 1 2 ;;
Unit_SG H 0 2 ;;
Unit_SG H 1 2 ;;
Unit_SG σX 1 2 ;;
Unit_DB σX 0 1 2 ;;
Unit_SG H 0 2.

Lemma deu10_cor : @dceval 2 deu10
[(empty_CState, density (∣0⟩ ⊗ ∣0⟩))]
[(empty_CState, density (∣1⟩ ⊗ ∣-⟩))].
Proof.
unfold deu10.
rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣0⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p3. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (- C1 .* ∣+⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p5. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (- C1 .* ∣-⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_DB.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p6. reflexivity.
apply eq_DS_nil.

rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p9,p11. reflexivity.
apply eq_DS_nil.
Qed.




Definition deu11 : com :=
Unit_SG σX 1 2 ;;
Unit_SG H 0 2 ;;
Unit_SG H 1 2 ;;
Unit_SG σX 1 2 ;;
Unit_SG H 0 2.

Lemma deu11_cor : @dceval 2 deu11
[(empty_CState, density (∣0⟩ ⊗ ∣0⟩))]
[(empty_CState, density (∣0⟩ ⊗ ∣-⟩))].
Proof.
unfold deu11.
rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣0⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p3. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (- C1 .* ∣+⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p5. reflexivity.
apply eq_DS_nil.

rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p10,p12. reflexivity.
apply eq_DS_nil.
Qed.

End Deu.
