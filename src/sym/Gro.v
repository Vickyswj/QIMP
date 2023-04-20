Require Export Preparation.

Section Gro.

Definition x : Cvar := O.
Definition k : Cvar :=S O.

Lemma kr1 :  I 1 ⊗ (B0 ⊗ I_2 .+ B3 ⊗ σZ) ≡ B0 ⊗ I_2 .+ B3 ⊗ σZ.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p1 :
super (u_2 σZ 0 1 2) (density (∣+⟩ ⊗ ∣+⟩)) ≡ density (/√2 .* (∣0⟩ ⊗ ∣+⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩)).
Proof.
unfold u_2.
simpl.
repeat rewrite kron_1_r.
repeat rewrite <- I2_eq.
unfold super.
rewrite kr1.
super_reduce.
Qed.

Lemma kr2 :  I 1 ⊗ H ≡ H.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p2 :
super (u_1 H 0 2) (density (/√2 .* (∣0⟩ ⊗ ∣+⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩))) ≡ density (/√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩)).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p3 :
super (u_1 H 1 2) (density (/√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩))) ≡ density (/√2 .* (∣0⟩ ⊗ ∣+⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩)).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq, kron_1_r.
unfold super.
super_reduce.
Qed.

Lemma kr4 :  I 1 ⊗ σX ≡ σX.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p4 :
super (u_1 σX 0 2) (density (/√2 .* (∣0⟩ ⊗ ∣+⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩))) ≡ density (/√2 .* (∣1⟩ ⊗ ∣+⟩) .+ /√2 .* (∣0⟩ ⊗ ∣-⟩)).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq.
unfold super. rewrite kr4.
super_reduce.
Qed.

Lemma p5 :
super (u_1 σX 1 2) (density (/√2 .* (∣1⟩ ⊗ ∣+⟩) .+ /√2 .* (∣0⟩ ⊗ ∣-⟩))) ≡ density (/√2 .* (∣1⟩ ⊗ ∣+⟩) .+ - /√2 .* (∣0⟩ ⊗ ∣-⟩)).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq, kron_1_r.
unfold super.
super_reduce.
Qed.

Lemma p6 :
super (u_2 σZ 0 1 2) (density (/√2 .* (∣1⟩ ⊗ ∣+⟩) .+ - /√2 .* (∣0⟩ ⊗ ∣-⟩))) ≡ density (- C1 .* ∣-⟩ ⊗ ∣-⟩).
Proof.
unfold u_2. simpl.
repeat rewrite kron_1_r.
unfold super. rewrite kr1.
super_reduce.
Qed.

Lemma p7 :
super (u_1 σX 0 2) (density (- C1 .* ∣-⟩ ⊗ ∣-⟩)) ≡ density (∣-⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq.
unfold super. rewrite kr4.
super_reduce.
Qed.

Lemma p8 :
super (u_1 σX 1 2) (density (∣-⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣-⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq, kron_1_r.
unfold super.
super_reduce.
Qed.

Lemma p9 :
super (u_1 H 0 2) (density (- C1 .* ∣-⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣1⟩ ⊗ ∣-⟩).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq.
unfold super. rewrite kr2.
super_reduce.
Qed.

Lemma p10 :
super (u_1 H 1 2) (density (- C1 .* ∣1⟩ ⊗ ∣-⟩)) ≡ density (- C1 .* ∣1⟩ ⊗ ∣1⟩).
Proof.
unfold u_1. simpl.
rewrite <-I2_eq, kron_1_r.
unfold super.
super_reduce.
Qed.

Lemma p11 :
density (∣1⟩ ⊗ ∣1⟩) ≡ density (- C1 .* ∣1⟩ ⊗ ∣1⟩).
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


Definition gro : com :=
While (x<= (k-1%Z)) Do
Unit_DB σZ 0 1 2 ;;
Unit_SG H 0 2 ;;
Unit_SG H 1 2 ;;
Unit_SG σX 0 2 ;;
Unit_SG σX 1 2 ;;
Unit_DB σZ 0 1 2 ;;
Unit_SG σX 0 2 ;;
Unit_SG σX 1 2 ;;
Unit_SG H 0 2 ;;
Unit_SG H 1 2 ;;
x ::= x + 1%Z
EndWhile.

Lemma gro_cor : @dceval 2 gro
[((k !-> 1), density (∣+⟩ ⊗ ∣+⟩))]
[((x !-> 1, k !-> 1), density (∣1⟩ ⊗ ∣1⟩))].
Proof.
unfold gro.
rewrite dceval_CWhile.
unfold loop_sem. unfold BinRel.omega_union.
exists 1. simpl.

unfold BinRel.concat.
exists [((x !-> 1, k !-> 1), density (∣1⟩ ⊗ ∣1⟩))].
unfold BinRel.merge.
split.
exists [((x !-> 1, k !-> 1), density (∣1⟩ ⊗ ∣1⟩))], [].
split.
exists [((k !-> 1), density (∣+⟩ ⊗ ∣+⟩))].
split.
unfold BinRel.test_rel'. simpl.
split. auto. unfold not. intros. inversion H.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (/√2 .* (∣0⟩ ⊗ ∣+⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩)))].
split.
rewrite dceval_Unit_DB. 
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (/√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩)))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (/√2 .* (∣0⟩ ⊗ ∣+⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩)))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p3. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (/√2 .* (∣1⟩ ⊗ ∣+⟩) .+ /√2 .* (∣0⟩ ⊗ ∣-⟩)))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p4. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (/√2 .* (∣1⟩ ⊗ ∣+⟩) .+ - /√2 .* (∣0⟩ ⊗ ∣-⟩)))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p5. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (- C1 .*∣-⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_DB. 
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p6. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (∣-⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p7. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (-C1 .* ∣-⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p8. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (-C1 .* ∣1⟩ ⊗ ∣-⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p9. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((k !-> 1), density (-C1 .* ∣1⟩ ⊗ ∣1⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p10. reflexivity.
apply eq_DS_nil.

rewrite dceval_CAss.
simpl. unfold DC. simpl.
apply eq_DS_cons. auto.
apply p11. apply eq_DS_nil.

split.
unfold BinRel.test_rel. simpl. auto.
simpl. auto.
unfold BinRel.test_rel''. simpl. auto.
Qed.

End Gro.
