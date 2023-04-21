Require Export Preparation.

Section Sim.

Definition x : Cvar := O.
Definition k : Cvar :=S O.

Lemma I4_eq : I_2 ⊗ I_2 = I (2 * 2) .
Proof.
  rewrite I2_eq.
  rewrite id_kron.
  simpl; auto.
Qed.

Lemma I8_eq : I_2 ⊗ (I_2 ⊗ I_2) = I (2 * (2 * 2)) .
Proof.
  rewrite I2_eq.
  rewrite id_kron.
  simpl; auto.
  rewrite id_kron.
  simpl; auto.
Qed.

Lemma kr1 :  I 1 ⊗ H ≡ H.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p1 :
super (u_1 H 0 4) (density (∣0,0,0,0⟩)) ≡ density (∣+⟩ ⊗ ∣0,0,0⟩).
Proof.
unfold u_1.
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r.
rewrite <- I8_eq.
unfold super. rewrite kr1.
super_reduce.
Qed.

Lemma p2 :
super (u_1 H 1 4) (density (∣+⟩ ⊗ ∣0,0,0⟩)) ≡ density (∣+⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩).
Proof.
unfold u_1. 
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r.
rewrite <- I4_eq, <- I2_eq.
unfold super. 
super_reduce.
Qed.

Lemma kr3 :  I 1 ⊗ (B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ σX) ≡ (B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ σX).
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p3 :
super (u_2 σX 0 2 4) (density (∣+⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩)) ≡ density (/√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1,0⟩)).
Proof.
unfold u_2. 
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r.
rewrite <- I2_eq.
unfold super. rewrite kr3.
super_reduce.
Qed.

Lemma p4 :
super (u_1 σX 3 4) (density (/√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1,0⟩))) ≡ density (/√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0,1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1,1⟩)).
Proof.
unfold u_1. 
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r.
rewrite <- I8_eq. rewrite kron_1_r.
unfold super.
super_reduce.
Qed.

Lemma p5 :
super (u_2 σX 1 2 4) (density (/√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0,1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1,1⟩))) ≡ density (/C2 .* ∣0,0,0,1⟩ .+ /C2 .* ∣0,1,1,1⟩ .+ /C2 .* ∣1,0,1,1⟩ .+ /C2 .* ∣1,1,0,1⟩).
Proof.
unfold u_2. 
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r, <- I2_eq. 
repeat rewrite kron_1_r.
super_reduce.
Qed.

Lemma p6 :
super (u_1 H 0 4) (density (/C2 .* ∣0,0,0,1⟩ .+ /C2 .* ∣0,1,1,1⟩ .+ /C2 .* ∣1,0,1,1⟩ .+ /C2 .* ∣1,1,0,1⟩)) ≡ density (/C2 .* (∣+⟩ ⊗ ∣0,0,1⟩) .+ /C2 .* (∣+⟩ ⊗ ∣1,1,1⟩) .+ /C2 .* (∣-⟩ ⊗ ∣0,1,1⟩) .+ /C2 .* (∣-⟩ ⊗ ∣1,0,1⟩)).
Proof.
unfold u_1. 
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r, <-I8_eq. 
unfold super. rewrite kr1.
super_reduce.
Qed.

Lemma p7 :
super (u_1 H 1 4) (density (/C2 .* (∣+⟩ ⊗ ∣0,0,1⟩) .+ /C2 .* (∣+⟩ ⊗ ∣1,1,1⟩) .+ /C2 .* (∣-⟩ ⊗ ∣0,1,1⟩) .+ /C2 .* (∣-⟩ ⊗ ∣1,0,1⟩))) ≡ density (/C2 .* ∣0,0,0,1⟩ .+ /C2 .* ∣1,1,0,1⟩ .+ /C2 .* ∣0,0,1,1⟩ .+ - /C2 .* ∣1,1,1,1⟩).
Proof.
unfold u_1.
Opaque Init.Nat.mul. simpl.
rewrite mult_1_r, <-I4_eq,<-I2_eq.
super_reduce.
Qed.


Definition sim : com :=
Unit_SG H 0 4 ;;
Unit_SG H 1 4 ;;
Unit_DB σX 0 2 4 ;;
Unit_SG σX 3 4 ;;
Unit_DB σX 1 2 4 ;;
Unit_SG H 0 4 ;;
Unit_SG H 1 4.

Lemma sim_cor : @dceval 4 sim
[(empty_CState, density ∣0,0,0,0⟩)]
[(empty_CState, density (/C2 .* ∣0,0,0,1⟩ .+ /C2 .* ∣1,1,0,1⟩ .+ /C2 .* ∣0,0,1,1⟩ .+ - /C2 .* ∣1,1,1,1⟩))].
Proof.
unfold sim.
rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣0,0,0⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (∣+⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (/√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1,0⟩)))].
split.
rewrite dceval_Unit_DB.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p3. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (/√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0,1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1,1⟩)))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p4. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (/C2 .* ∣0,0,0,1⟩ .+ /C2 .* ∣0,1,1,1⟩ .+ /C2 .* ∣1,0,1,1⟩ .+ /C2 .* ∣1,1,0,1⟩))].
split.
rewrite dceval_Unit_DB.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p5. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (/C2 .* (∣+⟩ ⊗ ∣0,0,1⟩) .+ /C2 .* (∣+⟩ ⊗ ∣1,1,1⟩) .+ /C2 .* (∣-⟩ ⊗ ∣0,1,1⟩) .+ /C2 .* (∣-⟩ ⊗ ∣1,0,1⟩)))].
split.
rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p6. reflexivity.
apply eq_DS_nil.

rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
simpl. unfold empty_QState.
rewrite p7. reflexivity.
apply eq_DS_nil.
Qed.

End Sim.
