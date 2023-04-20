Require Export Preparation.

Section Tele.


Definition x : Cvar := O.
Definition y : Cvar :=S O.

Check [((x !-> 0,  y !->9), ∣0⟩); ((x !-> 1, y !->9), ∣1⟩)].


Definition bell00 := /√2 .* (∣0,0⟩) .+ /√2 .* (∣1,1⟩).
Definition bell01 := /√2 .* (∣0,1⟩) .+ /√2 .* (∣1,0⟩).
Definition bell10 := /√2 .* (∣0,0⟩) .+ (-/√2) .* (∣1,1⟩).
Definition bell11 := /√2 .* (∣0,1⟩) .+ (-/√2) .* (∣1,0⟩).


Definition tele : com :=
Unit_DB σX 0 1 3 ;;
Unit_SG H 0 3 ;;
Meas x 0 3 ;;
Meas y 1 3 ;;
If (y == 1%Z)
    Then (Unit_SG σX 2 3)
    Else Skip EndIf ;;
If (x  == 1%Z)
    Then (Unit_SG σZ 2 3)
    Else Skip EndIf.

Variables (α β : C).
Hypothesis Normalise: (Cmod α ^ 2 + Cmod β ^ 2)%R = R1.
(* Cmod a ^2 + Cmod b ^2 = 1. *)
Definition φ : Vector 2 := α .* ∣0⟩ .+ β .* ∣1⟩.

Definition φ0 := φ ⊗ bell00.


Lemma kr1 :  I 1 ⊗ (B0 ⊗ I_2 .+ B3 ⊗ σX) ≡ (B0 ⊗ I_2 .+ B3 ⊗ σX).
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p1 :
super (u_2 σX 0 1 3) (density (φ ⊗ bell00)) ≡ density (α .* ∣0⟩ ⊗ bell00 .+ β .* ∣1⟩ ⊗ bell01).
Proof.
unfold u_2.
Opaque Init.Nat.mul. simpl.
repeat rewrite mult_1_r,mult_1_l,kron_1_r.
repeat rewrite <- I2_eq.
unfold super.
rewrite kr1.
unfold bell00, bell01,φ .
super_reduce.     (* autorewrite with G_db. *)
Qed.

Lemma I4_eq : I_2 ⊗ I_2 = I (2 * 2) .
Proof.
  rewrite I2_eq.
  rewrite id_kron.
  simpl; auto.
Qed.

Lemma kr2 :  I 1 ⊗ H ≡ H.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p2 :
super (u_1 H 0 3) (density (α .* ∣0⟩ ⊗ bell00 .+ β .* ∣1⟩ ⊗ bell01)) ≡ density (α .* ∣+⟩ ⊗ bell00 .+ β .* ∣-⟩ ⊗ bell01).
Proof.
unfold u_1. simpl.
rewrite mult_1_r,<-I4_eq.
unfold super. rewrite kr2.
unfold bell00, bell01,φ.
super_reduce.
Qed.

Lemma kr3 :  I 1 ⊗ B0 ≡ B0.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p3 :
super (Mea0 0 3) (density (α .* ∣+⟩ ⊗ bell00 .+ β .* ∣-⟩ ⊗ bell01)) ≡ density (/ √ 2 .* ∣0⟩ ⊗ (α .* bell00 .+ β .* bell01)).
Proof.
unfold Mea0,u_1. simpl.
rewrite mult_1_r,<-I4_eq.
unfold super. rewrite kr3.
unfold bell00, bell01,φ.
super_reduce.
Qed.

Lemma kr4 :  I 1 ⊗ B3 ≡ B3.
Proof.
unfold mat_equiv.
intros.
rewrite kron_1_l. auto.
Qed.

Lemma p4 :
super (Mea1 0 3) (density (α .* ∣+⟩ ⊗ bell00 .+ β .* ∣-⟩ ⊗ bell01)) ≡ density (/ √ 2 .* ∣1⟩ ⊗ (α .* bell00 .+ - β .* bell01)).
Proof.
unfold Mea1,u_1. simpl.
rewrite mult_1_r,<-I4_eq.
unfold super.
 rewrite kr4.
unfold bell00, bell01,φ.
super_reduce.
Qed.

Lemma p5 :
super (Mea0 1 3) (density (/ √ 2 .* ∣0⟩ ⊗ (α .* bell00 .+ β .* bell01))) ≡ density  (/ C2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))).
Proof.
unfold Mea0,u_1. simpl.
rewrite mult_1_r, <-I2_eq.
unfold bell00, bell01,φ.
super_reduce.
Qed.

Lemma p6 :
super (Mea0 1 3) (density (/ √ 2 .* ∣1⟩ ⊗ (α .* bell00 .+ - β .* bell01))) ≡ density (/ C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))).
Proof.
unfold Mea0,u_1. simpl.
rewrite mult_1_r,<-I2_eq.
unfold bell00, bell01,φ.
super_reduce.
Qed.

Lemma p7 :
super (Mea1 1 3) (density (/ √ 2 .* ∣0⟩ ⊗ (α .* bell00 .+ β .* bell01))) ≡ density (/ C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))).
Proof.
unfold Mea1,u_1. simpl.
rewrite mult_1_r,<-I2_eq.
unfold bell00, bell01,φ.
super_reduce.
Qed.


Lemma p8 :
super (Mea1 1 3) (density (/ √ 2 .* ∣1⟩ ⊗ (α .* bell00 .+ - β .* bell01))) ≡ density (/ C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))).
Proof.
unfold Mea1,u_1. simpl.
rewrite mult_1_r,<-I2_eq.
unfold bell00, bell01,φ.
super_reduce.
Qed.

Lemma p9 :
super (u_1 σX 2 3) (density (/ C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩)))) ≡ density (/ C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))).
Proof.
unfold u_1. simpl.
rewrite mult_1_r,<-I4_eq,kron_1_r.
super_reduce.
Qed.

Lemma p10 :
super (u_1 σX 2 3) (density (/ C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩)))) ≡ density (/ C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))).
Proof.
unfold u_1. simpl.
rewrite mult_1_r,<-I4_eq,kron_1_r.
super_reduce.
Qed.

Lemma p11 :
super (u_1 σZ 2 3) (density (/ C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩)))) ≡ density (/ C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))).
Proof.
unfold u_1. simpl.
rewrite mult_1_r,<-I4_eq,kron_1_r.
super_reduce.
Qed.

Lemma p12 :
super (u_1 σZ 2 3) (density (/ C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩)))) ≡ density (/ C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))).
Proof.
unfold u_1. simpl.
rewrite mult_1_r,<-I4_eq,kron_1_r.
super_reduce.
Qed.



Lemma tele_cor : @dceval 3 tele
[(empty_CState, density (φ ⊗ bell00))]
[((y !-> 1, x !-> 1), density (/ C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
((y !-> 0, x !-> 1), density (/ C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
((y !-> 1, x !-> 0), density (/ C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
((y !-> 0, x !-> 0), density (/ C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))))].
Proof.
unfold tele.
rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (α .*  ∣0⟩ ⊗ bell00   .+  β .*  ∣1⟩ ⊗ bell01))].
split.

unfold dceval.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p1. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [(empty_CState, density (α .*  ∣+⟩ ⊗ bell00   .+  β .*  ∣-⟩ ⊗ bell01))].
split. rewrite dceval_Unit_SG.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p2. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((x !-> 0), density (/ √ 2 .* ∣0⟩ ⊗ (α .* bell00 .+ β .* bell01)));
                ((x !-> 1), density (/ √ 2 .* ∣1⟩ ⊗ (α .* bell00 .+ - β .* bell01)))].
split.
rewrite dceval_Meas.
simpl. unfold update_State,update_QState,constant_func.
simpl. unfold DQ,update_QState.
apply eq_DS_cons. auto.
rewrite p3. reflexivity.
apply eq_DS_cons. auto.
rewrite p4. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((y !-> 0, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))));
               ((y !-> 1, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))));
               ((y !-> 1, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))))].
split.
rewrite dceval_Meas .
simpl. unfold update_State,update_QState,constant_func.
apply eq_DS_cons. auto.
rewrite p5. reflexivity.
apply eq_DS_cons. auto.
rewrite p6. reflexivity.
apply eq_DS_cons. auto.
rewrite p7. reflexivity.
apply eq_DS_cons. auto.
rewrite p8. reflexivity.
apply eq_DS_nil.

rewrite dceval_CSeq.
unfold BinRel.concat.
exists [((y !-> 1, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 1, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))));
               ((y !-> 0, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))].
split.
rewrite dceval_CIf.
unfold if_sem. unfold BinRel.merge.
exists [((y !-> 1, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 1, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))].
exists [((y !-> 0, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))].
split.
unfold BinRel.concat.
exists [((y !-> 1, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))));
               ((y !-> 1, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))))].
split. unfold BinRel.test_rel. simpl. auto.

rewrite dceval_Unit_SG. simpl. unfold DQ,update_QState. simpl.
apply eq_DS_cons. auto.
rewrite p9. reflexivity.
apply eq_DS_cons. auto.
rewrite p10. reflexivity.
apply eq_DS_nil.

unfold BinRel.concat. split.
exists [((y !-> 0, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))].
split. unfold BinRel.test_rel. simpl. auto.
rewrite dceval_CSkip. unfold BinRel.id. auto. auto.

rewrite dceval_CIf.
unfold if_sem. unfold BinRel.merge.
exists [((y !-> 1, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))))].
exists [((y !-> 1, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 0), density (/C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))))].
split. 
unfold BinRel.concat.
exists [((y !-> 1, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))));
               ((y !-> 0, x !-> 1), density (/C2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))].
split. unfold BinRel.test_rel. simpl. auto.

rewrite dceval_Unit_SG. simpl. unfold DQ,update_QState. simpl.
apply eq_DS_cons. auto.
rewrite p11. reflexivity.
apply eq_DS_cons. auto.
rewrite p12. reflexivity.
apply eq_DS_nil.

unfold BinRel.concat.
split.
exists [((y !-> 1, x !-> 0), density (/ C2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))));
               ((y !-> 0, x !-> 0), density (/ C2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))))].
split. unfold BinRel.test_rel. simpl. auto.
rewrite dceval_CSkip. unfold BinRel.id. auto. auto.
Qed.


End Tele.