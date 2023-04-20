 (* Require Import RTClosure. *)
Require Export Nat_Dirac.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Logic.Classical. 

Open Scope Z_scope.

Parameter  n: nat.

Definition Cvar: Type := nat.
Definition Qvar: Type := nat.

Definition CState : Type :=  nat -> Z.
Definition QState : Type :=  Square (2^n). 
Definition State := (CState * QState)%type.

Definition empty_CState : CState :=
  (fun _ => 0%Z).

Notation "'_' '!->' 0" := (empty_CState)
  (at level 100, right associativity).

Definition Qint : Square (2^n) := 
fun x y => 
match x, y with 
          | O, O => C1
          | _, _ => C0
          end.

Definition empty_QState : QState := Qint.

Definition empty_State : State :=(empty_CState, empty_QState).

Definition update_CState (cst : CState) (x : Cvar) (z : Z) : CState :=
  (fun x' => if Nat.eq_dec x x' then z else cst x').

Notation "x '!->' v ',' cst" := (update_CState cst x v)
                              (at level 100, v at next level, right associativity).

Notation "x '!->' v" := (x !-> v , empty_CState) (at level 100).

Definition update_QState (qst : QState) (U : Square (2^n)) : QState := super U qst.

Notation " U '#' qst " := (update_QState qst U)
                              (at level 100, right associativity).

Definition update_State (st : State) (x : Cvar) (z : Z) (U : Square (2^n)) : State :=
((x !-> z , (fst st)) , (U # (snd st))).


Module Func.

Definition add {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a + g a.

Definition sub {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a - g a.

Definition mul {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a * g a.

Definition test_eq {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a = g a.

Definition test_lt {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a < g a.

Definition test_le {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a <= g a.

Definition equiv {A: Type} (f g: A -> Z): Prop :=
  forall a, f a = g a.

Definition le {A: Type} (f g: A -> Z): Prop :=
  forall a, f a <= g a.

End Func.


Module Sets.

Definition full {A: Type}: A -> Prop := fun _ => True.

Definition empty {A: Type}: A -> Prop := fun _ => False.

Definition uni {A: Type} (X Y: A -> Prop) := fun a => X a \/ Y a.

Definition intersect {A: Type} (X Y: A -> Prop) := fun a => X a /\ Y a.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.

Definition equiv {A: Type} (X Y: A -> Prop): Prop :=
  forall a, X a <-> Y a.

End Sets.


Declare Scope func_scope.
Delimit Scope func_scope with Func.

Notation "f + g" := (Func.add f g): func_scope.
Notation "f - g" := (Func.sub f g): func_scope.
Notation "f * g" := (Func.mul f g): func_scope.


Lemma Func_equiv_refl: forall A, Reflexive (@Func.equiv A).
Proof.
  intros.
  unfold Reflexive.
  unfold Func.equiv.
  intros.
  reflexivity.
Qed.

Lemma Func_equiv_sym: forall A, Symmetric (@Func.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold Func.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Func_equiv_trans: forall A, Transitive (@Func.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold Func.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_equiv_refl: forall A, Reflexive (@Sets.equiv A).
Proof.
  intros.
  unfold Reflexive.
  unfold Sets.equiv.
  intros.
  tauto.
Qed.

Lemma Sets_equiv_sym: forall A, Symmetric (@Sets.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold Sets.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_equiv_trans: forall A, Transitive (@Sets.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold Sets.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_add_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.add.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.add.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_sub_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.sub.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.sub.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_mul_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.mul.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.mul.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_test_eq_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Sets.equiv A) Func.test_eq.
Proof.
  unfold Proper, respectful.
  unfold Func.equiv, Sets.equiv, Func.test_eq.
  intros A f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_test_le_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Sets.equiv A) Func.test_le.
Proof.
  unfold Proper, respectful.
  unfold Func.equiv, Sets.equiv, Func.test_le.
  intros A f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_intersect_equiv: forall A,
  Proper (@Sets.equiv A ==> @Sets.equiv A ==> @Sets.equiv A) Sets.intersect.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Sets.intersect.
  intros A S1 S2 ? T1 T2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_complement_equiv: forall A,
  Proper (@Sets.equiv A ==> @Sets.equiv A) Sets.complement.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Sets.complement.
  intros A S1 S2 ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_complement_complement: forall A (S: A -> Prop),
  Sets.equiv (Sets.complement (Sets.complement S)) S.
Proof.
  intros.
  unfold Sets.equiv, Sets.complement.
  intros.
  tauto.
Qed.

Existing Instances Func_equiv_refl
                   Func_equiv_sym
                   Func_equiv_trans
                   Func_add_equiv
                   Func_sub_equiv
                   Func_mul_equiv.

Existing Instances Sets_equiv_refl
                   Sets_equiv_sym
                   Sets_equiv_trans
                   Func_test_eq_equiv
                   Func_test_le_equiv
                   Sets_intersect_equiv
                   Sets_complement_equiv.


Module TerRel.

Definition id : State -> list Z -> State-> Prop := fun st1 l st2 => st1 = st2 /\ l = [].

Definition empty {A E B: Type}: A -> E -> B -> Prop := fun a e b => False.

Definition concat (r1 r2: State -> list Z -> State -> Prop): State -> list Z -> State -> Prop :=
  fun a e c => exists b l1 l2 , r1 a l1 b /\ r2 b l2 c /\ e = l1 ++ l2.

Definition union {A E B: Type} (r1 r2: A -> E -> B -> Prop): A -> E -> B -> Prop :=
  fun a e b => r1 a e b \/ r2 a e b.

Definition intersection {A E B: Type} (r1 r2: A -> E -> B -> Prop): A -> E -> B -> Prop :=
  fun a e b => r1 a e b /\ r2 a e b.

Definition omega_union {A E B: Type} (rs: nat -> A -> E -> B -> Prop): A -> E -> B -> Prop :=
  fun a e b => exists n, rs n a e b.

Definition test_rel (X: State -> Prop): State -> list Z -> State -> Prop :=
  fun st1 l st2 => st1 = st2 /\ X st1 /\ l = [].

Definition equiv {A E B: Type} (r1 r2: A -> E -> B -> Prop): Prop :=
  forall a e b, r1 a e b <-> r2 a e b.

Definition le {A E B: Type} (r1 r2: A -> E -> B -> Prop): Prop :=
  forall a e b, r1 a e b -> r2 a e b.

End TerRel.

Lemma Ter_equiv_refl: forall A E B, Reflexive (@TerRel.equiv A E B).
Proof.
  unfold Reflexive, TerRel.equiv.
  intros.
  reflexivity.
Qed.

Lemma Ter_equiv_sym: forall A E B, Symmetric (@TerRel.equiv A E B).
Proof.
  unfold Symmetric, TerRel.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Ter_equiv_trans: forall A E B, Transitive (@TerRel.equiv A E B).
Proof.
  unfold Transitive, TerRel.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Ter_equiv_test_rel:
  Proper (@Sets.equiv State ==> @TerRel.equiv State (list Z) State) TerRel.test_rel.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, TerRel.equiv, TerRel.test_rel.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Ter_equiv_concat:
  Proper (@TerRel.equiv State (list Z) State ==> @TerRel.equiv State (list Z) State ==> @TerRel.equiv State (list Z) State) TerRel.concat.
Proof.
  unfold Proper, respectful.
  unfold TerRel.equiv, TerRel.concat.
  intros.
  unfold iff.
  split.
  + intros [b0 [l1 [l2 [? [? ?]]]]].
    exists b0, l1, l2.
    rewrite <- H, <- H0.
    tauto.
  + intros [b0 [l1 [l2 [? [? ?]]]]].
    exists b0, l1, l2.
    rewrite H, H0.
    tauto.
Qed.

Lemma Ter_equiv_union: forall A E B,
  Proper (@TerRel.equiv A E B==> @TerRel.equiv A E B ==> @TerRel.equiv A E B) TerRel.union.
Proof.
  unfold Proper, respectful.
  unfold TerRel.equiv, TerRel.union.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Ter_equiv_omega_union: forall A E B (r1 r2: nat -> A -> E -> B -> Prop),
  (forall n, TerRel.equiv (r1 n) (r2 n)) ->
  TerRel.equiv (TerRel.omega_union r1) (TerRel.omega_union r2).
Proof.
  unfold TerRel.equiv, TerRel.omega_union.
  intros.
  unfold iff; split; intros HH;
  destruct HH as [n ?]; exists n.
  + rewrite <- H.
    exact H0.
  + rewrite H.
    exact H0.
Qed.

Lemma Ter_equiv_Ter_le: forall A E B (r1 r2: A -> E -> B -> Prop),
  TerRel.equiv r1 r2 <-> TerRel.equiv r1 r2 /\ TerRel.equiv r1 r2.
Proof.
  unfold TerRel.equiv, TerRel.le.
  intros.
  unfold iff at 1.
  split; intros.
  + split; intros; rewrite H; tauto.
  + destruct H.
    unfold iff; split.
    - apply H.
    - apply H0.
Qed.

Lemma Ter_union_comm: forall A E B (r1 r2: A -> E -> B -> Prop),
  TerRel.equiv (TerRel.union r1 r2) (TerRel.union r2 r1).
Proof.
  intros.
  unfold TerRel.equiv, TerRel.union.
  intros.
  tauto.
Qed.

Lemma Ter_concat_assoc:
  forall (r1: State -> list Z -> State -> Prop) (r2: State -> list Z -> State -> Prop) (r3: State -> list Z -> State -> Prop),
  TerRel.equiv
    (TerRel.concat (TerRel.concat r1 r2) r3)
    (TerRel.concat r1 (TerRel.concat r2 r3)).
Proof.
  unfold TerRel.equiv, TerRel.concat.
  intros; split; intros.
  + destruct H as [b' [l1 [l2 ]]].
     destruct H as [[a' [l3 [l4 [? [? ?]]]]] [? ?]].
    exists a',l3,(l4++l2).
    split. auto. split.
    exists b',l4,l2.
    tauto. subst.
    rewrite app_assoc. auto.
  + destruct H as [a' [l3 [l5]]].
     destruct H as [? [[b' [l4 [l2 [? [? ?]] ]]] ?]].
    exists b',(l3++l4),l2.
    split. exists a',l3,l4. auto.
    split. auto. subst. rewrite <- app_assoc. auto.
Qed.

Existing Instances Ter_equiv_refl
                   Ter_equiv_sym
                   Ter_equiv_trans
                   Ter_equiv_test_rel
                   Ter_equiv_concat
                   Ter_equiv_union.


(*******************************************)
(*************** Syntax ********************)
(*******************************************)


Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : Cvar)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion ANum : Z >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Declare Scope imp_scope.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x == y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'!' b" := (BNot b) (at level 39, right associativity) : imp_scope.


Inductive com : Type :=
  | CSkip
  | CAss (X: Cvar) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | Unit_SG (U : Matrix 2 2) (Q : Qvar)
  | Unit_DB (U : Matrix 2 2) (Q P : Qvar)
  | Meas (X: Cvar) (Q : Qvar).

Bind Scope imp_scope with com.
Notation "'Skip'" :=
   CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (CIf c1 c2 c3) (at level 10, right associativity) : imp_scope.

(* Module Abstract_Pretty_Printing. *)
Coercion AId: Cvar >-> aexp.
Notation "x '::=' a" :=
  (CAss x a) (at level 80) : imp_scope.
(* End Abstract_Pretty_Printing. *)


(*******************************************)
(************ Denotations ******************)
(*******************************************)

Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.
Definition query_var (x: Cvar): State -> Z := fun st => fst st x.

Fixpoint aeval (a : aexp) : State -> Z :=
  match a with
  | ANum n => constant_func n
  | AId x => query_var x
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  end.

Fixpoint beval (b : bexp) : State -> Prop :=
  match b with
  | BTrue       => Sets.full
  | BFalse      => Sets.empty
  | BEq a1 a2   => Func.test_eq (aeval a1) (aeval a2)
  | BLe a1 a2   => Func.test_le (aeval a1) (aeval a2)
  | BNot b1     => Sets.complement (beval b1)
  | BAnd b1 b2  => Sets.intersect (beval b1 ) (beval b2)
  end.

Definition u_1  (U: Matrix 2 2) (q: nat) : Matrix (2^n) (2^n) := (I (2^q) ⊗ U ⊗ I (2^(n-q-1))).
Definition u_2  (U: Matrix 2 2) (q p: nat): Matrix (2^n) (2^n) := 
    (I (2^q) ⊗ (B0 ⊗ I (2^(p-q-1)) ⊗ I_2 .+ B3 ⊗ I (2^(p-q-1)) ⊗ U) ⊗ I (2^(n-p-1))).
Definition Mea0 :=  u_1 B0.
Definition Mea1 :=  u_1 B3.
(* Definition u_1 (n:nat)  (U: Matrix 2 2) (q: nat) : Matrix (2^n) (2^n) := (I (2^q) ⊗ U ⊗ I (2^(n-q-1))).
Definition u_2 (n:nat)  (U: Matrix 2 2) (q p: nat): Matrix (2^n) (2^n) := 
    (I (2^q) ⊗ (B0 ⊗ I (2^(n-q-3)) ⊗ I_2 .+ B3 ⊗ I (2^(n-q-3)) ⊗ U) ⊗ I (2^(n-p-1))).
Definition Mea0 (n:nat)  (q: nat): Matrix (2^n) (2^n) :=  (I (2^q) ⊗ B0 ⊗ I (2^(n-q-1))).
Definition Mea1 (n:nat)  (q: nat) : Matrix (2^n) (2^n) :=  (I (2^q) ⊗ B3 ⊗ I (2^(n-q-1))). *)

Definition if_sem
  (b: bexp)
  (then_branch else_branch: State -> list Z -> State -> Prop)
  : State -> list Z -> State -> Prop
:=
  TerRel.union
    (TerRel.concat (TerRel.test_rel (beval b)) then_branch)
    (TerRel.concat (TerRel.test_rel (beval (BNot b))) else_branch).


Fixpoint iter_loop_body (b: bexp)
                        (loop_body: State -> list Z -> State -> Prop)
                        (n0: nat): State -> list Z -> State -> Prop :=
  match n0 with
  | O =>
         TerRel.test_rel (beval (BNot b))
  | S n0' =>
         TerRel.concat
           (TerRel.test_rel (beval b))
           (TerRel.concat
              loop_body
              (iter_loop_body b loop_body n0'))
  end.


Definition loop_sem  (b: bexp) (loop_body : State -> list Z -> State -> Prop):
  State -> list Z -> State -> Prop :=
  TerRel.omega_union (iter_loop_body b loop_body).


Definition Pro (M ρ: Matrix (2^n) (2^n)) : C := trace (M × ρ).

Fixpoint ceval  (c : com): State -> list Z -> State -> Prop :=
  match c with
  | CSkip =>  TerRel.id
  | CAss X E => fun st1 l st2 => st2 = ((X  !-> (aeval E st1), (fst st1)) , snd st1) /\ l = []
  | CSeq c1 c2 => TerRel.concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | Unit_SG U q => fun st1 l st2 => st2 = ((fst st1),  ((u_1 U q) # (snd st1))) /\ l = []
  | Unit_DB U q p => fun st1 l st2 => st2 = ((fst st1),  ((u_2 U q p) # (snd st1))) /\ l = []
  | Meas x q => fun st1 l st2 => (st2 = ((x !-> 0, (fst st1)), ((Mea0 q) # (snd st1))) /\ l = [0]) \/
                                                                   (st2 = ((x !-> 1, (fst st1)), ((Mea1 q) # (snd st1))) /\ l = [1])
  end.


Lemma ceval_CSkip: ceval CSkip = TerRel.id.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 l st2 => st2 = ((X  !-> (aeval E st1), (fst st1)) , snd st1) /\ l = [].
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = TerRel.concat (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_Unit_SG : forall U q,
  ceval (Unit_SG U q) = fun st1 l st2 => st2 = ((fst st1),  ((u_1 U q) # (snd st1))) /\ l = [].
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_Unit_DB : forall U q p,
  ceval (Unit_DB U q p) = fun st1 l st2 => st2 = ((fst st1),  ((u_2 U q p) # (snd st1))) /\ l = [].
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_Meas : forall x q,
  ceval (Meas x q) =  fun st1 l st2 => (st2 = ((x !-> 0, (fst st1)), ((Mea0 q) # (snd st1))) /\ l = [0]) \/
                                                                   (st2 = ((x !-> 1, (fst st1)), ((Mea1 q) # (snd st1))) /\ l = [1]).
Proof. intros. simpl. reflexivity. Qed.

Arguments ceval: simpl never.


Definition aexp_equiv (a1 a2: aexp): Prop :=
  Func.equiv (aeval a1) (aeval a2).

Lemma aexp_equiv_refl: Reflexive aexp_equiv.
Proof.
  unfold Reflexive, aexp_equiv.
  intros.
  reflexivity.
Qed.

Lemma aexp_equiv_sym: Symmetric aexp_equiv.
Proof.
  unfold Symmetric, aexp_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma aexp_equiv_trans: Transitive aexp_equiv.
Proof.
  unfold Transitive, aexp_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma APlus_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) APlus.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma AMinus_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) AMinus.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma AMult_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) AMult.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Existing Instances aexp_equiv_refl
                   aexp_equiv_sym
                   aexp_equiv_trans
                   APlus_congr
                   AMinus_congr
                   AMult_congr.


Definition bexp_equiv (b1 b2: bexp): Prop :=
  Sets.equiv (beval b1) (beval b2).

Lemma bexp_equiv_refl: Reflexive bexp_equiv.
Proof.
  unfold Reflexive, bexp_equiv.
  intros.
  reflexivity.
Qed.

Lemma bexp_equiv_sym: Symmetric bexp_equiv.
Proof.
  unfold Symmetric, bexp_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma bexp_equiv_trans: Transitive bexp_equiv.
Proof.
  unfold Transitive, bexp_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BEq_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BEq.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BLe_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BLe.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BAnd_congr:
  Proper (bexp_equiv ==> bexp_equiv ==> bexp_equiv) BAnd.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BNot_congr: Proper (bexp_equiv ==> bexp_equiv) BNot.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv.
  intros; simpl.
  rewrite H.
  reflexivity.
Qed.

Existing Instances bexp_equiv_refl
                   bexp_equiv_sym
                   bexp_equiv_trans
                   BEq_congr
                   BLe_congr
                   BAnd_congr
                   BNot_congr.

Definition com_equiv (c1 c2: com): Prop :=
  TerRel.equiv (ceval c1) (ceval c2).

Lemma com_equiv_refl: Reflexive com_equiv.
Proof.
  unfold Reflexive, com_equiv.
  intros.
  reflexivity.
Qed.

Lemma com_equiv_sym: Symmetric com_equiv.
Proof.
  unfold Symmetric, com_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma com_equiv_trans: Transitive com_equiv.
Proof.
  unfold Transitive, com_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma CAss_congr: forall (X: Cvar),
  Proper (aexp_equiv ==> com_equiv) (CAss X).
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, com_equiv, TerRel.equiv.
  intros X E E' ?.
  intros st1 st2.
  rewrite ! ceval_CAss.
  unfold Func.equiv in H.
  specialize (H st1).
  rewrite H.
  reflexivity.
Qed.

Lemma CSeq_congr: Proper (com_equiv ==> com_equiv ==> com_equiv) CSeq.
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros c1 c1' ? c2 c2' ?.
  rewrite ! ceval_CSeq.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma CIf_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv ==> com_equiv) CIf.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c1 c1' ? c2 c2' ?.
  rewrite ! ceval_CIf.
  unfold if_sem.
  simpl.
  rewrite H, H0, H1.
  reflexivity.
Qed.

Lemma CWhile_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv) CWhile.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c c' ?.
  rewrite ! ceval_CWhile.
  unfold loop_sem.
  apply Ter_equiv_omega_union.
  intros.
  induction n0; simpl.
  + rewrite H.
    reflexivity.
  + rewrite IHn0, H, H0.
    reflexivity.
Qed.


Lemma loop_sem_unrolling: forall b (r: State -> list Z -> State -> Prop),
  TerRel.equiv (loop_sem b r) (if_sem b (TerRel.concat r (loop_sem b r)) TerRel.id).
Proof.
  intros.
  unfold TerRel.equiv; intros st1 l st2.
  unfold iff; split; intros.
  + unfold loop_sem, TerRel.omega_union in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, TerRel.union.
      right; simpl.
      unfold TerRel.concat, TerRel.id.
      unfold TerRel.test_rel in H. destruct H as [? [? ?]]. subst.
      exists st2,[],[]. unfold TerRel.test_rel.
      firstorder.
    - simpl in H.
      unfold if_sem, TerRel.union.
      left.
      unfold TerRel.concat in H.
      unfold TerRel.concat.
      destruct H as [st1' [l1 [l2]]].
      destruct H as [? [[st1'' [l3 [l4 [? [? ?]]]]] ?]].
      exists st1',l1,l2.
      split. auto. split. exists st1'',l3,l4. firstorder. firstorder.
  + unfold if_sem, union in H.
    unfold loop_sem, TerRel.omega_union.
    destruct H.
    2: {
      exists 0%nat.
      simpl. simpl in H.
      unfold TerRel.concat, TerRel.id in H.
      destruct H as [st2' [l1 [[] [? [[? ?] ?]]]]]. subst.
      firstorder. subst. auto. subst. rewrite H1. rewrite app_nil_r. auto.
    }
    unfold TerRel.concat at 1 in H.
    destruct H as [st1' [l0 [l1 [? [? ?]]]]].
    unfold TerRel.concat in H0.
    destruct H0 as [st1'' [l2 [l3 [? [? ?]]]]].
    unfold loop_sem, TerRel.omega_union in H3.
    destruct H2 as [n ?].
    exists (S n).
    simpl.
    unfold TerRel.concat at 1.
    exists st1',l0,(l2++l3).
    split. auto. unfold TerRel.concat. split.
    exists st1'',l2,l3. subst. firstorder. subst. auto.
Qed.

Theorem loop_unrolling : forall b c,
  com_equiv
    (While b Do c EndWhile)
    (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf).
Proof.
  intros.
  unfold com_equiv.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

Lemma seq_assoc : forall c1 c2 c3,
  com_equiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  unfold com_equiv.
  rewrite ! ceval_CSeq.
  apply Ter_concat_assoc.
Qed.

