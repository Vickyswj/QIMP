Require Export Nat_Dirac.

Open Scope nat_scope.

Module Func.

Open Scope Z_scope.

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



Definition Cvar: Type := nat.
Definition Qvar: Type := nat.

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
  | Unit_SG (U : Matrix 2 2) (Q : Qvar) (n : nat)
  | Unit_DB (U : Matrix 2 2) (Q P : Qvar) (n : nat)
  | Meas (X: Cvar) (Q : Qvar) (n : nat).

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



Definition CState : Type :=  nat -> Z.
Definition QState n : Type :=  Square (2^n).

Definition State n := (CState * QState n)%type.

Definition empty_CState : CState :=
  (fun _ => 0%Z).

Notation "'_' '!->' 0" := (empty_CState)
  (at level 100, right associativity).

Definition Qint n : Square (2^n) := 
fun x y => 
match x, y with 
          | O, O => C1
          | _, _ => C0
          end.

Definition empty_QState n : QState n := Qint n.  (* cangbucang? *)

Definition update_CState (cst : CState) (x : Cvar) (z : Z) : CState :=
  (fun x' => if Nat.eq_dec x x' then z else cst x').

Notation "x '!->' v ',' cst" := (update_CState cst x v)
                              (at level 100, v at next level, right associativity).

Notation "x '!->' v" := (x !-> v , empty_CState) (at level 100).

Lemma update_CState_shadow : forall (m : CState) x v1 v2,
  (x !-> v2 , x !-> v1 , m) = (x !-> v2 , m).
Proof.
  intros. unfold update_CState. apply functional_extensionality.
  intros. destruct (Nat.eq_dec x x0). reflexivity. reflexivity.
Qed.

Definition update_QState {n} (qst : QState n) (U : Square (2^n)) : QState n := super U qst.

Notation " U '#' qst " := (update_QState qst U)
                              (at level 100, right associativity).

Definition update_State {n} (st : State n) (x : Cvar) (z : Z) (U : Square (2^n)) : State n :=
((x !-> z , (fst st)) , (U # (snd st))).


Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.
Definition query_var {n} (x: Cvar): State n -> Z := fun st => fst st x.

Fixpoint aeval {n} (a : aexp) : State n -> Z :=
  match a with
  | ANum n => constant_func n
  | AId x => query_var x
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  end.

Fixpoint dbeval {n} (b : bexp) (st : State n) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => Z.eqb (aeval a1 st) (aeval a2 st)
  | BLe a1 a2   => Z.leb (aeval a1 st) (aeval a2 st)
  | BNot b1     => negb (dbeval b1 st)
  | BAnd b1 b2  => (dbeval b1 st) && (dbeval b2 st)
  end.


Definition DState n : Type := list (State n).

Inductive eq_DS {n} : DState n ->DState n -> Prop :=
  | eq_DS_nil : eq_DS nil nil
  | eq_DS_cons : forall c q c' q' d d',
       c = c' -> q ≡ q' -> eq_DS d d' -> eq_DS ((c,q)::d) ((c',q')::d').

Infix ".=" := eq_DS (at level 70).


Definition DC {n} (st : State n) (x: Cvar) (a : aexp) : State n :=
((x !-> (aeval a st), (fst st)), snd st).

Fixpoint dist_update_C {n} (dst : DState n) (x: Cvar) (a : aexp) : DState  n:=   (*Z?*)
  match dst with
  | [] => []
  | st :: dst1 => DC st x a :: (dist_update_C dst1 x a)
  end.

Definition DQ {n} (st : State n) (U: Square (2^n)) : State n :=
(fst st, (U # (snd st))).

Fixpoint dist_update_Q {n} (dst : DState n) (U: Square (2^n)) : DState n :=
  match dst with
  | [] => []
  | st :: dst1 => DQ st U :: (dist_update_Q dst1 U)
  end.

Fixpoint dist_update_State {n} (dst : DState n) (x: Cvar) (a : aexp) (U: Square (2^n)) : DState n :=
  match dst with
  | [] => []
  | st :: dst1 => (update_State st x (aeval a st) U) :: (dist_update_State dst1 x a U)
  end.

Module BinRel.

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition merge {n} (r1 r2: DState n -> DState n -> Prop): DState n -> DState n -> Prop :=
  fun a b => exists b1 b2, r1 a b1 /\  r2 a b2 /\ b = b1 ++ b2.

Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition test_rel {n} (X: State n -> bool) : DState n -> DState n -> Prop  :=
fun dst1 dst2 =>  dst2 = filter X dst1.

Definition test_rel' {n} (X: State n -> bool) : DState n -> DState n -> Prop  :=
fun dst1 dst2 => dst2 = filter X dst1 /\ dst2 <> [].

Definition test_rel'' {n} (X: State n -> bool) : DState n -> DState n -> Prop  :=
fun dst1 dst2 => dst2 = filter X dst1 /\ dst2 = dst1.

Definition equiv {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b <-> r2 a b.

Definition le {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b -> r2 a b.

End BinRel.

Definition if_sem {n}
   (b: bexp)
  (then_branch else_branch: DState n -> DState n -> Prop)
  : DState n -> DState n -> Prop
:=
  BinRel.merge
    (BinRel.concat (BinRel.test_rel (dbeval b)) then_branch)
    (BinRel.concat (BinRel.test_rel (dbeval (BNot b))) else_branch).


Fixpoint iter_loop_body {n} (b: bexp)
                        (loop_body: DState n -> DState n -> Prop)
                        (n0: nat): DState n -> DState n -> Prop :=
  match n0 with
  | O =>
         BinRel.test_rel'' (dbeval (BNot b))
  | S n0' =>
        (BinRel.concat (BinRel.merge
           (BinRel.concat (BinRel.test_rel' (dbeval b)) loop_body)
           (BinRel.test_rel (dbeval (BNot b))))
              (iter_loop_body b loop_body n0'))
  end.

Definition loop_sem {n} (b: bexp) (loop_body : DState n -> DState n -> Prop):
  DState n -> DState n -> Prop :=
  BinRel.omega_union (iter_loop_body b loop_body).

Definition u_1  (U: Matrix 2 2) q n : Matrix (2^n) (2^n) := (I (2^q) ⊗ U ⊗ I (2^(n-q-1))).
Definition u_2  (U: Matrix 2 2) q p n : Matrix (2^n) (2^n) := 
    (I (2^q) ⊗ (B0 ⊗ I (2^(p-q-1)) ⊗ I_2 .+ B3 ⊗ I (2^(p-q-1)) ⊗ U) ⊗ I (2^(n-p-1))).
Definition Mea0 :=  u_1 B0.
Definition Mea1 :=  u_1 B3.

Fixpoint dceval {n} (c : com): DState n -> DState n -> Prop :=
  match c with
  | CSkip =>  BinRel.id
  | CAss X E => fun dst1 dst2 => dst2 .= dist_update_C dst1 X E

  | CSeq c1 c2 => BinRel.concat (dceval c1) (dceval c2)
  | CIf b c1 c2 => if_sem b (dceval c1) (dceval c2)
  | CWhile b c => loop_sem b (dceval c)
(*   | QInt => fun dst1 dst2 => dst2 = dist_update_Q dst1 (kron_n n ∣0⟩⟨0∣) *)
  | Unit_SG U q n => fun dst1 dst2 => dst2 .= dist_update_Q dst1 (u_1 U q n)
  | Unit_DB U q p n => fun dst1 dst2 => dst2 .= dist_update_Q dst1 (u_2 U q p n)
  | Meas x q n => fun dst1 dst2 => dst2 .= (* dist_update_State_ZM dst1 x q. *)
  (dist_update_State dst1 x 0%Z (Mea0 q n)) ++ (dist_update_State dst1 x 1%Z (Mea1 q n))
  end.


Lemma dceval_CSkip {n} : @dceval n CSkip = BinRel.id.
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CAss {n} : forall X E,
  @dceval n (CAss X E) = fun dst1 dst2 => dst2 .= dist_update_C dst1 X E.
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CSeq {n} : forall c1 c2,
  @dceval n (c1 ;; c2) = BinRel.concat (dceval c1) (dceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CIf {n} : forall b c1 c2,
  @dceval n (CIf b c1 c2) = if_sem b (dceval c1) (dceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CWhile {n} : forall b c,
  @dceval n (While b Do c EndWhile) = loop_sem b (dceval c).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_Unit_SG : forall  n U q,
  dceval (Unit_SG U q n) = fun dst1 dst2 => dst2 .= dist_update_Q dst1 (u_1 U q n).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_Unit_DB : forall  n U q p,
  dceval (Unit_DB U q p n) = fun dst1 dst2 => dst2 .= dist_update_Q dst1 (u_2 U q p n).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_Meas : forall n x q,
  dceval (Meas x q n) =  fun dst1 dst2 => dst2 .= (* dist_update_State_ZM dst1 x q. *)
  (dist_update_State dst1 x 0%Z (Mea0 q n)) ++ (dist_update_State dst1 x 1%Z (Mea1 q n)).
Proof. intros. simpl. reflexivity. Qed.

Arguments dceval: simpl never.