Require Export Denotations.
Require Export Nat_Dirac.


Open Scope Z_scope.

Definition DState : Type := list State.


Module BinRel.

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition empty {A B: Type}: A -> B -> Prop := fun a b => False.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.

Definition union {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b \/ r2 a b.

Definition intersection {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b /\ r2 a b.

Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition test_rel (X: State -> bool) : DState -> DState -> Prop  :=
fun dst1 dst2 =>  dst2 = filter X dst1.

Definition test_rel' (X: State -> bool) : DState -> DState -> Prop  :=
fun dst1 dst2 => dst2 = filter X dst1 /\ dst2 <> [].

Definition test_rel'' (X: State -> bool) : DState -> DState -> Prop  :=
fun dst1 dst2 => dst2 = filter X dst1 /\ dst2 = dst1.

Definition merge (r1 r2: DState -> DState -> Prop): DState -> DState -> Prop :=
  fun a b => exists b1 b2, r1 a b1 /\  r2 a b2 /\ b = b1 ++ b2.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition equiv {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b <-> r2 a b.

Definition le {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b -> r2 a b.

End BinRel.

Fixpoint dbeval  (b : bexp) (st : State) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => Z.eqb (aeval a1 st) (aeval a2 st)
  | BLe a1 a2   => Z.leb (aeval a1 st) (aeval a2 st)
  | BNot b1     => negb (dbeval b1 st)
  | BAnd b1 b2  => (dbeval b1 st) && (dbeval b2 st)
  end.


Definition DC (st : State) (x: Cvar) (a : aexp) : State :=
((x !-> (aeval a st), (fst st)), snd st).

Fixpoint dist_update_C  (dst : DState) (x: Cvar) (a : aexp) : DState :=   (*Z?*)
  match dst with
  | [] => []
  | st :: dst1 => DC st x a :: (dist_update_C dst1 x a)
  end.

Lemma in_map_c :
  forall dst st x a, In st dst -> In (DC st x a) (dist_update_C dst x a).
Proof.
  intro l; induction l; firstorder (subst; auto).
Qed.

  Lemma in_map_iff_c : forall dst st x a, In st (dist_update_C dst x a) <-> exists st0, (DC st0 x a) = st /\ In st0 dst.
  Proof.
    intro l.
    induction l.
    simpl. firstorder.
    simpl.
    intros. split.
    intros.
    inversion H.
    exists a. auto.
    rewrite IHl in H0. destruct H0 as [st0 [? ?]].
    exists st0. split. auto. right. auto.
    intros.
    destruct H as [st0 [? ?]].
    inversion H0.
    rewrite H1. left. auto.
    right. rewrite IHl.
    exists st0. auto.
  Qed.

Definition DQ (st : State) (U: Square (2^n)) : State :=
(fst st, (U # (snd st))).

Fixpoint dist_update_Q  (dst : DState) (U: Square (2^n)) : DState :=
  match dst with
  | [] => []
  | st :: dst1 => DQ st U :: (dist_update_Q dst1 U)
  end.

Fixpoint dist_update_State  (dst : DState) (x: Cvar) (a : aexp) (U: Square (2^n)) : DState :=
  match dst with
  | [] => []
  | st :: dst1 => (update_State st x (aeval a st) U) :: (dist_update_State dst1 x a U)
  end.

Definition if_sem
   (b: bexp)
  (then_branch else_branch: DState -> DState -> Prop)
  : DState -> DState -> Prop
:=
  BinRel.merge
    (BinRel.concat (BinRel.test_rel (dbeval b)) then_branch)
    (BinRel.concat (BinRel.test_rel (dbeval (BNot b))) else_branch).


Fixpoint iter_loop_body  (b: bexp)
                        (loop_body: DState -> DState -> Prop)
                        (n0: nat): DState -> DState -> Prop :=
  match n0 with
  | O =>
         BinRel.test_rel'' (dbeval (BNot b))
  | S n0' =>
        (BinRel.concat (BinRel.merge
           (BinRel.concat (BinRel.test_rel' (dbeval b)) loop_body)
           (BinRel.test_rel (dbeval (BNot b))))
              (iter_loop_body b loop_body n0'))
  end.


Definition loop_sem  (b: bexp) (loop_body : DState -> DState -> Prop):
  DState -> DState -> Prop :=
  BinRel.omega_union (iter_loop_body b loop_body).

Fixpoint dceval  (c : com): DState -> DState -> Prop :=
  match c with
  | CSkip =>  BinRel.id
  | CAss X E => fun dst1 dst2 => dst2= dist_update_C dst1 X E

  | CSeq c1 c2 => BinRel.concat (dceval c1) (dceval c2)
  | CIf b c1 c2 => if_sem b (dceval c1) (dceval c2)
  | CWhile b c => loop_sem b (dceval c)
(*   | QInt => fun dst1 dst2 => dst2 = dist_update_Q dst1 (kron_n n ∣0⟩⟨0∣) *)
  | Unit_SG U q => fun dst1 dst2 => dst2 = dist_update_Q dst1 (u_1 U q)
  | Unit_DB U q p => fun dst1 dst2 => dst2 = dist_update_Q dst1 (u_2 U q p)
  | Meas x q => fun dst1 dst2 => dst2 = (* dist_update_State_ZM dst1 x q. *)
  (dist_update_State dst1 x 0 (Mea0 q)) ++ (dist_update_State dst1 x 1 (Mea1 q))
  end.

Lemma dceval_CSkip: dceval CSkip = BinRel.id.
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CAss: forall X E,
  dceval (CAss X E) =
fun dst1 dst2 => dst2= dist_update_C dst1 X E.
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CSeq: forall c1 c2,
  dceval (c1 ;; c2) = BinRel.concat (dceval c1) (dceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CIf: forall b c1 c2,
  dceval (CIf b c1 c2) = if_sem b (dceval c1) (dceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_CWhile: forall b c,
  dceval (While b Do c EndWhile) = loop_sem b (dceval c).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_Unit_SG: forall U q,
  dceval (Unit_SG U q) = fun dst1 dst2 => dst2 = dist_update_Q dst1 (u_1 U q).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_Unit_DB: forall U q p,
  dceval (Unit_DB U q p) = fun dst1 dst2 => dst2 = dist_update_Q dst1 (u_2 U q p).
Proof. intros. simpl. reflexivity. Qed.

Lemma dceval_Meas : forall x q,
  dceval (Meas x q) = fun dst1 dst2 =>  dst2 = (* dist_update_State_ZM dst1 x q. *)
  (dist_update_State dst1 x 0 (Mea0 q)) ++ (dist_update_State dst1 x 1 (Mea1 q)).
Proof. intros. simpl. reflexivity. Qed.

Require Import Permutation.

Section Preparation.

Variables (X Y : Type) (R : X -> Y -> Prop) (f : X -> bool) (P : X->Prop).

Fact cons_app (a:X) (l:list X) : a :: l = [a] ++ l.
Proof. simpl. auto. Qed.

Lemma Forall_cons_iff : forall (a:X) l, Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  split.
  intros. split; inversion H; trivial.
  intros. apply Forall_cons; firstorder.
Qed.


Ltac do_one_match_then matcher do_tac tac :=
  idtac;
  match goal with
  | [ H : ?T |- _ ]
    => matcher T; do_tac H;
       try match type of H with
           | T => clear H
           end;
       tac
  end.

Ltac inversion_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => inversion H; subst) tac.

Ltac inversion_one_match matcher := inversion_one_match_then matcher ltac:( simpl in * ).

Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

Ltac destruct_head_matcher T HT :=
  match head HT with
  | T => idtac
  end.

Ltac inversion_one_head T := inversion_one_match ltac:(destruct_head_matcher T).

Lemma Forall2_cons_cons_iff A B Q x xs y ys
  : @Forall2 A B Q (cons x xs) (cons y ys) <-> (Q x y /\ Forall2 Q xs ys).
Proof using Type. split; firstorder (inversion_one_head Forall2; eauto). Qed.

Lemma Forall2_cons_l_ex_iff A B Q x xs ls
  : @Forall2 A B Q (cons x xs) ls <-> (exists y ys, ls = cons y ys /\ Q x y /\ Forall2 Q xs ys).
Proof using Type. split; firstorder (inversion_one_head Forall2; eauto). Qed.

Lemma Forall2_cons_r_ex_iff A B Q x xs ls
  : @Forall2 A B Q ls (cons x xs) <-> (exists y ys, ls = cons y ys /\ Q y x /\ Forall2 Q ys xs).
Proof using Type. split; firstorder (inversion_one_head Forall2; eauto). Qed.


Lemma Permutation_concat l l' :
  Permutation l l' -> Permutation (@concat X l) (@concat X l').
Proof with auto.
  repeat intro.
  induction H...
      simpl.
      apply Permutation_app...
    simpl.
    repeat rewrite <- app_ass.
    apply Permutation_app...
    apply Permutation_app_swap.
    apply Permutation_trans with (concat l').
  eauto. eauto.
Qed.


Lemma filter_cons a l:
filter f (a::l) = (a:: l) -> f a = true -> filter f l = l.
Proof.
    cbn. destruct (f a); auto; congruence.
Qed.

Hint Rewrite @app_nil_l @app_nil_r @last_last @rev_app_distr : listsimpl.

Ltac listsimpl := autorewrite with listsimpl.

Lemma split_app {A B} (l1 l2 : list (A * B)) :
    List.split (l1 ++ l2) = (fst (List.split l1) ++ fst (List.split l2),
                        snd (List.split l1) ++ snd (List.split l2)).
  Proof.
    revert l2; induction l1; destruct l2;
      repeat first [ progress cbn [List.split fst snd]
                   | progress listsimpl
                   | rewrite <-app_comm_cons
                   | match goal with
                     | |- context [match ?p with pair _ _ => _ end] =>
                       rewrite (surjective_pairing p)
                     end
                   | rewrite IHl1; clear IHl1
                   | reflexivity ].
  Qed.

Lemma split_cons: forall {A B} (l:list (A*B))(x:A*B),
    List.split (x :: l) = (fst x :: fst (List.split l),
                        snd x :: snd (List.split l)).
  Proof.
      intros. induction l.
      + simpl. destruct x as [a0 b]. simpl. auto.
      + simpl in *. destruct x as [a0 b]. destruct a. destruct (List.split l).
          simpl in *. auto.
  Qed.

End  Preparation.

Section NoPrefix.
Set Implicit Arguments.

Variable X : Type.

Definition NoPrefix (l1 l2 : list X): Prop :=
(~ exists l, l1 ++ l = l2) /\ (~ exists l,  l2 ++ l = l1).

Inductive MNP : list (list X) -> Prop :=
  |MNP_nil : MNP [] 
  |MNP_cons : forall x l, Forall (NoPrefix x) l -> MNP l -> MNP (x::l).


Lemma MNP_app (a b: list (list X)): MNP a -> MNP b ->
  (forall x, In x a -> Forall (NoPrefix x) b) -> MNP (a ++ b).
Proof with auto.
  induction a...
  intros.
  simpl.
  inversion_clear H.
  apply MNP_cons.
  apply Forall_app.
  split. auto.
  apply H1. simpl. auto.
  apply IHa. auto. auto.
  intros. apply H1. simpl. auto.
Qed.

Theorem MNP_cons_iff (a : list X) (l : list (list X)):
  MNP (a :: l) <-> Forall (NoPrefix a) l /\ MNP l.
Proof.
  split.
  + inversion_clear 1. now split.
  + now constructor.
Qed.

(* Lemma error1 :
NoPrefix [] [].
Lemma error2 : forall l,
NoPrefix [] l . *)

Lemma NoPrefix_comm : forall l1 l2,
NoPrefix l1 l2 ->
NoPrefix l2 l1.
Proof.
intros.
unfold NoPrefix in *.
destruct H.
split. auto. auto.
Qed.

Lemma NoPrefix_nil_l : forall l,
~ NoPrefix [] l.
Proof.
intros.
unfold NoPrefix.
apply or_not_and.
left. unfold not. intros. apply H.
exists l. auto.
Qed.

Lemma NoPrefix_nil_r : forall l,
~ NoPrefix l [].
Proof.
intros.
unfold NoPrefix.
apply or_not_and.
right. unfold not. intros. apply H.
exists l. auto.
Qed.

Lemma Prefix_a : forall (l1 l3 l2 : list X) a,
l1 ++ l2 = l3 ++ [a] ->
(exists l, l1 ++ l = l3) \/ (exists l, l3 ++ l = l1).
Proof.
induction l1.
+ intros. left. exists l3. auto.
+ induction l3. 
   - intros. right. exists (a :: l1). auto.
   - intros.
      rewrite <- app_comm_cons in H.
      rewrite <- app_comm_cons in H.
      inversion H.
     pose proof IHl1 l3 l2 a1 H2.
    destruct H0.
    * left.
       destruct H0.
       exists x.
       rewrite <- app_comm_cons. subst. auto.
    * right.
       destruct H0.
       exists x.
       rewrite <- app_comm_cons.
       subst.
       auto.
Qed.

Lemma app_NoPrefix_l : forall l l1 l2,
NoPrefix l1 l2 ->
NoPrefix (l1 ++ l) l2.
Proof.
intros l.
induction l.
+ intros. rewrite <- app_nil_end. auto.
+ intros.
    rewrite cons_app.
    rewrite app_assoc.
    apply IHl. clear IHl.
    unfold NoPrefix in *.
    destruct H.
    split.
    - unfold not in *.
       intros. apply H.
       destruct H1 as [l'].
       exists ([a] ++ l').
       rewrite app_assoc. auto.
    - unfold not in *.
       intros. destruct H1 as [l'].
       pose proof Prefix_a l2 l1 l' a H1.
       destruct H2.
       apply H0. auto.
       apply H. auto.
Qed.

Lemma app_NoPrefix : forall l1 l2 l3 l4,
NoPrefix l1 l2 ->
NoPrefix (l1 ++ l3) (l2 ++ l4).
Proof.
intros.
apply app_NoPrefix_l.
apply NoPrefix_comm.
apply app_NoPrefix_l.
apply NoPrefix_comm.
auto.
Qed.

Lemma app_NoPrefix_head : forall l0 l1 l2,
NoPrefix l1 l2 ->
NoPrefix (l0 ++ l1) (l0 ++ l2).
Proof.
intros l0.
induction l0.
+ intros. simpl. auto.
+ intros. simpl. unfold NoPrefix.
    pose proof IHl0 l1 l2 H.
    unfold NoPrefix in H0.
    destruct H0.
    split. unfold not in H0. unfold not. intros. apply H0.
    destruct H2 as [l]. exists l. 
    rewrite <- app_comm_cons in H2.
    rewrite cons_app in H2.
    pose proof cons_app X a (l0 ++ l2).
    rewrite H3 in H2.
    apply app_inv_head_iff in H2. auto.
    unfold not in H1. unfold not. intros. apply H1.
    destruct H2 as [l]. exists l. 
    rewrite <- app_comm_cons in H2.
    rewrite cons_app in H2.
    pose proof cons_app X a (l0 ++ l1).
    rewrite H3 in H2.
    apply app_inv_head_iff in H2. auto.
Qed.

End NoPrefix.


Fixpoint prepre0 (a : list Z * State) (c : list (list Z * State)) : list (list Z * State) :=
match c with
| [] => @nil (list Z * State)
| e :: f => (((fst a) ++ (fst e)), snd e) :: prepre0 a f
end.

Fixpoint prepre1 (y : list (list Z * State)) (l1' : list (list (list Z * State))) : list (list (list Z * State)) :=
match l1' with
| nil => nil
| c :: d => match y with
                   | nil => l1'
                   | a :: b => prepre0 a c :: prepre1 b d
                   end
end.

Fixpoint prepre2 (dst : list State) : list (list (list Z * State)) :=
match dst with
| [] => @nil (list (list Z * State))
| a:: b => [([],a)] :: prepre2 b
end.

Fixpoint prepre3 (dst : list State) Q X0 : list (list (list Z * State)) :=
match dst with
| [] => @nil (list (list Z * State))
| a:: b => [([0], (X0 !-> 0, fst a, Mea0 Q # snd a));
([1], (X0 !-> 1, fst a, Mea1 Q # snd a))] :: prepre3 b Q X0
end.


Lemma pre0 : forall l, prepre1 l [] = [] .
Proof. intros. destruct l; auto. Qed.

Lemma pre1 : forall l, prepre1 [] l = l .
Proof. intros. destruct l; auto. Qed.

Lemma pre2 : forall a l, map snd (prepre0 a l) = map snd l.
Proof.
intros. induction l.
+ simpl. auto.
+ simpl.  rewrite IHl. auto.
Qed.

Lemma pre3 : forall y l, map snd (concat (prepre1 y l)) = map snd (concat l).
Proof.
      intro y; induction y.
      intros. rewrite pre1. auto.
      intro l; destruct l.
      simpl. auto.
      simpl. rewrite map_app. rewrite map_app.
      rewrite IHy. apply app_inv_tail_iff.
      rewrite pre2. auto.
Qed.

Lemma pre4 : forall x l1 l2 b st2,
In (l2, st2) x ->
In (l1 ++ l2, st2) (prepre0 (l1, b) x).
Proof.
intros x.
induction x.
simpl. auto.
intros. inversion H.
subst. simpl. left. auto.
simpl. right. apply IHx. auto.
Qed.

Lemma pre5 : forall y l'0  l1 l2 b st2 c2,
Forall2
        (fun (st1 : State) (sts : list (list Z * State)) =>
              MNP (fst (List.split sts)) /\
         (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts)) (map snd y) l'0
-> ceval c2 b l2 st2 -> In (l1, b) y
-> In (l1 ++ l2, st2) (concat (prepre1 y l'0)).
Proof.
intros y.
induction y.
+ intros. inversion H1.
+ intros l'0. destruct l'0.
   - intros. inversion H.
   - intros. simpl. simpl in H.
      apply Forall2_cons_cons_iff in H.
      destruct H as [[? ?] ?].
      inversion H1.
     * apply in_or_app.
        left. specialize (H2 l2 st2).
        subst. simpl in H2.
        apply H2 in H0. apply pre4. auto.
     * apply in_or_app.
        right. specialize (IHy l'0 l1 l2 b st2 c2 H3 H0 H4). auto.
Qed.

Lemma pre6 : forall l' l1 l o1 st,
In (l, st) (prepre0 (l1, o1) l') ->
 exists l2,  l1 ++ l2 = l /\ (In (l2, st) l').
Proof.
intros.
induction l'.
inversion H.
simpl in H.
destruct a as [l2 o2].
simpl in H.
destruct H.
inversion H.
exists l2. simpl. auto.
apply IHl' in H.
destruct H as [l3[? ?]].
exists l3. simpl. auto.
Qed.

Lemma pre7 : forall y l' l st2 c1 c2 a,
(forall (l : list Z) (st2 : State), In (l, st2) y -> ceval c1 a l st2) ->
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
              MNP (fst (List.split sts)) /\
        (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts)) (map snd y) l' ->
In (l, st2) (concat (prepre1 y l')) ->
exists (b : State) (l1 l2 : list Z), ceval c1 a l1 b /\ ceval c2 b l2 st2 /\ l = l1 ++ l2.
Proof.
intros y.
induction y as [ | a1 y].
+ intros. inversion H0. subst. inversion H1.
+ intros. destruct l' as [ | p l'].
             - inversion H0.
             - simpl in H0,H1.
                   apply Forall2_cons_cons_iff in H0.
                   destruct H0 as [[? ?] ?].
                   apply in_app_or in H1.
                   destruct H1.
                       * destruct a1 as [l1 o].
                          specialize (H l1 o).
                          pose proof pre6 p l1 l o st2 H1.
                          destruct H4 as [l2 [? ?]].
                          specialize (H2 l2 st2). rewrite <- H2 in H5.
                          exists o,l1,l2.
                          split. apply H. simpl. auto. auto.
                     * specialize (IHy l' l st2 c1 c2 a).
                          apply IHy.
                          ++ intros. apply H. simpl. auto.
                          ++ auto. ++ auto.
Qed.

Lemma pre8 : forall l l0 l1 o0,
Forall (NoPrefix l1) (fst (List.split l))
-> Forall (NoPrefix (l0 ++ l1)) (fst (List.split (prepre0 (l0, o0) l))).
Proof.
intros l.
induction l.
+ intros. simpl in *. auto.
+ intros.
   destruct a as [l2 o2].
   Opaque List.split.
   simpl in *.
   rewrite split_cons in H. simpl in H.
   rewrite Forall_cons_iff in H.
   destruct H.
   rewrite split_cons. simpl.
   apply Forall_cons_iff.
   split.
   apply app_NoPrefix_head. auto.
   apply IHl. auto.
Qed.

Lemma pre9 : forall l a,
MNP (fst (List.split l)) -> 
MNP (fst (List.split (prepre0 a l))).
Proof.
intros l.
induction l.
+ intros. simpl. apply MNP_nil.
+ intros.
   destruct a0 as [l0 o0].
   destruct a as [l1 o1].
   rewrite split_cons in H. simpl in H.
   apply MNP_cons_iff in H.
   destruct H.
   simpl.
   rewrite split_cons. simpl.
   apply MNP_cons_iff.
   split. apply pre8. auto.
   apply IHl. auto.
Qed.

Lemma pre11 : forall l0 l1 o1 x l2 (a : list Z * State),
In x (fst (List.split (prepre0 (l1, o1) l0))) ->
NoPrefix l1 l2 ->
NoPrefix x (l2 ++ fst a).
Proof.
intros l0.
induction l0.
+ intros. inversion H.
+ intros. simpl in *.
                  rewrite split_cons in H. simpl in H.
                  destruct H.
                  - subst. apply app_NoPrefix. auto.
                  - pose proof IHl0 l1 o1 x l2 a0 H. auto.
Qed.

Lemma pre12 :forall l' l l1 l2 o1 o2 x,
NoPrefix l1 l2 ->
In x (fst (List.split (prepre0 (l1, o1) l))) ->
Forall (NoPrefix x) (fst (List.split (prepre0 (l2, o2) l'))).
Proof.
intros l.
induction l.
+ intros. Transparent List.split. simpl. auto.
+ intros.
    Opaque List.split. simpl in *.
                       rewrite split_cons in *. simpl in *.
                       apply Forall_cons_iff.
                       split.
                       - pose proof pre11 l0 o1 x a H0 H. auto.
                       - pose proof IHl l0 l1 l2 o1 o2 x H. auto.
Qed.

Lemma pre13 : forall y l' x a l c2,
In x (fst (List.split (prepre0 a l))) ->
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
             MNP (fst (List.split sts)) /\
        (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts))
       (map snd y) l' ->
Forall (NoPrefix (fst a)) (fst (List.split y)) ->
Forall (NoPrefix x) (fst (List.split (concat (prepre1 y l')))).
Proof.
intros y.
induction y.
+ intros. inversion H0. subst. simpl.
    Transparent List.split. simpl. auto.
+ intros. destruct l'.
     - simpl. auto.
     - simpl.
        rewrite split_app. simpl.
        simpl in H0.
        apply Forall2_cons_cons_iff in H0.
        destruct H0 as [[? ?] ?].
        apply Forall_app.
        Opaque List.split.
        rewrite split_cons in H1. simpl in H1.
        apply Forall_cons_iff in H1.
        destruct H1.
        split.
        * destruct a0 as [l1 o1].
           destruct a as [l2 o2].
           simpl in *.
           pose proof pre12 l0 l o1 o2 x H1 H.
           auto.
        * specialize (IHy l' x a0 l c2 H H3 H4). auto.
Qed.

Lemma pre14 : forall y l' c2,
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
              MNP (fst (List.split sts)) /\
       (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts)) (map snd y) l' ->
MNP (fst (List.split y)) ->
MNP (fst (List.split (concat (prepre1 y l')))).
Proof.
intros y.
induction y.
+ intros. inversion H. subst. simpl. auto.
+ intros. destruct l'.
                    - intros. inversion H.
                    - Opaque List.split.
                       simpl in *.
                       apply Forall2_cons_cons_iff in H.
                       destruct H as [[? ?] ?].
                       rewrite split_cons in H0. rewrite split_app. simpl in *.
                       apply MNP_cons_iff in H0.
                       destruct H0.
                       apply MNP_app.
                       * apply pre9. auto.
                       * apply IHy with c2. auto. auto.
                       * clear IHy. intros.
                          apply pre13 with a l c2; auto.
Qed.

Lemma pre15 : forall l l0 l2 o2 l1,
NoPrefix l0 l2 ->
 Forall (NoPrefix (l0 ++ l1)) (fst (List.split (prepre0 (l2, o2) l))).
Proof.
intros l.
induction l.
+ intros. Transparent List.split. simpl. auto.
+ intros. Opaque List.split. simpl in *.
    rewrite split_cons. simpl.
    apply Forall_cons_iff.
    split.
    - apply app_NoPrefix. auto.
    - apply IHl. auto.
Qed.

Lemma pre16 : forall y l' l0 l1 c2,
Forall (NoPrefix l0) (fst (List.split y)) ->
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
        MNP (fst (List.split sts)) /\
        (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts)) (map snd y) l' ->
Forall (NoPrefix (l0 ++ l1)) (fst (List.split (concat (prepre1 y l')))).
Proof.
intros y.
induction y.
+ intros. inversion H0. subst. Transparent List.split. simpl. auto.
+ intros l'. destruct l'.
           - intros. inversion H0.
           - intros. Opaque List.split. simpl in *.
              apply Forall2_cons_cons_iff in H0.
              destruct H0 as [[? ?] ?].
              rewrite split_cons in H. rewrite split_app. simpl in *.
              apply Forall_cons_iff in H.
              destruct H.
              apply Forall_app.
              split.
              * destruct a as [l2 o2].
                 simpl in *.
                 apply pre15; auto.
              * apply IHy with c2; auto.
Qed.


Lemma test1 :
forall dst1 (dsts1 dsts3: list (list (list Z * State))) c1 c2,
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
              MNP (fst (List.split sts)) /\
       (forall (l : list Z) (st2 : State), ceval c1 st1 l st2 <-> In (l, st2) sts)) dst1 dsts1 ->
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
              MNP (fst (List.split sts)) /\
       (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts)) (map snd (concat dsts1)) dsts3 ->
exists dsts : list (list (list Z * State)),
(map snd (concat dsts)) = (map snd (concat dsts3)) /\
Forall2
      (fun (st1 : State) (sts : list (list Z * State)) =>
            MNP (fst (List.split sts)) /\
      (forall (l : list Z) (st2 : State), ceval (c1;; c2) st1 l st2 <-> In (l, st2) sts)) dst1 dsts.
Proof.
intros dst1.
induction dst1.
+ intros.
    inversion H. subst.
    inversion H0. subst.
    exists []. split; auto.
+ intros.
    inversion H. subst. clear H.
    destruct H3 as [? ?].
    simpl in H0. rewrite map_app in H0.
    apply Forall2_app_inv_l in H0.
    destruct H0 as [l1' [l2' [? [? ?]]]]. subst.
    specialize (IHdst1 l' l2' c1 c2 H5 H2). clear H2 H5 l'.
    destruct IHdst1 as [dsts [? ?]].
    exists ((concat (prepre1 y l1')) :: dsts).
    destruct y.
    - inversion H0. subst. clear H0. 
       split.
       * auto.
       * apply Forall2_cons. split.
          ++ auto.
          ++ intros.
                 rewrite ceval_CSeq. unfold TerRel.concat. split.
                 -- intros.
                     destruct H0 as [b [l1 [l2 [? [? ?]]]]].
                     specialize (H1 l1 b). apply H1. auto.
                 -- intros. inversion H0.
           ++ auto.
    - inversion H0. subst. clear H0.
       destruct H6 as [? ?].
       destruct y0.
       * split.
          ++ simpl. rewrite concat_app.  rewrite map_app.
                 rewrite map_app. rewrite H2. rewrite app_inv_tail_iff.
                 rewrite pre3. auto. 
          ++ simpl. apply Forall2_cons.
                 2 :{ auto. } clear H3 H2.
                 split.
                 -- clear H1 H4 H0.
                      Opaque List.split.
                      rewrite split_cons in H. simpl in H.
                      apply MNP_cons_iff in H.
                      destruct H.
                      apply pre14 with c2; auto.
                 -- intros. clear H H0.
                     rewrite ceval_CSeq. unfold TerRel.concat. split.
                     ** intros.
                           destruct H as [b [l1 [l2 [? [? ?]]]]].
                           rewrite H1 in H. destruct H.
                           { rewrite H in H4. rewrite H4 in H0. inversion H0. }
                           { subst. pose proof @pre5 y l' l1 l2 b st2 c2 H8 H0 H. auto. }
                     ** intros.
                           assert (forall (l : list Z) (st2 : State), In (l, st2) y -> ceval c1 a l st2).
                           intros. apply H1. simpl. auto.
                           apply pre7 with y l'; auto.
       * split.
          ++ simpl. pose proof cons_app State (snd p0) (map snd (y0 ++ concat (l' ++ l2'))). 
                 rewrite H5. rewrite cons_app. apply app_inv_head_iff.
                 rewrite concat_app. repeat rewrite map_app. rewrite H2.
                 rewrite <- app_assoc_reverse. rewrite app_inv_tail_iff. rewrite pre2,pre3. auto.
          ++ simpl. apply Forall2_cons.
                 2 : { auto. } clear H3 H2.
                 split.
                 -- clear H1 H4.
                     Opaque List.split.
                     rewrite split_cons,split_app in *. simpl in *.
                     apply MNP_cons_iff in H,H0.
                     destruct H,H0.
                     apply MNP_cons_iff.
                     split.
                     ** destruct p as [l0 o0].
                          destruct p0 as [l1 o1].
                           simpl in *.
                           apply Forall_app.
                           split.
                           +++ apply pre8. auto.
                           +++ apply pre16 with c2; auto.
                      ** apply MNP_app.
                           +++ apply pre9. auto.
                           +++ apply pre14 with c2; auto.
                           +++ intros. apply pre13 with p y0 c2; auto.
                 -- intros. clear H H0.
                     rewrite ceval_CSeq. unfold TerRel.concat.
                     split.
                     ** intros.
                          destruct H as [b [l1 [l2 [? [? ?]]]]].
                          rewrite H1 in H. subst. destruct H.
                          +++ subst. rewrite H4 in H0. destruct H0.
                                --- subst. simpl. left. auto.
                                --- simpl. right. apply in_or_app.
                                      left. apply pre4. auto.
                           +++ simpl. right. apply in_or_app. right.
                                     apply pre5 with b c2; auto.
                     ** intros. simpl in H. destruct H.
                           +++ destruct p as [l1 o1].
                                     destruct p0 as [l2 o2].
                                     simpl in *. inversion H.
                                     specialize (H1 l1 o1).
                                     specialize (H4 l2 o2).
                                     exists o1,l1,l2.
                                     split. apply H1. left. auto.
                                     split. rewrite <- H3. apply H4. auto. auto.
                           +++ apply in_app_or in H.
                                     destruct H.
                                     --- destruct p as [l1 o].
                                           apply pre6 in H.
                                           destruct H as [l2 [? ?]].
                                           exists o,l1,l2.
                                           split. apply H1. simpl. auto.
                                           split. apply H4. simpl. auto. auto.
                                     --- assert (forall (l : list Z) (st2 : State), In (l, st2) y -> ceval c1 a l st2).
                                          intros. apply H1. simpl. auto.
                                          apply pre7 with y l'; auto.
Qed.


Lemma TE4 :forall b st, (dbeval b st) = true <-> beval b st.
Admitted.
Lemma TE3 : forall b st, ¬ (dbeval b st) = true <-> ~ beval b st.
Admitted.


Lemma test2 : forall dst1 (dsts1 dsts2: list (list (list Z * State))) c1 c2 b,
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
             MNP (fst (List.split sts)) /\
        (forall (l : list Z) (st2 : State), ceval c1 st1 l st2 <-> In (l, st2) sts)) (filter (dbeval b) dst1) dsts1 ->
Forall2
       (fun (st1 : State) (sts : list (list Z * State)) =>
             MNP (fst (List.split sts)) /\
        (forall (l : list Z) (st2 : State), ceval c2 st1 l st2 <-> In (l, st2) sts)) (filter (dbeval (! b)) dst1) dsts2 ->

exists dsts : list (list (list Z * State)),
  Permutation (map snd (concat dsts)) (map snd (concat (dsts1 ++ dsts2))) /\
  Forall2
    (fun (st1 : State) (sts : list (list Z * State)) =>
     MNP (fst (List.split sts)) /\
     (forall (l : list Z) (st2 : State), ceval (If b Then c1 Else c2 EndIf) st1 l st2 <-> In (l, st2) sts))
    dst1 dsts.
Proof.
intros dst1.

induction dst1. 
- intros.
  simpl in *.
  inversion H0. subst.
  inversion H. subst.
  subst. exists [].
  split. simpl. auto. apply Forall2_nil.

- intros. rewrite ceval_CIf. unfold Denotations.if_sem. unfold TerRel.union, TerRel.concat, TerRel.test_rel.
  destruct (dbeval b a) eqn:EQ.
  + simpl in *. rewrite EQ in H,H0. simpl in H0.  rewrite TE4 in EQ.
      induction dsts1.
      * inversion H.
      * apply Forall2_cons_cons_iff in H. destruct H as [[? ?] ?].
         specialize (IHdst1 dsts1 dsts2 c1 c2 b H2 H0).
         destruct IHdst1 as [dsts [? ?]].
         exists (a0 :: dsts).
         split. simpl. rewrite map_app. rewrite map_app.
         apply Permutation_app_head. auto.
         apply Forall2_cons.
         split. auto. intros.
         split. intros. inversion H5. apply H1.
         destruct H6 as [b0 [l1 [l2 [[? [? ?]] [? ?]]]]].
         subst. rewrite app_nil_l. auto.
         destruct H6 as [b0 [l1 [l2 [[? [? ?]] [? ?]]]]].
         unfold Sets.complement in H7. unfold not in H7. apply H7 in EQ. inversion EQ.
         intros. apply H1 in H5.
         left. exists a,[],l. split. auto.
         rewrite app_nil_l. auto. auto.
  +  simpl in *. rewrite EQ in H,H0. simpl in H0. apply negb_true_iff in EQ. rewrite TE3 in EQ.
      induction dsts2.
      * inversion H0.
      * apply Forall2_cons_cons_iff in H0. destruct H0 as [[? ?] ?].
         specialize (IHdst1 dsts1 dsts2 c1 c2 b H H2).
         destruct IHdst1 as [dsts [? ?]].
         exists (a0 :: dsts).
         split. simpl. rewrite map_app. rewrite concat_app. simpl.
         rewrite map_app. rewrite map_app.
         pose proof Permutation_app_swap_app (map snd a0) (map snd (concat dsts1)) (map snd (concat dsts2)).
         apply perm_trans with (map snd a0 ++ map snd (concat dsts1) ++ map snd (concat dsts2)). 
         apply Permutation_app_head. rewrite concat_app in H3. rewrite map_app in H3. auto. auto.
         apply Forall2_cons.
         split. auto. intros.
         split. intros. inversion H5. apply H1.
         destruct H6 as [b0 [l1 [l2 [[? [? ?]] [? ?]]]]].
         unfold not in EQ. apply EQ in H7. inversion H7.
         destruct H6 as [b0 [l1 [l2 [[? [? ?]] [? ?]]]]].
         subst. rewrite app_nil_l. apply H1. auto.
         intros. apply H1 in H5.
         right. exists a,[],l. split. auto.
         rewrite app_nil_l. auto. auto.
Qed.

Lemma test3 : forall dst2,
Permutation (map snd (concat (prepre2 dst2))) dst2 /\
Forall2
  (fun (st1 : State) (sts : list (list Z * State)) =>
   MNP (fst (List.split sts)) /\
   (forall (l : list Z) (st2 : State), ceval Skip st1 l st2 <-> In (l, st2) sts)) dst2 
  (prepre2 dst2).
Proof.
intros dst2. split.
- induction dst2. 
        * auto.
        * intros. simpl. pose proof Permutation_app_head [a] IHdst2. auto.
    - induction dst2. 
        * simpl. apply Forall2_nil.
        * simpl in *.  apply Forall2_cons.
           split. apply MNP_cons.  auto. apply MNP_nil.
           split. rewrite ceval_CSkip. unfold TerRel.id. intros. destruct H as [? ?]. subst. firstorder.
           intros. inversion H. inversion H0. subst. rewrite ceval_CSkip. unfold TerRel.id. auto. 
           inversion H0. auto.
Qed.


Lemma loop_sem_unrolling': forall b (r: State -> list Z -> State -> Prop),
  TerRel.equiv (Denotations.loop_sem b r) 
       (TerRel.concat (Denotations.if_sem b r TerRel.id) (Denotations.loop_sem b r)).
Proof.
  intros.
  unfold TerRel.equiv; intros st1 l st2.
  unfold iff; split; intros.
  + unfold loop_sem, TerRel.omega_union in H.
      destruct H as [n ?].
      destruct n.
      - simpl in H.
         unfold TerRel.test_rel in H.
         destruct H as [? [? ?]]. subst.
         unfold TerRel.concat.
         exists st2,[],[].
         split.
         unfold if_sem, TerRel.union.
         right.
         unfold TerRel.concat.
         exists st2,[],[].
         split. unfold TerRel.test_rel. auto.
         split. unfold TerRel.id. auto.
         split. auto.
         split. unfold loop_sem, if_sem, TerRel.union,TerRel.omega_union.
         exists 0%nat. simpl. unfold TerRel.test_rel. auto. split.
      - simpl in H. unfold TerRel.concat in H.
        destruct H as [st1' [l1 [l2 ?]]].
        destruct H as [? [[st1'' [l3 [l4 [? [? ?]]]]] ?]].
        unfold TerRel.concat.
        exists st1'',(l1 ++ l3),l4.
        split. unfold if_sem, TerRel.union.
        left.
        unfold TerRel.concat.
        exists st1',l1,l3.
        split; auto.
        split.
        unfold loop_sem, TerRel.omega_union.
        exists n. auto.
        subst. rewrite app_assoc. auto.
 + unfold TerRel.concat in H.
      destruct H as [st1' [l0 [l1[? [? ?]]]]].
      unfold loop_sem,TerRel.omega_union in H0.
      destruct H0 as [n ?].
      unfold if_sem, TerRel.union in H.
      destruct H.
      - unfold TerRel.concat in H.
        destruct H as [st1'' [l2 [l3 [? [? ?]]]]].
        unfold loop_sem, TerRel.omega_union.
        exists (S n). simpl. unfold TerRel.concat.
        exists st1'',l2,(l3 ++ l1).
        split. auto.
        split. exists st1',l3,l1. auto.
        subst. rewrite app_assoc. auto.
      -  simpl in *.
         unfold TerRel.concat, TerRel.id in H.
         destruct H as [st2' [l3 [[] [? [[? ?] ?]]]]]. subst.
         unfold loop_sem,TerRel.omega_union.
         exists n.
         unfold TerRel.test_rel in H.
         destruct H as [? [? ?]].
         subst. simpl. auto.
         unfold Denotations.loop_sem,TerRel.omega_union.
         exists n.
         unfold TerRel.test_rel in H.
         destruct H as [? [? ?]].
         subst. rewrite H3.
         simpl. auto.
Qed.


Lemma test4 : forall dst1 dsts5 b c,
Forall2
        (fun (st1 : State) (sts : list (list Z * State)) =>
         MNP (fst (List.split sts)) /\
         (forall (l : list Z) (st2 : State),
          ceval (If b Then c Else Skip EndIf;; While b Do c EndWhile) st1 l st2 <-> In (l, st2) sts)) dst1 dsts5 ->
Forall2
  (fun (st1 : State) (sts : list (list Z * State)) =>
   MNP (fst (List.split sts)) /\
   (forall (l : list Z) (st2 : State), ceval (While b Do c EndWhile) st1 l st2 <-> In (l, st2) sts)) dst1
  dsts5 .
Proof.
intros dst1.
induction dst1.
+ intros. inversion H. subst. auto.
+ intros dsts5. destruct dsts5.
    - intros. inversion H.
    - intros. apply Forall2_cons_cons_iff in H.
       destruct H as [[? ?] ?].
       apply Forall2_cons_cons_iff. split.
       * split. auto.
          intros. rewrite ceval_CWhile.
          pose proof loop_sem_unrolling'.
          unfold TerRel.equiv in H2.
          rewrite H2.
          rewrite ceval_CSeq, ceval_CIf, ceval_CSkip in H0. auto.
       * auto.
Qed.


Lemma tranDC_While: forall dst1 dst2 n b c,
  (forall dst1 dst2 : DState, dceval c dst1 dst2 ->
      exists dsts : list (list (list Z * State)),
        Permutation (map snd (concat dsts)) dst2 /\
        Forall2
          (fun (st1 : State) (sts : list (list Z * State)) =>
           MNP (fst (List.split sts)) /\ (forall (l : list Z) (st2 : State), ceval c st1 l st2 <-> In (l, st2) sts)) dst1 dsts) ->
  iter_loop_body b (dceval c) n dst1 dst2 ->
  exists dsts : list (list (list Z * State)),
  Permutation (map snd (concat dsts)) dst2 /\
  Forall2
    (fun (st1 : State) (sts : list (list Z * State)) =>
     MNP (fst (List.split sts)) /\ (forall (l : list Z) (st2 : State), ceval (While b Do c EndWhile) st1 l st2 <-> In (l, st2) sts)) dst1 dsts.
Proof.
intros.
revert dst1 dst2 H0; induction n; intros.
+ simpl in H0. unfold BinRel.test_rel'' in H0.
    destruct H0. subst. clear H. rewrite H1.
    exists (prepre2 dst1). split.
    - clear H1. induction dst1.
    * auto.
    * simpl. pose proof Permutation_app_head [a] IHdst1. auto.
    - induction dst1.
     * simpl. intros. apply Forall2_nil.
     * assert (In a (a :: dst1)). simpl. auto. rewrite <- H1 in H.
        rewrite filter_In in H. inversion H.
        pose proof filter_app (fun st : State => ¬ (dbeval b st)) [a] dst1.
        assert (a:: dst1 = [a] ++ dst1). simpl. auto. rewrite H4 in H1.
        apply filter_cons in H1. apply IHdst1 in H1. clear IHdst1 H H0 H3 H4. 2:{ auto. } rewrite TE3 in H2.
      intros. simpl.  apply Forall2_cons.
        split. apply MNP_cons. auto. apply MNP_nil.
        split. intros. rewrite ceval_CWhile in H. unfold Denotations.loop_sem in H. unfold TerRel.omega_union in H.
        destruct H as [n ?]. induction n.
         { simpl in H. unfold TerRel.test_rel in H. destruct H as [? [? ?]]. subst. simpl. auto. }
         { apply IHn. clear IHn. simpl in *. unfold TerRel.concat in H.
            destruct H as [b0 [ l1 [l2 [? [? ?]]]]].
            destruct H0 as [b1 [l3 [l4 [? [? ?]]]]].
            unfold TerRel.test_rel in H. destruct H as [? [? ?]]. subst. unfold not in H2. apply H2 in H6. inversion H6. }
         intros. inversion H. inversion H0. rewrite ceval_CWhile. 
         unfold Denotations.loop_sem, TerRel.omega_union. exists O. simpl. unfold TerRel.test_rel.
         subst. auto. inversion H0.
       auto.
+ simpl in H0.
    unfold BinRel.concat,BinRel.merge,BinRel.test_rel',BinRel.test_rel in H0.
    destruct H0 as [dst [[b1 [b2 [[b0 [[? ?] ?]] [? ?]]]] ?]].
    specialize (H b0 b1 H2). destruct H as [dsts1 [? ?]].
    specialize (IHn dst dst2 H5). destruct IHn as [dsts2 [? ?]].
    subst.
    pose proof test3 (filter (fun st : State => ¬ (dbeval b st)) dst1).
    destruct H0.
    pose proof @test2 dst1 dsts1 ((prepre2 (filter (fun st : State => ¬ (dbeval b st)) dst1))) c CSkip b H6 H3.
    assert (exists dsts : list (list (list Z * State)),
    Permutation (map snd (concat dsts)) (b1 ++ (filter (fun st : State => ¬ (dbeval b st)) dst1)) /\
    Forall2
    (fun (st1 : State) (sts : list (list Z * State)) =>
     MNP (fst (List.split sts)) /\
     (forall (l : list Z) (st2 : State),
      ceval (If b Then c Else CSkip EndIf) st1 l st2 <-> In (l, st2) sts)) dst1 dsts). 
      destruct H4 as [dsts [? ?]].
      exists dsts. rewrite H4. split.
      rewrite concat_app,map_app. apply Permutation_app. auto. auto. auto.
      clear H4 H6 H3.
      destruct H9 as [dsts3 [? ?]].
      apply Permutation_sym in H3.
      pose proof Permutation_Forall2 H3 H8.
      destruct H6 as [dsts4 [? ?]].
      pose proof test1 ( (If b Then c Else Skip EndIf)) (While b Do c EndWhile) H4 H9.
      destruct  H10 as [dsts5 [? ?]].
      exists dsts5. split. rewrite H10.
      apply Permutation_trans with (map snd (concat dsts2)).
      apply Permutation_map. apply Permutation_concat.
      apply Permutation_sym. auto. auto.
      apply test4. auto.
Qed.


Lemma EQU : forall c dst1 dst2,
dceval c dst1 dst2 -> exists dsts: list (list (list Z * State)),
Permutation (map snd (concat dsts)) dst2 /\
Forall2 (fun st1 sts => MNP (fst (List.split sts)) /\  forall l st2, ceval c st1 l st2 <-> In (l, st2) sts) dst1 dsts.
Proof.
intros.
revert dst1 dst2 H. induction c; intros.
+ rewrite dceval_CSkip in H. unfold BinRel.id in H. subst.
    exists (prepre2 dst2). split.
    - induction dst2. 
        * auto.
        * simpl. pose proof Permutation_app_head [a] IHdst2. auto.
    - induction dst2. 
        * simpl. apply Forall2_nil.
        * simpl in *.  apply Forall2_cons.
           split. apply MNP_cons.  auto. apply MNP_nil.
           split. rewrite ceval_CSkip. unfold TerRel.id. intros. destruct H as [? ?]. subst. firstorder.
           intros. inversion H. inversion H0. subst. rewrite ceval_CSkip. unfold TerRel.id. auto. 
           inversion H0. auto.
+ rewrite dceval_CAss in H. subst.
    exists (prepre2 (dist_update_C dst1 X a)). split.
    - induction dst1.
       * simpl. auto.
       * simpl in *. pose proof Permutation_app_head [(X !-> aeval a a0, fst a0, snd a0)] IHdst1. auto.
    - induction dst1.
      * simpl. apply Forall2_nil.
      * simpl in *. apply Forall2_cons.
        split. apply MNP_cons. auto. apply MNP_nil.
        split. intros. rewrite ceval_CAss in H. destruct H as [? ?]. subst. firstorder.
        intros. inversion H. inversion H0. subst. rewrite ceval_CAss. unfold TerRel.id. auto.
        inversion H0. auto.
+ rewrite dceval_CSeq in H. unfold BinRel.concat in H. destruct H as [dst0 [? ?]].
    specialize (IHc1 dst1 dst0 H). destruct IHc1 as [dsts1 [? ?]].
    specialize (IHc2 dst0 dst2 H0). destruct IHc2 as [dsts2 [? ?]].
    apply Permutation_sym in H1.
    pose proof Permutation_Forall2 H1 H4.
     destruct H5 as [dsts3 [? ?]].
    pose proof test1 c1 c2 H2 H6.
    destruct  H7 as [dsts4 [? ?]].
    exists dsts4. split. rewrite H7. apply Permutation_trans with (map snd (concat dsts2)).
    apply Permutation_map. apply Permutation_concat. apply Permutation_sym. auto. auto. auto.
+ rewrite dceval_CIf in H. unfold if_sem in H. unfold BinRel.merge in H.
    destruct H as [b1 [b2 [ ? [? ?]]]]. unfold BinRel.concat,BinRel.test_rel in H, H0.
    destruct H as [b01 [? ?]]. destruct H0 as [b02 [? ?]].
    specialize (IHc1 b01 b1 H2). specialize (IHc2 b02 b2 H3).
    destruct IHc1 as [dsts1 [? ?]]. destruct IHc2 as [dsts2 [? ?]]. subst.
    pose proof test2 dst1 c1 c2 b H5 H7.
    destruct H as [dsts [? ?]].
    exists dsts. rewrite H. split.
    rewrite concat_app,map_app. apply Permutation_app. auto. auto. auto.
+ rewrite dceval_CWhile in H. unfold loop_sem in H. unfold BinRel.omega_union in H.
    destruct H as [n ?]. apply tranDC_While with n. auto. auto.
+ unfold dceval in H. subst.
    exists (prepre2 (dist_update_Q dst1 (u_1 U Q))). split.
    - induction dst1.
       * simpl. auto.
       * simpl in *. pose proof Permutation_app_head [DQ a (u_1 U Q)] IHdst1. auto.
    - induction dst1.
      * simpl. apply Forall2_nil.
      * simpl in *. apply Forall2_cons.
        split. apply MNP_cons. auto. apply MNP_nil.
        split. intros. simpl in H. destruct H as [? ?]. subst. firstorder.
        intros. inversion H. inversion H0. subst. unfold ceval. auto.
        inversion H0. auto.
+ unfold dceval in H. subst.
    exists (prepre2 (dist_update_Q dst1 (u_2 U Q P))). split.
    - induction dst1.
       * simpl. auto.
       * simpl in *. pose proof Permutation_app_head [DQ a (u_2 U Q P)] IHdst1. auto.
    - induction dst1.
      * simpl. apply Forall2_nil.
      * simpl in *. apply Forall2_cons.
        split. apply MNP_cons. auto. apply MNP_nil.
        split. intros. unfold ceval in H. destruct H as [? ?]. subst. simpl. left. auto.
        intros. inversion H. inversion H0. subst. unfold ceval. auto.
        inversion H0. auto.
+ unfold dceval in H. subst.
    unfold ceval.
    exists (prepre3 dst1 Q X). split.
    - induction dst1.
       * simpl. auto.
       * simpl in *. unfold update_State. unfold constant_func.
       pose proof Permutation_app_head [(X !-> 0, fst a, Mea0 Q # snd a)]. simpl in H. apply H.
       apply Permutation_cons_app. auto.
    - induction dst1.
      * simpl. apply Forall2_nil.
      * simpl in *. apply Forall2_cons.
       split. apply MNP_cons. apply Forall_cons. unfold NoPrefix.
       split. unfold not. intros. inversion H.  simpl in H0. inversion H0.
       unfold not. intros. inversion H.  simpl in H0. inversion H0.
       auto. apply MNP_cons. auto. apply MNP_nil.
       intros. split. intros. destruct H as [[? ?]|[? ?]]; subst; simpl; auto.
                                 intros. destruct H as [?|[ ?| ?]];inversion H; subst; auto. auto.
Qed.





