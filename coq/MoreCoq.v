Require Export Poly.

Theorem silly1 : forall (n m o p : nat), n = m -> [n; o] = [n; p] -> [n; o] = [m; p].
Proof. intros n m o p H1 H2; rewrite <- H1; exact H2. Qed.

Theorem silly2 : forall (n m o p : nat), n = m ->
  (forall (q r : nat), q = r -> [q; o] = [r; p]) ->
  [n; o] = [m; p].
Proof. intros n m o p H1 H2; apply H2; exact H1. Qed.

Theorem silly2a: forall (n m : nat), (n, n) = (m, m) ->
  (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
  [n] = [m].
Proof. intros n m H1 H2; apply H2; exact H1. Qed.

Theorem silly_ex : (forall (n : nat), evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> oddb 4 = true.
Proof. intros H H3; apply H; exact H3. Qed.

Theorem silly3 : forall (n : nat), true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof. intros n H; symmetry; apply H. Qed.

Theorem rev_exercise1 : forall (l l' : list nat), l = rev l' -> l' = rev l.
Proof. intros l l' H; rewrite H; symmetry; apply rev_involutive. Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].
Proof. intros a b c d e f E1 E2; rewrite E1; rewrite E2; reflexivity. Qed.

Theorem trans_eq : forall {X : Set} (n m o : X), n = m -> m = o -> n = o.
Proof. intros X n m o E1 E2; rewrite E1; rewrite E2; reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].
Proof. intros a b c d e f E1 E2; apply trans_eq with (m := [c; d]); [exact E1 | exact E2]. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof. intros n m o p E1 E2; apply trans_eq with m; [exact E2 | exact E1]. Qed.

Theorem eq_add_S : forall (n m : nat), S n = S m -> n = m.
Proof. intros n m H; inversion H; reflexivity. Qed.

Theorem silly4 : forall (n m : nat), [n] = [m] -> n = m.
Proof. intros n m H; inversion H; reflexivity. Qed.

Theorem silly5 : forall (n m o : nat), [n; m] = [o; o] -> [n] = [m].
Proof. intros n m o H; inversion H; reflexivity. Qed.

Example sillyex1 : forall (X : Set) (x y z : X) (l j : list X),
  x::y::l = z::j -> y::l = x::j -> x = y.
Proof. intros X x y z l j H1 H2; inversion H2; reflexivity. Qed.

Theorem silly6 : forall (n : nat), S n = O -> 2 + 2 = 5.
Proof. intros n H; inversion H. Qed.

Theorem silly7 : forall (n m : nat), false = true -> [n] = [m].
Proof. intros n m H; inversion H. Qed.

Example sillyex2 : forall (X : Set) (x y z : X) (l j : list X),
  x::y::l = [] -> y::l = z::j -> x = z.
Proof. intros X x y z l j H1 H2; inversion H1. Qed.

Theorem f_equal : forall {A B : Set} (f : A -> B) (x y : A), x = y -> f x = f y.
Proof. intros A B f x y E; rewrite E; reflexivity. Qed.

Theorem length_snoc' : forall (X : Set) (v : X) (l : list X) (n : nat),
                         length l = n -> length (snoc l v) = S n.
Proof. intros x v l; induction l as [| m l'].
Case "l = []".    intros n E; inversion E; reflexivity.
Case "l = m::l'". intros n E; simpl; destruct n as [| n'].
SCase "n = 0".    inversion E.
SCase "n = S n'". apply f_equal; apply IHl'; inversion E; reflexivity.
Qed.

Theorem beq_nat_0_l : forall (n : nat), beq_nat 0 n = true -> n = 0.
Proof. intro n; destruct n as [| n']; simpl; intro H; [reflexivity | inversion H]. Qed.

Theorem beq_nat_0_r : forall (n : nat), beq_nat n 0 = true -> n = 0.
Proof. intro n; destruct n as [| n']; simpl; intro H; [reflexivity | inversion H]. Qed.

Theorem S_inj : forall (n m : nat) (b : bool), beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof. intros n m b H; simpl in H; exact H. Qed.

Theorem silly3' : forall (n : nat), (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
                                    true = beq_nat n 5 -> true = beq_nat (S (S n)) 7.
Proof. intros n Himp H5; symmetry in H5; apply Himp in H5; symmetry in H5; exact H5. Qed.

Theorem plus_n_n_injective : forall (n m : nat), n + n = m + m -> n = m.
Proof. intros n; induction n as [| n']; intros m H; destruct m as [| m'];
       (* Clear the superfluous subcases from destructing m *)
       inversion H as [H1]; clear H1.
Case "n = 0".    reflexivity.
Case "n = S n'". repeat rewrite <- plus_n_Sm in H; simpl in H; inversion H as [H2];
                 apply IHn' in H2; rewrite H2; reflexivity.
Qed.

Theorem double_injective : forall (n m : nat), double n = double m -> n = m.
Proof. intros n; induction n as [| n']; intros m H; destruct m as [| m'];
       inversion H as [H1]; clear H1.
Case "n = 0".    reflexivity.
Case "n = S n'". apply f_equal; apply IHn'; inversion H; reflexivity.
Qed.

Theorem beq_nat_true : forall (n m : nat), beq_nat n m = true -> n = m.
Proof. intros n; induction n as [| n']; intros m H; destruct m as [| m'];
       inversion H as [H1]; clear H1.
Case "n = 0".    reflexivity.
Case "n = S n'". apply f_equal; apply IHn'; simpl in H; exact H.
Qed.

Theorem double_injective_take2 : forall (n m : nat), double n = double m -> n = m.
Proof. intros n m; generalize dependent n; induction m as [| m']; intros n H;
       destruct n as [| n']; inversion H as [H1]; clear H1.
Case "m = 0".    reflexivity.
Case "m = S m'". apply f_equal; apply IHm'; inversion H; reflexivity.
Qed.

Theorem index_after_last : forall (n : nat) (X : Set) (l : list X),
                             length l = n -> index n l = None.
Proof. intros n X l; generalize dependent n; induction l as [| x l'];
       intros n H; destruct n as [| n']; inversion H as [H1]; clear H1.
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; apply IHl'; reflexivity.
Qed.

Theorem length_snoc'' : forall (n : nat) (X : Set) (v : X) (l : list X),
                          length l = n -> length (snoc l v) = S n.
Proof. intros n X v l; generalize dependent n; induction l as [| x l'];
       intros n H; destruct n as [| n']; inversion H as [H1]; clear H1.
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; apply f_equal; apply IHl'; reflexivity.
Qed.

Theorem app_length_cons : forall (X : Set) (l1 l2 : list X) (x : X) (n : nat),
                            length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
Proof. intros X l1; induction l1 as [| y l1']; intros l2 x n H; simpl; simpl in H.
Case "l1 = []".     exact H.
Case "l1 = y::l1'". destruct n as [| n']; inversion H as [H1]; apply IHl1' in H1;
                    symmetry; rewrite H1; exact H.
Qed.

Theorem app_length_twice : forall (X : Set) (n : nat) (l : list X),
                             length l = n -> length (l ++ l) = n + n.
Proof. intros X n l; generalize dependent n; induction l as [| x l']; intros n H;
       destruct n as [| n']; inversion H as [H1]; clear H1.
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; replace (length (l' ++ x :: l')) with (S (length (l' ++ l'))).
                  simpl in H; inversion H as [H1]; clear H; repeat rewrite H1;
                  apply IHl' in H1; rewrite <- plus_n_Sm; rewrite H1; reflexivity.
SCase "Proof of replace". apply app_length_cons with (x := x); reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat), sillyfun n = false.
Proof. intro n; unfold sillyfun; destruct (beq_nat n 3); destruct (beq_nat n 5); reflexivity. Qed.

(* Last override at a given key wins *)
Theorem override_shadow : forall (X : Set) x1 x2 k1 k2 (f : nat -> X),
                            (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof. intros X x1 x2 k1 k2 f; destruct (beq_nat k1 k2) eqn: Hkeq.
Case "k1 = k2".  unfold override; rewrite Hkeq; reflexivity.
Case "k1 <> k2". repeat apply override_neq; try exact Hkeq; symmetry; apply override_neq;
                 [reflexivity | exact Hkeq].
Qed.

Theorem combine_split : forall {X Y : Set} (l : list (X * Y)) (l1 : list X) (l2 : list Y),
                          split l = (l1, l2) -> combine l1 l2 = l.
Proof. intros X Y l; induction l as [| p l']; intros l1 l2 H; inversion H as [H1].
Case "l = []".    reflexivity.
Case "l = p::l'". destruct p as [x y]; destruct (split l') as [xs' ys'];
                  inversion H1; simpl; rewrite IHl'; reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd : forall (n : nat), sillyfun1 n = true -> oddb n = true.
Proof. intros n H; unfold sillyfun1 in H; destruct (beq_nat n 3) eqn: Hn3.
Case "n = 3".  apply beq_nat_true in Hn3; rewrite Hn3; reflexivity.
Case "n <> 3". destruct (beq_nat n 5) eqn: Hn5.
SCase "n = 5". apply beq_nat_true in Hn5; rewrite Hn5; reflexivity.
SCase "n <> 5". inversion H.
Qed.

Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof. intros f b; destruct (f true) eqn: Hftrue; destruct (f false) eqn: Hffalse;
       destruct b; repeat (try rewrite Hftrue; try rewrite Hffalse); reflexivity.
Qed.

Theorem override_same : forall (X : Set) x1 k1 k2 (f : nat -> X),
  f k1 = x1 -> (override f k1 x1) k2 = f k2.
Proof. intros X x1 k1 k2 f Hfk1; unfold override; destruct (beq_nat k1 k2) eqn: Hk1k2;
       try reflexivity.
Case "k1 = k2". apply beq_nat_true in Hk1k2; rewrite <- Hfk1; rewrite Hk1k2; reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat), beq_nat n m = beq_nat m n.
Proof. intros n m; destruct (beq_nat n m) eqn: Heq1.
Case "beq_nat n m = true". apply beq_nat_true in Heq1; rewrite Heq1; apply beq_nat_refl.
Case "beq_nat n m = false". destruct (beq_nat m n) eqn: Heq2; try reflexivity.
SCase "beq_nat m n = true". apply beq_nat_true in Heq2; rewrite Heq2 in Heq1;
  rewrite <- beq_nat_refl in Heq1; inversion Heq1.
Qed.

Theorem beq_nat_trans : forall (n m p : nat),
  beq_nat n m = true -> beq_nat m p = true -> beq_nat n p = true.
Proof. intros n m p Hnm Hmp; apply beq_nat_true in Hnm; apply beq_nat_true in Hmp;
       rewrite Hnm; rewrite <- Hmp; rewrite <- beq_nat_refl; reflexivity.

Theorem split_combine : forall (X Y : Set) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof. intros X Y l1; induction l1 as [| x l1']; intros l2 Hleq;
       destruct l2 as [| y l2']; inversion Hleq as [Hleq'].
Case "l1 = []".     reflexivity.
Case "l1 = x::l1'". simpl; rewrite (IHl1' l2' Hleq'); reflexivity.
Qed.

Lemma override_neq' : forall {X : Set} (x2 : X) (k1 k2 : nat) (f : nat -> X),
  beq_nat k2 k1 = false -> override f k2 x2 k1 = f k1.
Proof. intros X x2 k1 k2 f; apply override_neq; reflexivity.
Qed.

Theorem override_permute : forall (X : Set) (x1 x2 : X) (k1 k2 k3 : nat) (f : nat -> X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof. intros X x1 x2 k1 k2 k3 f k2_Neq_k1.
       assert (beq_nat k1 k2 = false) as k1_Neq_k2. rewrite beq_nat_sym; exact k2_Neq_k1.
       destruct (beq_nat k1 k3) eqn: k1_Qeq_k3; try apply beq_nat_true in k1_Qeq_k3;
       destruct (beq_nat k2 k3) eqn: k2_Qeq_k3; try apply beq_nat_true in k2_Qeq_k3.
Case "k1 = k3, k2 = k3 (absurd case)". rewrite k1_Qeq_k3 in k2_Neq_k1;
  rewrite k2_Qeq_k3 in k2_Neq_k1; rewrite <- beq_nat_refl in k2_Neq_k1; inversion k2_Neq_k1.
Case "k1 = k3 <> k2". rewrite <- k1_Qeq_k3; rewrite override_eq; rewrite override_neq';
  [idtac | exact k2_Neq_k1]; rewrite override_eq; reflexivity.
Case "k1 <> k3 = k2". rewrite <- k2_Qeq_k3; rewrite override_eq; rewrite override_neq';
  [idtac | exact k1_Neq_k2]; rewrite override_eq; reflexivity.
Case "k1 <> k3 <> k2".
  rewrite override_neq'; [idtac | exact k1_Qeq_k3];
  repeat (rewrite override_neq'; [idtac | exact k2_Qeq_k3]);
  rewrite override_neq'; [idtac | exact k1_Qeq_k3];
  reflexivity.
Qed.

Theorem filter_exercise : forall (X : Set) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof. intros X test x l; generalize dependent x; induction l as [| y l'];
       intros x lf H; simpl in H.
Case "l = []".    inversion H.
Case "l = y::l'". destruct (test y) eqn: Hy.
SCase "test y = true". inversion H as [Hyx]; rewrite <- Hyx; exact Hy.
SCase "test x = false". apply IHl' with (lf := lf); exact H.
Qed.

Fixpoint forallb {X : Set} (p : X -> bool) (l : list X) : bool :=
  match l with
    | []    => true
    | x::l' => if p x then forallb p l' else false
  end.

Fixpoint existsb {X : Set} (p : X -> bool) (l : list X) : bool :=
  match l with
    | []    => false
    | x::l' => if p x then true else existsb p l'
  end.

Definition existsb' {X : Set} (p : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (p x)) l).

Theorem exists_equivalent : forall {X : Set} (p : X -> bool) (l : list X),
  existsb' p l = existsb p l.
Proof. intros X p l; induction l as [| x l'].
Case "l = []".    reflexivity.
Case "l = x::l'". unfold existsb'; simpl; destruct (p x).
SCase "p x = true". reflexivity.
SCase "p x = false". rewrite <- IHl'; reflexivity.
Qed.
