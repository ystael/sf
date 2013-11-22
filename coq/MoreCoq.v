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
Proof.