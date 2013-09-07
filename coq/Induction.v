Require Export Basics.
Require Export TacticUtil.

Theorem andb_true_elim1 : forall b c : bool, andb b c = true -> b = true.
Proof. intros b c H; destruct b.
Case "b = true".  reflexivity.
Case "b = false". rewrite <- H; reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof. intros b c H; destruct c.
Case "c = true".  reflexivity.
Case "c = false". destruct b; rewrite <- H; reflexivity.
Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof. intro n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; rewrite IHn'; reflexivity.
Qed.

Theorem minus_diag : forall n : nat, minus n n = 0.
Proof. intro n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; apply IHn'.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof. intro n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; apply IHn'.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof. intros n m; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; rewrite IHn'; reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof. intros n m; induction n as [| n'].
Case "n = 0".    rewrite plus_0_r; reflexivity.
Case "n = S n'". simpl; rewrite IHn'; rewrite plus_n_Sm; reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof. intros n m p; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; rewrite IHn'; reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
    | O    => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n : nat, double n = n + n.
Proof. intros n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; rewrite IHn'; rewrite plus_n_Sm; reflexivity.
Qed.
