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

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof. intros n m; assert (0 + n = n) as H.
Case "H: 0 + n = n". reflexivity.
rewrite H; reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof. intros n m p q; assert (n + m = m + n) as H.
Case "H: n + m = m + n". apply plus_comm.
rewrite H; reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof. intros n m p; assert (n + m = m + n) as H.
Case "H: n + m = m + n". apply plus_comm.
rewrite plus_assoc; rewrite plus_assoc; rewrite H; reflexivity.
Qed.

Theorem mult_iden_r : forall n : nat, n * 1 = n.
Proof. intro n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; rewrite IHn'; reflexivity.
Qed.

Lemma mult_S_r : forall n m : nat, n * S m = n + n * m.
Proof. intros n m; induction n as [| n']. 
Case "n = 0".    reflexivity.
Case "n = S n'". simpl. rewrite plus_swap; rewrite IHn'; reflexivity.
Qed.

Theorem mult_comm : forall n m : nat, n * m = m * n.
Proof. intros m n; induction n as [| n'].
Case "n = 0".    simpl; apply mult_0_r.
Case "n = S n'". simpl; rewrite mult_S_r; rewrite IHn'; reflexivity.
Qed.

Lemma evenb_SS : forall n : nat, evenb (S (S n)) = evenb n.
Proof. reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat, evenb n = negb (evenb (S n)).
Proof. intros n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". rewrite evenb_SS; rewrite IHn'; rewrite negb_involutive; reflexivity.
Qed.

Theorem ble_nat_refl : forall n : nat, ble_nat n n = true.
Proof. intros n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; exact IHn'.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat O (S n) = false.
Proof. reflexivity. Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof. destruct b; reflexivity. Qed.

Theorem plus_ble_compat_l :
  forall n m p : nat, ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof. intros n m p H; induction p as [| p'].
Case "p = 0".    simpl; exact H.
Case "p = S p'". simpl; exact IHp'.
Qed.

Theorem S_nbeq_0 : forall n : nat, beq_nat (S n) 0 = false.
Proof. reflexivity. Qed.

Theorem mult_iden_l : forall n : nat, 1 * n = n.
Proof. intro n; simpl; rewrite plus_0_r; reflexivity.
Qed.

Theorem all3_spec : forall b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.
Proof. intros b c; destruct b; destruct c; reflexivity.
Qed.

Theorem mult_plus_dist_r : forall n m p : nat, (n + m) * p = n * p + m * p.
Proof. intros n m p; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; rewrite IHn'; apply plus_assoc; reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, n * (m * p) = (n * m) * p.
Proof. intros n m p; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl. rewrite mult_plus_dist_r. rewrite IHn'; reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat, true = beq_nat n n.
Proof. intro n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; exact IHn'.
Qed.

Theorem plus_swap' : forall n m p : nat, n + (m + p) = m + (n + p).
Proof. intros n m p; repeat rewrite plus_assoc; replace (n + m) with (m + n). reflexivity.
Case "hypothesis from replace". apply plus_comm.
Qed.

Theorem bin_to_nat_past_S : forall n : bin, bin_to_nat (bin_S n) = S (bin_to_nat n).
Proof. intros n; induction n as [| n' | n'].
Case "n = ZZ".    reflexivity.
Case "n = EE n'". reflexivity.
Case "n = OO n'". simpl; repeat rewrite plus_0_r; repeat rewrite IHn';
  rewrite plus_n_Sm; reflexivity.
Qed.

