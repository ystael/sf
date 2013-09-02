Inductive day : Set :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

Definition next_weekday (d: day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
  end.

Eval compute in next_weekday (next_weekday saturday).

Example test_next_weekday: next_weekday (next_weekday saturday) = tuesday.
Proof.
  simpl; reflexivity.
Qed.

Inductive bool : Set :=
  | true  : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
    | true  => false
    | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
    | true  => b2
    | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
    | true  => true
    | false => b2
  end.

Example test_orb1: (orb true true) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. reflexivity. Qed.

Definition nandb (b1 b2 : bool) : bool :=
  match b1 with
    | true  => false
    | false => negb b2
  end.

Example test_nandb1 : (nandb true true) = false.
Proof. reflexivity. Qed.
Example test_nandb2 : (nandb true false) = false.
Proof. reflexivity. Qed.
Example test_nandb3 : (nandb false true) = false.
Proof. reflexivity. Qed.
Example test_nandb4 : (nandb false false) = true.
Proof. reflexivity. Qed.

Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1 with
    | true  => andb b2 b3
    | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Module Playground1.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O    => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O        => O
    | S O      => O
    | S (S n') => n'
  end.

Eval simpl in (minustwo 4).

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O        => true
    | S O      => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) := negb (evenb n).

Example test_oddb1 : oddb (S O) = true.
Proof. reflexivity. Qed.
Example test_oddb2 : oddb 4 = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O    => m
    | S n' => S (plus n' m)
  end.

Eval simpl in plus (S (S O)) (S (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O    => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1 : mult 3 3 = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O, _       => O
    | n, O       => n
    | S n', S m' => minus n' m'
  end.

Eval simpl in minus 5 3.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O   => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O    => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1 : factorial 3 = 6.
Proof. reflexivity. Qed.
Example test_factorial2 : factorial 5 = 120.
Proof. reflexivity. Qed.

(*
Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
*)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O    => match m with
                | O    => true
                | S m' => false
              end
    | S n' => match m with
                | O    => false
                | S m' => beq_nat n' m'
              end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O    => true
    | S n' => match m with
                | O    => false
                | S m' => ble_nat n' m'
              end
  end.

Example test_ble_nat1 : ble_nat 2 2 = true.
Proof. reflexivity. Qed.
Example test_ble_nat2 : ble_nat 2 4 = true.
Proof. reflexivity. Qed.
Example test_ble_nat3 : ble_nat 4 2 = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.

Example test_blt_nat1 : blt_nat 2 2 = false.
Proof. reflexivity. Qed.
Example test_blt_nat2 : blt_nat 2 4 = true.
Proof. reflexivity. Qed.
Example test_blt_nat3 : blt_nat 4 2 = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intro n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intro n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
Proof. intros n m H. rewrite H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof. intros n m o H1 H2. rewrite -> H1. rewrite <- H2. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof. intros n m. rewrite plus_O_n. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat, m = S n -> m * (1 + n) = m * m.
Proof. intros n m H. rewrite plus_1_l. rewrite H. reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat, beq_nat (n + 1) 0 = false.
Proof. intros n. destruct n as [| n']; reflexivity. Qed.

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof. intros b. destruct b; reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
Proof. intros n. destruct n as [| n']; reflexivity. Qed.

Theorem identity_fn_applied_twice :
  forall f : bool -> bool,
    (forall x : bool, f x = x) -> forall b : bool, f (f b) = b.
Proof. intros f H b. rewrite H. rewrite H. reflexivity. Qed.

Theorem andb_eq_orb :
  forall b c : bool, (andb b c = orb b c) -> b = c.
Proof. intros b c; destruct b; destruct c; simpl;
       intro H; try rewrite H; reflexivity.
Qed.

Inductive bin : Set :=
  | ZZ : bin         (* zero *)
  | EE : bin -> bin  (* EE n = 2n *)
  | OO : bin -> bin. (* OO n = 2n + 1 *)

Fixpoint bin_S (n : bin) : bin :=
  match n with
    | ZZ    => OO ZZ
    | EE n' => OO n'
    | OO n' => EE (bin_S n')
  end.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | O    => ZZ
    | S n' => bin_S (nat_to_bin n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
    | ZZ    => O
    | EE n' => 2 * (bin_to_nat n')
      (* Note this is not S (bin_to_nat (EE n')) because that isn't structurally decreasing *)
    | OO n' => S (2 * (bin_to_nat n'))
  end.

Example test_bin_to_nat1 : bin_to_nat (OO (EE (OO (EE (OO ZZ))))) = 21.
Proof. reflexivity. Qed.
Example test_bin_to_nat2 : bin_to_nat (EE (EE (EE ZZ))) = 0.
Proof. reflexivity. Qed.
Example test_bin_to_nat_S : S (bin_to_nat (OO (OO (OO (EE (OO ZZ)))))) =
                            bin_to_nat (bin_S (OO (OO (OO (EE (OO ZZ)))))).
Proof. reflexivity. Qed.
