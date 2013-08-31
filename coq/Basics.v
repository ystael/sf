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

Inductive bool: Type :=
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
