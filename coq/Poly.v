Require Export Lists.

Inductive list (X : Set) : Set :=
| nil  : list X
| cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint length {X : Set} (l : list X) : nat :=
  match l with
    | nil       => 0
    | cons x l' => S (length l')
  end.

Fixpoint app {X : Set} (l1 l2 : list X) : list X :=
  match l1 with
    | nil        => l2
    | cons x l1' => cons x (app l1' l2)
  end.

Fixpoint snoc {X : Set} (l : list X) (v : X) : list X :=
  match l with
    | nil       => cons v nil
    | cons x l' => cons x (snoc l' v)
  end.

Fixpoint rev {X : Set} (l : list X) : list X :=
  match l with
    | nil       => nil
    | cons x l' => snoc (rev l') x
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Module MumbleBaz.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Which of the following are well-typed elements of grumble X for some type X?

    d (b a 5) -> not well typed, d's first argument must be a type
    d mumble (b a 5) : grumble mumble.
    d bool (b a 5) : grumble bool.
    e bool true : grumble bool.
    e mumble (b c 0) : grumble mumble.
    e bool (b c 0) -> not well typed, b c 0 is a mumble, not a bool.
    c -> is a mumble, not a grumble. 
*)

Inductive baz : Type :=
  | x : baz -> baz
  | y : baz -> bool -> baz.

(* This type is empty, by backward induction on the length of an expression for an element. *)

End MumbleBaz.

Fixpoint repeat {X : Set} (x : X) (count : nat) : list X :=
  match count with
    | O        => []
    | S count' => x :: repeat x count'
  end.

Example test_repeat1 : repeat true 2 = [true; true].
Proof. reflexivity. Qed.

Theorem nil_app : forall {X : Set} (l : list X), [] ++ l = l.
Proof. reflexivity. Qed.

Theorem rev_snoc : forall {X : Set} (v : X) (l : list X), rev (snoc l v) = v :: rev l.
Proof. intros X v l; induction l as [| x l'].
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; rewrite IHl'; reflexivity.
Qed.

Theorem rev_involutive : forall {X : Set} (l : list X), rev (rev l) = l.
Proof. intros X l; induction l as [| x l'].
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; rewrite rev_snoc; rewrite IHl'; reflexivity.
Qed.

Theorem snoc_with_append :
  forall {X : Set} (l1 l2 : list X) (v : X), snoc (l1 ++ l2) v = l1 ++ snoc l2 v.
Proof. intros X l1 l2 v; induction l1 as [| x l1'].
Case "l1 = []".     reflexivity.
Case "l1 = x::l1'". simpl; rewrite IHl1'; reflexivity.
Qed.

Inductive prod (X Y : Set) : Set :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Set} (p : X * Y) :=
  match p with (x, _) => x end.
Definition snd {X Y : Set} (p : X * Y) :=
  match p with (_, y) => y end.

Fixpoint combine {X Y : Set} (xs : list X) (ys : list Y) : list (X * Y) :=
  match xs, ys with
    | [],      _     => []
    | _,      []     => []
    | x::xs', y::ys' => (x, y) :: combine xs' ys'
  end.

Fixpoint split {X Y : Set} (ps : list (X * Y)) : (list X) * (list Y) :=
  match ps with
    | []          => ([], [])
    | (x, y)::ps' => let (xs', ys') := split ps' in (x::xs', y::ys')
  end.

Example test_split : split [(1, false); (2, false)] = ([1; 2], [false; false]).
Proof. reflexivity. Qed.

Inductive option (X : Set) : Set :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X : Set} (n : nat) (l : list X) : option X :=
  match n, l with
    | _,    []    => None
    | O,    x::l' => Some x
    | S n', x::l' => index n' l'
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Set} (l : list X) : option X :=
  match l with
    | []    => None
    | x::l' => Some x
  end.

Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Set} (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Set} (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with (x, y) => f x y end.

Theorem uncurry_curry :
  forall (X Y Z : Set) (f : X -> Y -> Z) x y, prod_curry (prod_uncurry f) x y = f x y.
Proof. reflexivity. Qed.

Theorem curry_uncurry :
  forall (X Y Z : Set) (f : X * Y -> Z) p, prod_uncurry (prod_curry f) p = f p.
Proof. destruct p as [x y]; reflexivity. Qed.

Fixpoint filter {X : Set} (p : X -> bool) (l : list X) : list X :=
  match l with
    | []    => []
    | x::l' => if p x then x :: filter p l' else filter p l'
  end.

Example test_filter1 : filter evenb [1; 2; 3; 4] = [2; 4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Set} (l : list X) : bool := beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat := length (filter oddb l).

Example test_countoddmembers'1 : countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2 : countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3 : countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (ble_nat 8 n)) l.

Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 : filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Set} (p : X -> bool) (l : list X) : list X * list X :=
  (filter p l, filter (fun x => negb (p x)) l).

Example test_partition1 : partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2 : partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Set} (f : X -> Y) (l : list X) : list Y :=
  match l with
    | []    => []
    | x::l' => f x :: map f l'
  end.

Example test_map1 : map (plus 3) [2; 0; 2] = [5; 3; 5].
Proof. reflexivity. Qed.
Example test_map2 : map oddb [2; 1; 2; 5] = [false; true; false; true].
Proof. reflexivity. Qed.
Example test_map3 : map (fun n => [evenb n; oddb n]) [2; 1; 2; 5] =
                    [[true; false]; [false; true]; [true; false]; [false; true]].
Proof. reflexivity. Qed.

Lemma map_snoc : forall {X Y : Set} (f : X -> Y) (v : X) (l: list X),
                   map f (snoc l v) = snoc (map f l) (f v).
Proof. intros X Y f v l; induction l as [| x l'].
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; rewrite IHl'; reflexivity.
Qed.

Theorem map_rev : forall {X Y : Set} (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
Proof. intros X Y f l; induction l as [| x l'].
Case "l = []".    reflexivity.
Case "l = x::l'". simpl; rewrite map_snoc; rewrite IHl'; reflexivity.
Qed.

Fixpoint flat_map {X Y : Set} (f : X -> list Y) (l : list X) : list Y :=
  match l with
    | []    => []
    | x::l' => f x ++ flat_map f l'
  end.

Example test_flat_map1 : flat_map (fun n => [n; n; n]) [1; 5; 4] =
                         [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Set} (f : X -> Y) (xo: option X) : option Y :=
  match xo with
    | None   => None
    | Some x => Some (f x)
  end.
