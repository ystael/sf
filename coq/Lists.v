Require Export Induction.

Module NatList.

Inductive natprod : Set :=
  | pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
    | pair x _ => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
    | pair _ y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x, y) => (y, x)
  end.

Theorem surjective_pairing : forall p : natprod, p = (fst p, snd p).
Proof. intro p; destruct p as [x y]; reflexivity. Qed.

Theorem snd_fst_is_swap : forall p : natprod, (snd p, fst p) = swap_pair p.
Proof. intro p; destruct p as [x y]; reflexivity. Qed.

Theorem fst_swap_is_snd : forall p : natprod, fst (swap_pair p) = snd p.
Proof. intro p; destruct p as [x y]; reflexivity. Qed.

Inductive natlist : Set :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O        => []
    | S count' => n :: repeat n count'
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
    | []      => 0
    | n :: l' => S (length l')
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | []       => l2
    | n :: l1' => n :: app l1' l2
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | []     => default
    | n :: _ => n
  end.

Definition tl (l : natlist) : natlist :=
  match l with
    | []      => []
    | _ :: l' => l'
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
    | []          => []
    | O     :: l' => nonzeros l'
    | (S n) :: l' => (S n) :: nonzeros l'
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
    | []      => []
    | n :: l' => match (oddb n) with
                   | true  => n :: oddmembers l'
                   | false => oddmembers l'
                 end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
  match l with
    | []      => O
    | n :: l' => match (oddb n) with
                   | true  => S (countoddmembers l')
                   | false => countoddmembers l'
                 end
  end.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
    | []        => l2
    | n1 :: l1' => match l2 with
                     | []        => l1
                     | n2 :: l2' => n1 :: n2 :: alternate l1' l2'
                   end
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
