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

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | []      => O
    | n :: s' => match beq_nat v n with
                   | true  => S (count v s')
                   | false => count v s'
                 end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool := negb (beq_nat 0 (count v s)).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | []      => []
    | n :: s' => match beq_nat v n with
                   | true  => s'
                   | false => n :: remove_one v s'
                 end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
    | []      => []
    | n :: s' => match beq_nat v n with
                   | true  => remove_all v s'
                   | false => n :: remove_all v s'
                 end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1 s2 : bag) : bool :=
  match s1 with
    | []       => true
    | n :: s1' => match ble_nat (count n s1) (count n s2) with
                    | true  => subset s1' s2
                    | false => false
                  end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem add_increments_count : forall (s : bag) (v : nat), count v (add v s) = S (count v s).
Proof. intros s v; simpl; rewrite <- beq_nat_refl; reflexivity. Qed.

Theorem nil_app : forall l : natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist, length (tl l) = pred (length l).
Proof. intro l; destruct l as [| n l']; reflexivity. Qed.

Theorem app_ass : forall l1 l2 l3 : natlist, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof. intros l1 l2 l3; induction l1 as [| n l1'].
Case "l1 = []".     reflexivity.
Case "l1 = n::l1'". simpl; rewrite IHl1'; reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist, length (l1 ++ l2) = length l1 + length l2.
Proof. intros l1 l2; induction l1 as [| n l1'].
Case "l1 = []".     reflexivity.
Case "l1 = n::l1'". simpl; rewrite IHl1'; reflexivity.
Qed.

Fixpoint snoc (l : natlist) (v : nat) : natlist :=
  match l with
    | []      => [v]
    | n :: l' => n :: snoc l' v
  end.

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | []      => []
    | n :: l' => snoc (rev l') n
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc : forall (l : natlist) (v : nat), length (snoc l v) = S (length l).
Proof. intros l v; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl; rewrite IHl'; reflexivity.
Qed.

Theorem length_rev : forall l : natlist, length (rev l) = length l.
Proof. intro l; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl; rewrite <- IHl'; rewrite length_snoc; reflexivity.
Qed.

Theorem app_nil_end : forall l : natlist, l ++ [] = l.
Proof. intro l; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl; rewrite IHl'; reflexivity.
Qed.

Lemma rev_snoc : forall (l : natlist) (v : nat), rev (snoc l v) = v :: rev l.
Proof. intros l v; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl; rewrite IHl'; reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof. intro l; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl; rewrite rev_snoc; rewrite IHl'; reflexivity.
Qed.

Theorem app_ass4 :
  forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof. intros l1 l2 l3 l4; repeat rewrite app_ass; reflexivity. Qed.

Theorem snoc_append : forall (l : natlist) (v : nat), snoc l v = l ++ [v].
Proof. intros l v; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl. rewrite IHl'; reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist, rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof. intros l1 l2; induction l1 as [| n l1'].
Case "l1 = []".     simpl; rewrite app_nil_end; reflexivity.
Case "l1 = n::l1'". simpl; repeat rewrite snoc_append; rewrite IHl1';
                    rewrite app_ass; reflexivity.
Qed.

Lemma nonzeros_app :
  forall l1 l2 : natlist, nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2.
Proof. intros l1 l2; induction l1 as [| n l1'].
Case "l1 = []".     reflexivity.
Case "l1 = n::l1'". destruct n as [| n']; simpl; rewrite IHl1'; reflexivity.
Qed.

Theorem snoc_app_cons :
  forall (l1 l2 : natlist) (v : nat), (snoc l1 v) ++ l2 = l1 ++ (v :: l2).
Proof. intros l1 l2 v; rewrite snoc_append; rewrite <- app_ass; reflexivity. Qed.
