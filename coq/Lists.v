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

Theorem count_member_nonzero : forall (s : bag) (v : nat), ble_nat 1 (count v (v :: s)) = true.
Proof. intros s v; simpl; rewrite <- beq_nat_refl; reflexivity.
Qed.

Theorem ble_n_Sn : forall n : nat, ble_nat n (S n) = true.
Proof. intro n; induction n as [| n'].
Case "n = 0".    reflexivity.
Case "n = S n'". simpl; exact IHn'.
Qed.

(* This actually appears somewhat more subtle if you try to replace 0 by (v : nat).
 * Instead of destructing n, you need to destruct (beq_nat v n), but there are three
 * occurrences of this in the theorem and one of them is behind the reduction of
 * count v (remove_one v s).  One needs some way to retain the case-analyzed value of
 * beq_nat v n in the context, which I don't know how to do. *)
Theorem remove_decreases_count :
  forall (s : bag), ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof. intro s; induction s as [| n s'].
Case "s = []".    reflexivity.
Case "s = n::s'". simpl; destruct n as [| n'].
 SCase "n = 0".    apply ble_n_Sn.
 SCase "n = S n'". simpl; exact IHs'.
Qed.

(* To solve the problem above, use the eqn: clause of destruct which retains the case info. *)
Theorem remove_decreases_count' :
  forall (s : bag) (v : nat), ble_nat (count v (remove_one v s)) (count v s) = true.
Proof. intros s v; induction s as [| n s'].
Case "s = []".    reflexivity.
Case "s = n::s'". simpl; destruct (beq_nat v n) eqn: nH.
 SCase "v = n".  apply ble_n_Sn.
 SCase "v /= n". simpl; rewrite nH; exact IHs'.
Qed.

Theorem sum_adds_count :
  forall (v : nat) (s1 s2 : bag), count v (sum s1 s2) = count v s1 + count v s2.
Proof. intros v s1 s2; induction s1 as [| n s1'].
Case "s1 = []".     reflexivity.
Case "s1 = n::s1'". simpl; destruct (beq_nat v n); rewrite IHs1'; reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof. intros l1 l2 H; rewrite <- (rev_involutive l1); rewrite <- (rev_involutive l2);
       rewrite H; reflexivity.
Qed.

Inductive natoption : Set :=
| Some : nat -> natoption
| None : natoption.

Fixpoint index (i : nat) (l : natlist) : natoption :=
  match l with
    | []    => None
    | n::l' => match i with
                 | O    => Some n
                 | S i' => index i' l'
               end
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
    | Some n => n
    | None   => d
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with
    | []   => None
    | n::_ => Some n
  end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd :
  forall (l : natlist) (default : nat), hd default l = option_elim default (hd_opt l).
Proof. intros l default; destruct l as [| n l']; reflexivity. Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | [],      []      => true
    | n1::l1', n2::l2' => andb (beq_nat n1 n2) (beq_natlist l1' l2')
    | _,       _       => false
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.
Example test_beq_natlist4 : beq_natlist [1;2;3] [1;2] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist, true = beq_natlist l l.
Proof. intro l; induction l as [| n l'].
Case "l = []".    reflexivity.
Case "l = n::l'". simpl; rewrite <- beq_nat_refl; rewrite <- IHl'; reflexivity.
Qed.

Module Dictionary.

Inductive dictionary : Set :=
| empty : dictionary
| record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  record key value d.

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
    | empty         => None
    | record k v d' => if beq_nat key k
                         then Some v
                         else find key d'
  end.

Theorem dictionary_invariant1 :
  forall (d : dictionary) (k v : nat), find k (insert k v d) = Some v.
Proof. intros d k v; simpl; rewrite <- beq_nat_refl; reflexivity. Qed.

Theorem dictionary_invariant2 :
  forall (d : dictionary) (k k' v : nat),
    beq_nat k k' = false -> find k d = find k (insert k' v d).
Proof. intros d k k' v Hneq; simpl; rewrite Hneq; reflexivity. Qed.
