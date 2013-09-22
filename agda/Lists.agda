module Lists where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Basics
open import SFInduction
open import Data.Nat renaming (_≤_ to leq-rel)

module NatList where

  data ℕProd : Set where
    ⟨_,_⟩ : ℕ → ℕ → ℕProd

  fst : ℕProd → ℕ
  fst ⟨ x , _ ⟩ = x

  snd : ℕProd → ℕ
  snd ⟨ _ , y ⟩ = y

  swap-pair : ℕProd → ℕProd
  swap-pair ⟨ x , y ⟩ = ⟨ y , x ⟩

  surjective-pairing : ∀ p → p ≡ ⟨ fst p , snd p ⟩
  surjective-pairing ⟨ x , y ⟩ = refl

  snd-fst-is-swap : ∀ p → ⟨ snd p , fst p ⟩ ≡ swap-pair p
  snd-fst-is-swap ⟨ x , y ⟩ = refl

  fst-swap-is-snd : ∀ p → fst (swap-pair p) ≡ snd p
  fst-swap-is-snd ⟨ x , y ⟩ = refl

  infixr 6 _∷_
  data ℕList : Set where
    []   : ℕList
    _∷_ : ℕ → ℕList → ℕList

  repeat : ℕ → ℕ → ℕList
  repeat n zero    = []
  repeat n (suc k) = n ∷ repeat n k

  length : ℕList → ℕ
  length []       = zero
  length (n ∷ ns) = suc (length ns)

  infixr 5 _++_
  _++_ : ℕList → ℕList → ℕList
  []       ++ l = l
  (n ∷ ns) ++ l = n ∷ (ns ++ l)

  test-++-1 : 1 ∷ 2 ∷ 3 ∷ [] ++ 4 ∷ 5 ∷ [] ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  test-++-1 = refl

  test-++-2 : [] ++ 4 ∷ 5 ∷ [] ≡ 4 ∷ 5 ∷ []
  test-++-2 = refl

  test-++-3 : 1 ∷ 2 ∷ 3 ∷ [] ++ [] ≡ 1 ∷ 2 ∷ 3 ∷ []
  test-++-3 = refl

  hd : ℕ → ℕList → ℕ
  hd default []      = default
  hd default (n ∷ _) = n

  tl : ℕList → ℕList
  tl []       = []
  tl (_ ∷ ns) = ns

  test-hd-1 : hd 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 1
  test-hd-1 = refl

  test-hd-2 : hd 0 [] ≡ 0
  test-hd-2 = refl

  test-tl-1 : tl (1 ∷ 2 ∷ 3 ∷ []) ≡ 2 ∷ 3 ∷ []
  test-tl-1 = refl

  nonzeros : ℕList → ℕList
  nonzeros []             = []
  nonzeros (zero ∷ ns)    = nonzeros ns
  nonzeros ((suc n) ∷ ns) = (suc n) ∷ nonzeros ns

  test-nonzeros : nonzeros (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
  test-nonzeros = refl

  odd-members : ℕList → ℕList
  odd-members [] = []
  odd-members (n ∷ ns) with odd n
  ... | true  = n ∷ odd-members ns
  ... | false = odd-members ns

  test-odd-members : odd-members (0 ∷ 1 ∷ 0 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ []) ≡ 1 ∷ 3 ∷ []
  test-odd-members = refl

  count-odd-members : ℕList → ℕ
  count-odd-members [] = zero
  count-odd-members (n ∷ ns) with odd n
  ... | true  = suc (count-odd-members ns)
  ... | false = count-odd-members ns

  test-count-odd-members-1 : count-odd-members (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
  test-count-odd-members-1 = refl
  test-count-odd-members-2 : count-odd-members (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
  test-count-odd-members-2 = refl
  test-count-odd-members-3 : count-odd-members [] ≡ 0
  test-count-odd-members-3 = refl

  alternate : ℕList → ℕList → ℕList
  alternate []       ns       = ns
  alternate (m ∷ ms) []       = m ∷ ms
  alternate (m ∷ ms) (n ∷ ns) = m ∷ n ∷ alternate ms ns

  test-alternate-1 : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ 1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ 6 ∷ []
  test-alternate-1 = refl
  test-alternate-2 : alternate (1 ∷ []) (4 ∷ 5 ∷ 6 ∷ []) ≡ 1 ∷ 4 ∷ 5 ∷ 6 ∷ []
  test-alternate-2 = refl
  test-alternate-3 : alternate (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ []) ≡ 1 ∷ 4 ∷ 2 ∷ 3 ∷ []
  test-alternate-3 = refl
  test-alternate-4 : alternate [] (20 ∷ 30 ∷ []) ≡ 20 ∷ 30 ∷ []
  test-alternate-4 = refl

  Bag : Set
  Bag = ℕList

  count : ℕ → Bag → ℕ
  count v []       = 0
  count v (n ∷ ns) with v =ℕ= n
  ... | true  = suc (count v ns)
  ... | false = count v ns

  test-count-1 : count 1 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 3
  test-count-1 = refl
  test-count-2 : count 6 (1 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ 0
  test-count-2 = refl

  sum : Bag → Bag → Bag
  sum = _++_

  test-sum-1 : count 1 (sum (1 ∷ 2 ∷ 3 ∷ []) (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
  test-sum-1 = refl

  add : ℕ → Bag → Bag
  add = _∷_

  test-add-1 : count 1 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 3
  test-add-1 = refl
  test-add-2 : count 5 (add 1 (1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-add-2 = refl

  member : ℕ → Bag → Bool
  member v s = ¬ (0 =ℕ= count v s)

  test-member-1 : member 1 (1 ∷ 4 ∷ 1 ∷ []) ≡ true
  test-member-1 = refl
  test-member-2 : member 2 (1 ∷ 4 ∷ 1 ∷ []) ≡ false
  test-member-2 = refl

  remove-one : ℕ → Bag → Bag
  remove-one v [] = []
  remove-one v (n ∷ ns) with v =ℕ= n
  ... | true  = ns
  ... | false = n ∷ remove-one v ns

  test-remove-one-1 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-one-1 = refl
  test-remove-one-2 : count 5 (remove-one 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-one-2 = refl
  test-remove-one-3 : count 4 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ 4 ∷ [])) ≡ 2
  test-remove-one-3 = refl
  test-remove-one-4 : count 5 (remove-one 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 1
  test-remove-one-4 = refl

  remove-all : ℕ → Bag → Bag
  remove-all v [] = []
  remove-all v (n ∷ ns) with v =ℕ= n
  ... | true  = remove-all v ns
  ... | false = n ∷ remove-all v ns

  test-remove-all-1 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-all-1 = refl
  test-remove-all-2 : count 5 (remove-all 5 (2 ∷ 1 ∷ 4 ∷ 1 ∷ [])) ≡ 0
  test-remove-all-2 = refl
  test-remove-all-3 : count 4 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 1 ∷ 4 ∷ [])) ≡ 2
  test-remove-all-3 = refl
  test-remove-all-4 : count 5 (remove-all 5 (2 ∷ 1 ∷ 5 ∷ 4 ∷ 5 ∷ 1 ∷ 4 ∷ [])) ≡ 0
  test-remove-all-4 = refl

  subset : Bag → Bag → Bool
  subset []       _  = true
  subset (n ∷ ns) ms with count n (n ∷ ns) ≤ count n ms
  ... | true  = subset ns ms
  ... | false = false

  test-subset-1 : subset (1 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ true
  test-subset-1 = refl
  test-subset-2 : subset (1 ∷ 2 ∷ 2 ∷ []) (2 ∷ 1 ∷ 4 ∷ 1 ∷ []) ≡ false
  test-subset-2 = refl

  add-increments-count : ∀ s v → count v (add v s) ≡ suc (count v s)
  add-increments-count s v rewrite =ℕ=-refl v = refl
