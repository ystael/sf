module Lists where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
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

  iden-++-left : ∀ ns → [] ++ ns ≡ ns
  iden-++-left _ = refl

  tl-length-pred : ∀ ns → length (tl ns) ≡ pred (length ns)
  tl-length-pred []       = refl
  tl-length-pred (n ∷ ns) = refl

  assoc-++ : ∀ l₁ l₂ l₃ → l₁ ++ (l₂ ++ l₃) ≡ (l₁ ++ l₂) ++ l₃
  assoc-++ []       _  _  = refl
  assoc-++ (_ ∷ ns) l₂ l₃ rewrite assoc-++ ns l₂ l₃ = refl

  length-++ : ∀ l₁ l₂ → length (l₁ ++ l₂) ≡ length l₁ + length l₂
  length-++ []       _  = refl
  length-++ (_ ∷ ns) l₂ rewrite length-++ ns l₂ = refl

  snoc : ℕList → ℕ → ℕList
  snoc []       v = v ∷ []
  snoc (n ∷ ns) v = n ∷ snoc ns v

  reverse : ℕList → ℕList
  reverse []       = []
  reverse (n ∷ ns) = snoc (reverse ns) n

  test-reverse-1 : reverse (1 ∷ 2 ∷ 3 ∷ []) ≡ 3 ∷ 2 ∷ 1 ∷ []
  test-reverse-1 = refl
  test-reverse-2 : reverse [] ≡ []
  test-reverse-2 = refl

  length-snoc : ∀ ns v → length (snoc ns v) ≡ suc (length ns)
  length-snoc []       _ = refl
  length-snoc (_ ∷ ns) v rewrite length-snoc ns v = refl

  length-reverse : ∀ ns → length (reverse ns) ≡ length ns
  length-reverse []       = refl
  length-reverse (n ∷ ns) rewrite length-snoc (reverse ns) n | length-reverse ns = refl

  iden-++-right : ∀ ns → ns ++ [] ≡ ns
  iden-++-right []       = refl
  iden-++-right (_ ∷ ns) rewrite iden-++-right ns = refl

  reverse-snoc : ∀ ns v → reverse (snoc ns v) ≡ v ∷ reverse ns
  reverse-snoc []       _ = refl
  reverse-snoc (_ ∷ ns) v rewrite reverse-snoc ns v = refl

  reverse-involutive : ∀ ns → reverse (reverse ns) ≡ ns
  reverse-involutive []       = refl
  reverse-involutive (n ∷ ns) rewrite reverse-snoc (reverse ns) n
                                    | reverse-involutive ns = refl

  assoc-++-4 : ∀ l₁ l₂ l₃ l₄ → l₁ ++ (l₂ ++ (l₃ ++ l₄)) ≡ ((l₁ ++ l₂) ++ l₃) ++ l₄
  assoc-++-4 l₁ l₂ l₃ l₄ rewrite assoc-++ l₁ l₂ (l₃ ++ l₄)
                               | assoc-++ (l₁ ++ l₂) l₃ l₄ = refl

  snoc-++ : ∀ ns v → snoc ns v ≡ ns ++ (v ∷ [])
  snoc-++ []       _ = refl
  snoc-++ (_ ∷ ns) v rewrite snoc-++ ns v = refl

  distrib-reverse : ∀ ns ms → reverse (ns ++ ms) ≡ reverse ms ++ reverse ns
  distrib-reverse []       ms rewrite iden-++-right (reverse ms) = refl
  distrib-reverse (n ∷ ns) ms rewrite snoc-++ (reverse (ns ++ ms)) n
                                    | snoc-++ (reverse ns) n
                                    | distrib-reverse ns ms
                                    | assoc-++ (reverse ms) (reverse ns) (n ∷ []) = refl

  nonzeros-++ : ∀ ns ms → nonzeros (ns ++ ms) ≡ nonzeros ns ++ nonzeros ms
  nonzeros-++ []             _  = refl
  nonzeros-++ (zero    ∷ ns) ms rewrite nonzeros-++ ns ms = refl
  nonzeros-++ ((suc n) ∷ ns) ms rewrite nonzeros-++ ns ms = refl

  snoc-++-cons : ∀ ns ms v → (snoc ns v) ++ ms ≡ ns ++ (v ∷ ms)
  snoc-++-cons ns ms v rewrite snoc-++ ns v 
                             | sym (assoc-++ ns (v ∷ []) ms) = refl

  count-member-nonzero : (ns : Bag) → (v : ℕ) → 1 ≤ count v (v ∷ ns) ≡ true
  count-member-nonzero _ v rewrite =ℕ=-refl v = refl

  n-≤-suc-n : ∀ n → n ≤ suc n ≡ true
  n-≤-suc-n zero    = refl
  n-≤-suc-n (suc n) = n-≤-suc-n n

  -- This appears more difficult if you try to replace 0 by (v : ℕ).  See comments in the Coq
  -- source for why; an analogous issue appears (rather than pattern matching on the first
  -- element of ns, you attach "with v =ℕ= n", which needs to be used after it has been
  -- 'discharged').
  remove-decreases-count : (ns : Bag) → count 0 (remove-one 0 ns) ≤ count 0 ns ≡ true
  remove-decreases-count []             = refl
  remove-decreases-count (zero    ∷ ns) rewrite n-≤-suc-n (count 0 ns)    = refl
  remove-decreases-count ((suc n) ∷ ns) rewrite remove-decreases-count ns = refl

  sum-adds-count : (v : ℕ) → (ns ms : Bag) → count v (sum ns ms) ≡ count v ns + count v ms
  sum-adds-count _ []       _  = refl
  sum-adds-count v (n ∷ ns) ms with v =ℕ= n
  ... | true  rewrite sum-adds-count v ns ms = refl
  ... | false rewrite sum-adds-count v ns ms = refl

  -- This is harder to do with Agda's rewrite feature because it doesn't do very well at
  -- introducing facts of the form x ≡ f x to the unifier; see issue 520 at
  -- http://code.google.com/p/agda/issues/detail?id=520 .  It turns out to be easier to
  -- construct the proof term explicitly with trans.
  reverse-injective : ∀ ns ms → reverse ns ≡ reverse ms → ns ≡ ms
  reverse-injective ns ms pf = trans (sym (reverse-involutive ns))
                                     (trans rev-pf (reverse-involutive ms))
    where rev-pf : reverse (reverse ns) ≡ reverse (reverse ms)
          rev-pf rewrite pf = refl
