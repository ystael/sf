module Basics where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _*_)

data Day : Set where
  monday    : Day
  tuesday   : Day
  wednesday : Day
  thursday  : Day
  friday    : Day
  saturday  : Day
  sunday    : Day

next-weekday : Day → Day
next-weekday monday    = tuesday
next-weekday tuesday   = wednesday
next-weekday wednesday = thursday
next-weekday thursday  = friday
next-weekday friday    = monday
next-weekday saturday  = monday
next-weekday sunday    = monday

test-next-weekday : next-weekday (next-weekday saturday) ≡ tuesday
test-next-weekday = refl

data Bool : Set where
  true  : Bool
  false : Bool

¬ : Bool → Bool
¬ true  = false
¬ false = true

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

test-∨-1 : true ∨ true ≡ true
test-∨-1 = refl
test-∨-2 : true ∨ false ≡ true
test-∨-2 = refl
test-∨-3 : false ∨ true ≡ true
test-∨-3 = refl
test-∨-4 : false ∨ false ≡ false
test-∨-4 = refl

_nand_ : Bool → Bool → Bool
true  nand _ = false
false nand b = ¬ b

test-nand-1 : true nand true ≡ false
test-nand-1 = refl
test-nand-2 : true nand false ≡ false
test-nand-2 = refl
test-nand-3 : false nand true ≡ false
test-nand-3 = refl
test-nand-4 : false nand false ≡ true
test-nand-4 = refl

∧₃ : Bool → Bool → Bool → Bool
∧₃ true  b c = b ∧ c
∧₃ false _ _ = false

test-∧₃-1 : ∧₃ true true true ≡ true
test-∧₃-1 = refl
test-∧₃-2 : ∧₃ false true true ≡ false
test-∧₃-2 = refl
test-∧₃-3 : ∧₃ true false true ≡ false
test-∧₃-3 = refl
test-∧₃-4 : ∧₃ true true false ≡ false
test-∧₃-4 = refl

module Playground1 where
  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  pred : Nat -> Nat
  pred zero     = zero
  pred (succ n) = n

minus-two : ℕ → ℕ
minus-two zero          = zero
minus-two (suc zero)    = zero
minus-two (suc (suc n)) = n

even : ℕ → Bool
even zero          = true
even (suc zero)    = false
even (suc (suc n)) = even n

odd : ℕ → Bool
odd n = ¬ (even n)

test-odd-1 : odd (suc zero) ≡ true
test-odd-1 = refl
test-odd-2 : odd 4 ≡ false
test-odd-2 = refl

module Playground2 where
  _+_ : ℕ → ℕ → ℕ
  zero    + m = m
  (suc n) + m = suc (n + m)

  _×_ : ℕ → ℕ → ℕ
  zero    × m = zero
  (suc n) × m = m + (n × m)

  test-×-1 : 3 × 3 ≡ 9
  test-×-1 = refl

  _−_ : ℕ → ℕ → ℕ
  zero    − _       = zero
  n       − zero    = n
  (suc n) − (suc m) = n − m

_^_ : ℕ → ℕ → ℕ
_ ^ zero    = suc zero
b ^ (suc p) = b * (b ^ p)

factorial : ℕ → ℕ
factorial zero    = suc zero
factorial (suc n) = (suc n) * factorial n

test-factorial-1 : factorial 3 ≡ 6
test-factorial-1 = refl
test-factorial-2 : factorial 5 ≡ 120
test-factorial-2 = refl

_=ℕ=_ : ℕ → ℕ → Bool
zero    =ℕ= zero    = true
zero    =ℕ= (suc m) = false
(suc n) =ℕ= zero    = false
(suc n) =ℕ= (suc m) = n =ℕ= m

_≤_ : ℕ → ℕ → Bool
zero    ≤ _       = true
(suc n) ≤ zero    = false
(suc n) ≤ (suc m) = n ≤ m

test-≤-1 : 2 ≤ 2 ≡ true
test-≤-1 = refl
test-≤-2 : 2 ≤ 4 ≡ true
test-≤-2 = refl
test-≤-3 : 4 ≤ 2 ≡ false
test-≤-3 = refl

_<_ : ℕ → ℕ → Bool
n < m = (suc n) ≤ m

test-<-1 : 2 < 2 ≡ false
test-<-1 = refl
test-<-2 : 2 < 4 ≡ true
test-<-2 = refl
test-<-3 : 4 < 2 ≡ false
test-<-3 = refl

open Playground2 using (_+_)

iden-+-left : ∀ {n} → 0 + n ≡ n
iden-+-left = refl

inc-+-left : ∀ {n} → 1 + n ≡ (suc n)
inc-+-left = refl

absorb-*-left : ∀ {n} → 0 * n ≡ 0
absorb-*-left = refl

id-+-example : ∀ {n m} → n ≡ m → n + n ≡ m + m
id-+-example refl = refl

id-+-exercise : ∀ {n m o} → n ≡ m → m ≡ o → n + m ≡ m + o
id-+-exercise refl refl = refl

*-zero-+ : ∀ {n m} → (0 + n) * m ≡ n * m
*-zero-+ {n} with iden-+-left {n}
*-zero-+ | refl = refl

*-suc-1 : ∀ {n m} → m ≡ suc n → m * (1 + n) ≡ m * m
*-suc-1 {n} pf with inc-+-left {n}
*-suc-1 {n} refl | refl = refl

+-1-not-zero : ∀ {n} → (n + 1) =ℕ= 0 ≡ false
+-1-not-zero {zero}  = refl
+-1-not-zero {suc n} = refl

¬-involutive : ∀ {b} → ¬ (¬ b) ≡ b
¬-involutive {true}  = refl
¬-involutive {false} = refl

zero-neq-+-1 : ∀ {n} → 0 =ℕ= (n + 1) ≡ false
zero-neq-+-1 {zero}  = refl
zero-neq-+-1 {suc n} = refl

identity-applied-twice : {f : Bool → Bool} →
                         ((x : Bool) → f x ≡ x) → (b : Bool) → f (f b) ≡ b
identity-applied-twice {f} f-is-id b rewrite f-is-id (f b) | f-is-id b = refl

∧-eq-∨ : ∀ {b c} → b ∧ c ≡ b ∨ c → b ≡ c
∧-eq-∨ {true}  {true}  refl = refl
∧-eq-∨ {true}  {false} ()
∧-eq-∨ {false} {true}  ()
∧-eq-∨ {false} {false} refl = refl

data BinNat : Set where
  zz : BinNat           -- zero
  ee : BinNat -> BinNat -- ee n = 2n
  oo : BinNat -> BinNat -- oo n = 2n + 1

bin-suc : BinNat -> BinNat
bin-suc zz     = oo zz
bin-suc (ee n) = oo n
bin-suc (oo n) = ee (bin-suc n)

nat→bin : ℕ → BinNat
nat→bin zero    = zz
nat→bin (suc n) = bin-suc (nat→bin n)

bin→nat : BinNat → ℕ
bin→nat zz     = zero
bin→nat (ee n) = 2 * bin→nat n
-- This isn't suc (bin→nat (ee n)) because that isn't structurally decreasing
bin→nat (oo n) = suc (2 * (bin→nat n))

test-bin→nat-1 : bin→nat (oo (ee (oo (ee (oo zz))))) ≡ 21
test-bin→nat-1 = refl
test-bin→nat-2 : bin→nat (ee (ee (ee zz))) ≡ 0
test-bin→nat-2 = refl
test-bin→nat-suc : suc (bin→nat (oo (oo (oo (ee (oo zz)))))) ≡
                    bin→nat (bin-suc (oo (oo (oo (ee (oo zz))))))
test-bin→nat-suc = refl
