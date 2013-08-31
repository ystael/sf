module Basics where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
