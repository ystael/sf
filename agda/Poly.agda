module Poly where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; inspect; [_])
open import Basics
open import SFInduction
open import Data.Nat renaming (_≤_ to leq-rel)
open import Lists

infixr 6 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

snoc : {A : Set} → List A → A → List A
snoc []       y = y ∷ []
snoc (x ∷ xs) y = x ∷ (snoc xs y)

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = snoc (reverse xs) x

repeat : {A : Set} → A → ℕ → List A
repeat _ zero    = []
repeat x (suc n) = x ∷ repeat x n

test-repeat-1 : repeat true 2 ≡ true ∷ true ∷ []
test-repeat-1 = refl

iden-++-left : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
iden-++-left _ = refl

reverse-snoc : {A : Set} → (y : A) → (xs : List A) → reverse (snoc xs y) ≡ y ∷ reverse xs
reverse-snoc _ []       = refl
reverse-snoc y (x ∷ xs) rewrite reverse-snoc y xs = refl

reverse-involutive : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive []       = refl
reverse-involutive (x ∷ xs) rewrite reverse-snoc x (reverse xs) | reverse-involutive xs = refl

snoc-++ : {A : Set} → (xs ys : List A) → (v : A) → snoc (xs ++ ys) v ≡ xs ++ snoc ys v
snoc-++ []       _  _ = refl
snoc-++ (x ∷ xs) ys v rewrite snoc-++ xs ys v = refl

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

fst : {A B : Set} → A × B → A
fst ⟨ a , _ ⟩ = a

snd : {A B : Set} → A × B → B
snd ⟨ _ , b ⟩ = b

zip : {A B : Set} → List A → List B → List (A × B)
zip []       _        = []
zip _        []       = []
zip (a ∷ as) (b ∷ bs) = ⟨ a , b ⟩ ∷ zip as bs

unzip : {A B : Set} → List (A × B) → List A × List B
unzip [] = ⟨ [] , [] ⟩
unzip (⟨ a , b ⟩ ∷ ps) with unzip ps
... | ⟨ as , bs ⟩ = ⟨ a ∷ as , b ∷ bs ⟩

test-unzip : unzip (⟨ 1 , false ⟩ ∷ ⟨ 2 , false ⟩ ∷ []) ≡ ⟨ 1 ∷ 2 ∷ [] , false ∷ false ∷ [] ⟩
test-unzip = refl

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

_‼_ : {A : Set} → List A → ℕ → Maybe A
[]       ‼ _       = nothing
(x ∷ xs) ‼ zero    = just x
(x ∷ xs) ‼ (suc n) = xs ‼ n

test-index-1 : (4 ∷ 5 ∷ 6 ∷ 7 ∷ []) ‼ 0 ≡ just 4
test-index-1 = refl
test-index-2 : ((1 ∷ []) ∷ (2 ∷ []) ∷ []) ‼ 1 ≡ just (2 ∷ [])
test-index-2 = refl
test-index-3 : (true ∷ []) ‼ 2 ≡ nothing
test-index-3 = refl

hd-maybe : {A : Set} → List A → Maybe A
hd-maybe []       = nothing
hd-maybe (x ∷ xs) = just x

test-hd-maybe-1 : hd-maybe (1 ∷ 2 ∷ []) ≡ just 1
test-hd-maybe-1 = refl
test-hd-maybe-2 : hd-maybe ((1 ∷ []) ∷ (2 ∷ []) ∷ []) ≡ just (1 ∷ [])
test-hd-maybe-2 = refl
