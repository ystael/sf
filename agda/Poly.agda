module Poly where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; inspect; [_])
open import Basics
open import SFInduction
open import Data.Nat renaming (_≤_ to leq-rel)
open import Lists
open import Function using (_∘_)

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

curry : {A B C : Set} (f : A × B → C) → A → B → C
curry f a b = f ⟨ a , b ⟩

uncurry : {A B C : Set} (f : A → B → C) → A × B → C
uncurry f ⟨ a , b ⟩ = f a b

uncurry-curry : {A B C : Set} → (f : A → B → C) →
                (a : A) → (b : B) → curry (uncurry f) a b ≡ f a b
uncurry-curry f a b = refl

curry-uncurry : {A B C : Set} → (f : A × B → C) →
                (p : A × B) → uncurry (curry f) p ≡ f p
curry-uncurry f ⟨ a , b ⟩ = refl

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

test-filter-1 : filter even (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 2 ∷ 4 ∷ []
test-filter-1 = refl

length-is-1 : {A : Set} → List A → Bool
length-is-1 xs = length xs =ℕ= 1

test-filter-2 : filter length-is-1 ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ (4 ∷ []) ∷
                                    (5 ∷ 6 ∷ 7 ∷ []) ∷ [] ∷ (8 ∷ []) ∷ [])
                ≡ (3 ∷ []) ∷ (4 ∷ []) ∷ (8 ∷ []) ∷ []
test-filter-2 = refl

count-odd-members′ : List ℕ → ℕ
count-odd-members′ xs = length (filter odd xs)

test-count-odd-members′-1 : count-odd-members′ (1 ∷ 0 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ []) ≡ 4
test-count-odd-members′-1 = refl
test-count-odd-members′-2 : count-odd-members′ (0 ∷ 2 ∷ 4 ∷ []) ≡ 0
test-count-odd-members′-2 = refl
test-count-odd-members′-3 : count-odd-members′ [] ≡ 0
test-count-odd-members′-3 = refl

filter-even->7 : List ℕ → List ℕ
filter-even->7 = filter (λ n → (even n) ∧ (8 ≤ n))

test-filter-even->7-1 : filter-even->7 (1 ∷ 2 ∷ 6 ∷ 9 ∷ 10 ∷ 3 ∷ 12 ∷ 8 ∷ []) ≡ 10 ∷ 12 ∷ 8 ∷ []
test-filter-even->7-1 = refl
test-filter-even->7-2 : filter-even->7 (5 ∷ 2 ∷ 6 ∷ 19 ∷ 129 ∷ []) ≡ []
test-filter-even->7-2 = refl

partition : {A : Set} → (A → Bool) → List A → (List A) × (List A)
partition p xs = ⟨ filter p xs , filter (¬ ∘ p) xs ⟩

test-partition-1 : partition odd (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ ⟨ 1 ∷ 3 ∷ 5 ∷ [] , 2 ∷ 4 ∷ [] ⟩
test-partition-1 = refl
test-partition-2 : partition (λ _ → false) (5 ∷ 9 ∷ 0 ∷ []) ≡ ⟨ [] , 5 ∷ 9 ∷ 0 ∷ [] ⟩
test-partition-2 = refl

map : {A B : Set} → (A → B) → List A → List B
map _ []       = []
map f (a ∷ as) = f a ∷ map f as

test-map-1 : map (_+_ 3) (2 ∷ 0 ∷ 2 ∷ []) ≡ 5 ∷ 3 ∷ 5 ∷ []
test-map-1 = refl
test-map-2 : map odd (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡ false ∷ true ∷ false ∷ true ∷ []
test-map-2 = refl
test-map-3 : map (λ n → even n ∷ odd n ∷ []) (2 ∷ 1 ∷ 2 ∷ 5 ∷ []) ≡
             (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷
             (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ []
test-map-3 = refl

map-snoc : {A B : Set} → (f : A → B) → (v : A) → (xs : List A) →
           map f (snoc xs v) ≡ snoc (map f xs) (f v)
map-snoc _ _ []       = refl
map-snoc f v (x ∷ xs) rewrite map-snoc f v xs = refl

map-reverse : {A B : Set} → (f : A → B) → (xs : List A) →
              map f (reverse xs) ≡ reverse (map f xs)
map-reverse _ []       = refl
map-reverse f (x ∷ xs) rewrite map-snoc f x (reverse xs) | map-reverse f xs = refl

flatmap : {A B : Set} → (A → List B) → List A → List B
flatmap _ []       = []
flatmap f (x ∷ xs) = f x ++ flatmap f xs

test-flatmap-1 : flatmap (λ n → n ∷ n ∷ n ∷ []) (1 ∷ 5 ∷ 4 ∷ []) ≡
                 1 ∷ 1 ∷ 1 ∷ 5 ∷ 5 ∷ 5 ∷ 4 ∷ 4 ∷ 4 ∷ []
test-flatmap-1 = refl

option-map : {A B : Set} → (A → B) → Maybe A → Maybe B
option-map _ nothing  = nothing
option-map f (just x) = just (f x)

foldr : {A B : Set} → (f : A → B → B) → (z : B) → (xs : List A) → B
foldr _ z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldr-example-1 : foldr _*_ 1 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 24
foldr-example-1 = refl
foldr-example-2 : foldr _∧_ true (true ∷ true ∷ false ∷ true ∷ []) ≡ false
foldr-example-2 = refl
foldr-example-3 : foldr _++_ [] ((1 ∷ []) ∷ [] ∷ (2 ∷ 3 ∷ []) ∷ (4 ∷ []) ∷ [])
                  ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
foldr-example-3 = refl

constantly : {A : Set} → A → ℕ → A
constantly x = λ _ → x

ftrue : ℕ → Bool
ftrue = constantly true

constantly-example-1 : ftrue 0 ≡ true
constantly-example-1 = refl
constantly-example-2 : (constantly 5) 99 ≡ 5
constantly-example-2 = refl

override : {A : Set} → (ℕ → A) → ℕ → A → ℕ → A
override f k x k′ with k =ℕ= k′
... | true  = x
... | false = f k′

f-mostly-true : ℕ → Bool
f-mostly-true = override (override ftrue 1 false) 3 false

override-example-1 : f-mostly-true 0 ≡ true
override-example-1 = refl
override-example-2 : f-mostly-true 1 ≡ false
override-example-2 = refl
override-example-3 : f-mostly-true 2 ≡ true
override-example-3 = refl
override-example-4 : f-mostly-true 3 ≡ false
override-example-4 = refl

override-example : (b : Bool) → (override (constantly b) 3 true) 2 ≡ b
override-example _ = refl

plus-3 : ℕ → ℕ
plus-3 n = 3 + n

unfold-example : {n m : ℕ} → 3 + n ≡ m → plus-3 n + 1 ≡ m + 1
unfold-example refl = refl

override-= : {A : Set} → (f : ℕ → A) → (k : ℕ) → (x : A) → (override f k x) k ≡ x
override-= f k x rewrite =ℕ=-refl k = refl

override-≠ : {A : Set} → {x1 x2 : A} → {k1 k2 : ℕ} → (f : ℕ → A) →
             f k1 ≡ x1 → k2 =ℕ= k1 ≡ false → (override f k2 x2) k1 ≡ x1
override-≠ f pf₁ pf₂ rewrite pf₂ | pf₁ = refl

foldr-length : {A : Set} → List A → ℕ
foldr-length = foldr (λ _ n → suc n) 0

test-foldr-length-1 : foldr-length (4 ∷ 7 ∷ 0 ∷ []) ≡ 3
test-foldr-length-1 = refl

foldr-length-correct : {A : Set} → (xs : List A) → foldr-length xs ≡ length xs
foldr-length-correct []       = refl
foldr-length-correct (x ∷ xs) rewrite foldr-length-correct xs = refl

foldr-map : {A B : Set} → (A → B) → List A → List B
foldr-map f = foldr (λ x ys → (f x) ∷ ys) []

foldr-map-correct : {A B : Set} → (f : A → B) → (xs : List A) → foldr-map f xs ≡ map f xs
foldr-map-correct _ []       = refl
foldr-map-correct f (x ∷ xs) rewrite foldr-map-correct f xs = refl
