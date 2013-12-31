module MoreCoq where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; inspect; [_])
open import Data.Nat renaming (_≤_ to leq-rel)
open import Data.Empty
open import Basics
open import SFInduction
open import Poly

silly1 : {n m o p : ℕ} → n ≡ m → n ∷ o ∷ [] ≡ n ∷ p ∷ [] → n ∷ o ∷ [] ≡ m ∷ p ∷ []
silly1 pf₁ pf₂ rewrite (sym pf₁) = pf₂

silly2 : {n m o p : ℕ} → n ≡ m →
         ({q r : ℕ} → q ≡ r → q ∷ o ∷ [] ≡ r ∷ p ∷ []) →
         n ∷ o ∷ [] ≡ m ∷ p ∷ []
silly2 pf₁ pf₂ = pf₂ pf₁

silly2a : {n m : ℕ} → ⟨ n , n ⟩ ≡ ⟨ m , m ⟩ →
          ({q r : ℕ} → ⟨ q , q ⟩ ≡ ⟨ r , r ⟩ → q ∷ [] ≡ r ∷ []) →
          n ∷ [] ≡ m ∷ []
silly2a pf₁ pf₂ = pf₂ pf₁

silly-ex : ({n : ℕ} → even n ≡ true → odd (suc n) ≡ true) → even 3 ≡ true → odd 4 ≡ true
silly-ex thm hyp₃ rewrite hyp₃ = refl

silly3 : {n : ℕ} → true ≡ n =ℕ= 5 → (suc (suc n)) =ℕ= 7 ≡ true
silly3 pf = sym pf

reverse-exercise-1 : {ns ms : List ℕ} → ns ≡ reverse ms → ms ≡ reverse ns
reverse-exercise-1 {_} {ms} pf rewrite pf = sym (reverse-involutive ms)

trans-eq-example : {a b c d e f : ℕ} →
  a ∷ b ∷ [] ≡ c ∷ d ∷ [] → c ∷ d ∷ [] ≡ e ∷ f ∷ [] → a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example eq₁ eq₂ rewrite eq₁ | eq₂ = refl

trans-eq-example′ : {a b c d e f : ℕ} →
  a ∷ b ∷ [] ≡ c ∷ d ∷ [] → c ∷ d ∷ [] ≡ e ∷ f ∷ [] → a ∷ b ∷ [] ≡ e ∷ f ∷ []
trans-eq-example′ eq₁ eq₂ = trans eq₁ eq₂

trans-eq-exercise : {n m o p : ℕ} → m ≡ minus-two o → n + p ≡ m → n + p ≡ minus-two o
trans-eq-exercise eq₁ eq₂ = trans eq₂ eq₁

suc-injective : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-injective refl = refl

silly4 : {n m : ℕ} → n ∷ [] ≡ m ∷ [] → n ≡ m
silly4 refl = refl

silly5 : {n m o : ℕ} → n ∷ m ∷ [] ≡ o ∷ o ∷ [] → n ∷ [] ≡ m ∷ []
silly5 refl = refl

silly-ex1 : {A : Set} → {x y z : A} → {l j : List A} →
            x ∷ y ∷ l ≡ z ∷ j → y ∷ l ≡ x ∷ j → x ≡ y
silly-ex1 _ refl = refl

silly6 : {n : ℕ} → suc n ≡ zero → 2 + 2 ≡ 5
silly6 ()

silly7 : {n m : ℕ} → false ≡ true → n ∷ [] ≡ m ∷ []
silly7 ()

silly-ex2 : {A : Set} → {x y z : A} → {l j : List A} →
            x ∷ y ∷ l ≡ [] → y ∷ l ≡ z ∷ j → x ≡ z
silly-ex2 ()

length-snoc′ : {A : Set} → (v : A) → (as : List A) → (n : ℕ) →
               length as ≡ n → length (snoc as v) ≡ suc n
length-snoc′ _ []       zero    _  = refl
length-snoc′ _ []       (suc n) ()
length-snoc′ _ (a ∷ as) zero    ()
length-snoc′ v (a ∷ as) (suc n) pf = cong suc (length-snoc′ v as n (suc-injective pf))

zero-=ℕ=-left : {n : ℕ} → 0 =ℕ= n ≡ true → n ≡ 0
zero-=ℕ=-left {zero}  refl = refl
zero-=ℕ=-left {suc n} ()

zero-=ℕ=-right : {n : ℕ} → n =ℕ= 0 ≡ true → n ≡ 0
zero-=ℕ=-right {zero}  refl = refl
zero-=ℕ=-right {suc n} ()

-- This theorem is actually superfluous in Agda because of the way terms in types are normalized
-- (i.e., it's the identity)
suc-injective-bool : {n m : ℕ} → {b : Bool} → (suc n) =ℕ= (suc m) ≡ b → n =ℕ= m ≡ b
suc-injective-bool pf = pf

silly3′ : {n : ℕ} → (n =ℕ= 5 ≡ true → (suc (suc n)) =ℕ= 7 ≡ true) →
          true ≡ n =ℕ= 5 → true ≡ (suc (suc n)) =ℕ= 7
silly3′ pf eq = sym (pf (sym eq))

n-+-n-injective : {n m : ℕ} → n + n ≡ m + m → n ≡ m
n-+-n-injective {zero}  {zero}  _  = refl
n-+-n-injective {zero}  {suc m} ()
n-+-n-injective {suc n} {zero}  ()
n-+-n-injective {suc n} {suc m} pf = cong suc (n-+-n-injective (reduce pf))
  where reduce : suc n + suc n ≡ suc m + suc m → n + n ≡ m + m
        reduce pf rewrite sym (n-+-suc-m (suc n) n)
                        | sym (n-+-suc-m (suc m) m) = suc-injective (suc-injective pf)

double-injective : {n m : ℕ} → double n ≡ double m → n ≡ m
double-injective {zero}  {zero}  _  = refl
double-injective {zero}  {suc m} ()
double-injective {suc n} {zero}  ()
double-injective {suc n} {suc m} pf =
  cong suc (double-injective (suc-injective (suc-injective pf)))

=ℕ=-true : {n m : ℕ} → n =ℕ= m ≡ true → n ≡ m
=ℕ=-true {zero}  {zero}  _  = refl
=ℕ=-true {zero}  {suc m} ()
=ℕ=-true {suc n} {zero}  ()
=ℕ=-true {suc n} {suc m} pf = cong suc (=ℕ=-true pf)

‼-after-last : {n : ℕ} → {A : Set} → {l : List A} →
               length l ≡ n → l ‼ n ≡ nothing
‼-after-last {zero}  {_} {[]}       _  = refl
‼-after-last {zero}  {_} {(a ∷ as)} ()
‼-after-last {suc n} {_} {[]}       ()
‼-after-last {suc n} {A} {(a ∷ as)} pf = ‼-after-last (suc-injective pf)

length-snoc′′ : {n : ℕ} → {A : Set} → (v : A) → {l : List A} →
                length l ≡ n → length (snoc l v) ≡ suc n
length-snoc′′ {zero}  {_} _ {[]}       _  = refl
length-snoc′′ {zero}  {_} _ {(a ∷ as)} ()
length-snoc′′ {suc n} {_} _ {[]}       ()
length-snoc′′ {suc n} {A} v {(a ∷ as)} pf = cong suc (length-snoc′′ v (suc-injective pf))

app-length-cons : {A : Set} → {as bs : List A} → {x : A} → {n : ℕ} →
                  length (as ++ (x ∷ bs)) ≡ n → suc (length (as ++ bs)) ≡ n
app-length-cons {_} {[]}     {_}  {_} {_}     pf = pf
app-length-cons {_} {a ∷ as} {_}  {_} {zero}  ()
app-length-cons {A} {a ∷ as} {bs} {x} {suc n} pf =
  cong suc (app-length-cons {A} {as} {bs} {x} {n} (suc-injective pf))

app-length-twice : {A : Set} → {n : ℕ} → {as : List A} →
                   length as ≡ n → length (as ++ as) ≡ n + n
app-length-twice {_} {zero}  {[]}     _  = refl
app-length-twice {_} {zero}  {a ∷ as} ()
app-length-twice {_} {suc n} {[]}     ()
app-length-twice {A} {suc n} {a ∷ as} pf
  rewrite sym (app-length-cons {A} {as} {as} {a} {length (as ++ a ∷ as)} refl)
        | sym (n-+-suc-m (suc n) n)
  = cong suc (cong suc (app-length-twice (suc-injective pf)))

infix 0 if_then_else_
if_then_else_ : {A : Set} → Bool → A → A → A
if true  then cons else _   = cons
if false then _    else alt = alt

sillyfun : ℕ → Bool
-- NB. Definition by three equations matching on the argument is -not- identical to the
-- definition in terms of =ℕ=; if we used equations, the theorem would be a simple refl.
sillyfun n = if n =ℕ= 3 then false else if n =ℕ= 5 then false else false

sillyfun-false : ∀ n → sillyfun n ≡ false
sillyfun-false n with n =ℕ= 3 | n =ℕ= 5
... | true  | _     = refl
... | false | true  = refl
... | false | false = refl

override-shadow : {A : Set} → (x₁ x₂ : A) → (k₁ k₂ : ℕ) → (f : ℕ → A) →
                  (override (override f k₁ x₂) k₁ x₁) k₂ ≡ (override f k₁ x₁) k₂
override-shadow {A} x₁ x₂ k₁ k₂ f with k₁ =ℕ= k₂ | inspect (_=ℕ=_ k₁) k₂
... | true  | _      = refl
... | false | [ pf ] rewrite override-≠ {A} {f k₂} {x₁} {k₂} {k₁} f refl pf
                           | override-≠ {A} {f k₂} {x₂} {k₂} {k₁} f refl pf = refl

unzip-one : {A B : Set} → (x : A) → (y : B) → (ps : List (A × B)) →
            unzip (⟨ x , y ⟩ ∷ ps) ≡ ⟨ x ∷ fst (unzip ps) , y ∷ snd (unzip ps) ⟩
unzip-one x y ps with unzip ps | inspect unzip ps
... | ⟨ xs , ys ⟩ | [ pf ] = refl

zip-unzip : {A B : Set} → (ps : List (A × B)) → (xs : List A) → (ys : List B) →
            unzip ps ≡ ⟨ xs , ys ⟩ → ps ≡ zip xs ys
zip-unzip ps _ _ pf rewrite sym (cong fst pf)
                          | sym (cong snd pf) = sym (zip-unzip′ ps)
  where zip-unzip′ : {A B : Set} → (ps : List (A × B)) →
                     zip (fst (unzip ps)) (snd (unzip ps)) ≡ ps
        zip-unzip′ [] = refl
        zip-unzip′ (⟨ x , y ⟩ ∷ ps) rewrite cong fst (unzip-one x y ps)
                                          | cong snd (unzip-one x y ps)
                                          | zip-unzip′ ps = refl

sillyfun-1 : ℕ → Bool
sillyfun-1 n = if n =ℕ= 3 then true else if n =ℕ= 5 then true else false

boolean-if-inversion : (b : Bool) → (if b then true else false) ≡ b
boolean-if-inversion true  = refl
boolean-if-inversion false = refl

double-if-inversion : (b₁ b₂ : Bool) →
                      (if b₁ then true else if b₂ then true else false) ≡ b₁ ∨ b₂
double-if-inversion true  _     = refl
double-if-inversion false true  = refl
double-if-inversion false false = refl

is-3 : ℕ → Bool
is-3 n = if n =ℕ= 3 then true else false

is-3-correct : ∀ {n} → is-3 n ≡ true → n ≡ 3
is-3-correct {n} pf with n =ℕ= 3 | inspect (_=ℕ=_ n) 3
is-3-correct refl | true  | [ pf ] = =ℕ=-true pf
is-3-correct ()   | false | [ pf ]

sillyfun-1-odd : ∀ {n} → sillyfun-1 n ≡ true → odd n ≡ true
sillyfun-1-odd {n} pf with n =ℕ= 3 | inspect (_=ℕ=_ n) 3
                         | n =ℕ= 5 | inspect (_=ℕ=_ n) 5
-- I don't understand why =ℕ=-true has to have the n argument explicitly supplied here for
-- things to typecheck, since pf₃ has type n =ℕ= 3
sillyfun-1-odd {n} refl | true  | [ pf₃ ] | _     | [ pf₅ ] rewrite =ℕ=-true {n} pf₃ = refl
sillyfun-1-odd {n} refl | false | [ pf₃ ] | true  | [ pf₅ ] rewrite =ℕ=-true {n} pf₅ = refl
sillyfun-1-odd     ()   | false | [ pf₃ ] | false | [ pf₅ ]

bool-fn-applied-thrice : (f : Bool → Bool) → (b : Bool) → f (f (f b)) ≡ f b
bool-fn-applied-thrice f b with f true | inspect f true | f false | inspect f false
bool-fn-applied-thrice f true  | true  | [ pf₁ ] | _     | [ pf₀ ]
  rewrite pf₁ | pf₁ | pf₁ = refl
bool-fn-applied-thrice f false | _     | [ pf₁ ] | false | [ pf₀ ]
  rewrite pf₀ | pf₀ | pf₀ = refl
bool-fn-applied-thrice f true  | false | [ pf₁ ] | true  | [ pf₀ ]
  rewrite pf₁ | pf₀ | pf₁ = refl
bool-fn-applied-thrice f true  | false | [ pf₁ ] | false | [ pf₀ ]
  rewrite pf₁ | pf₀ | pf₀ = refl
bool-fn-applied-thrice f false | true  | [ pf₁ ] | true  | [ pf₀ ]
  rewrite pf₀ | pf₁ | pf₁ = refl
bool-fn-applied-thrice f false | false | [ pf₁ ] | true  | [ pf₀ ]
  rewrite pf₀ | pf₁ | pf₀ = refl

override-same : {A : Set} → (x₁ : A) → (k₁ k₂ : ℕ) → (f : ℕ → A) →
                f k₁ ≡ x₁ → (override f k₁ x₁) k₂ ≡ f k₂
override-same x₁ k₁ k₂ f pf with k₁ =ℕ= k₂ | inspect (_=ℕ=_ k₁) k₂
... | true  | [ pfk ] rewrite sym (=ℕ=-true {k₁} pfk) = sym pf
... | false | _       = refl

=ℕ=-sym : (n m : ℕ) → n =ℕ= m ≡ m =ℕ= n
=ℕ=-sym n m with n =ℕ= m | inspect (_=ℕ=_ n) m | m =ℕ= n | inspect (_=ℕ=_ m) n
... | true  | _ | true  | _ = refl
... | false | _ | false | _ = refl
-- These two cases are absurd but cannot be easily rejected using absurd patterns so we prove
-- the contradiction directly from hypotheses
... | true  | [ pf-nm ] | false | [ pf-mn ]
    rewrite =ℕ=-true {n} pf-nm | =ℕ=-refl m = pf-mn
... | false | [ pf-nm ] | true  | [ pf-mn ]
    rewrite =ℕ=-true {m} pf-mn | =ℕ=-refl n = sym pf-nm

=ℕ=-trans : {n m p : ℕ} → n =ℕ= m ≡ true → m =ℕ= p ≡ true → n =ℕ= p ≡ true
=ℕ=-trans {n} {m} {p} pf-nm pf-mp with =ℕ=-true {n} pf-nm | =ℕ=-true {m} pf-mp
... | re-nm | re-mp rewrite re-nm | sym re-mp = =ℕ=-refl m 

unzip-zip : {A B : Set} → (xs : List A) → (ys : List B) →
            length xs ≡ length ys → unzip (zip xs ys) ≡ ⟨ xs , ys ⟩
unzip-zip []       []       _  = refl
unzip-zip (x ∷ xs) []       ()
unzip-zip []       (y ∷ ys) ()
unzip-zip (x ∷ xs) (y ∷ ys) pf rewrite unzip-one x y (zip xs ys)
                                     | unzip-zip xs ys (suc-injective pf) = refl

override-≠′ : {A : Set} → (x₂ : A) → (k₁ k₂ : ℕ) → (f : ℕ → A) →
              k₂ =ℕ= k₁ ≡ false → override f k₂ x₂ k₁ ≡ f k₁
override-≠′ {A} x₂ k₁ k₂ f pf = override-≠ {A} {(f k₁)} {x₂} {k₁} {k₂} f refl pf

contra-elim : ∀ {ℓ} → {Whatever : Set ℓ} → true ≡ false → Whatever
contra-elim pf = ⊥-elim (contra-⊥ pf)
  where contra-⊥ : true ≡ false → ⊥
        contra-⊥ ()

override-permute : {A : Set} → (x₁ x₂ : A) → (k₁ k₂ k₃ : ℕ) → (f : ℕ → A) →
                   k₂ =ℕ= k₁ ≡ false →
                   (override (override f k₂ x₂) k₁ x₁) k₃ ≡ (override (override f k₁ x₁) k₂ x₂) k₃
override-permute x₁ x₂ k₁ k₂ k₃ f pf₂₁ with k₁ =ℕ= k₃ | inspect (_=ℕ=_ k₁) k₃
                                          | k₂ =ℕ= k₃ | inspect (_=ℕ=_ k₂) k₃
-- This first case is absurd (k₁ ≡ k₃ and k₂ ≡ k₃ but k₁ ≠ k₂)
... | true  | [ pf₁₃ ] | true  | [ pf₂₃ ]
  rewrite =ℕ=-true {k₁} pf₁₃ | =ℕ=-true {k₂} pf₂₃ | =ℕ=-refl k₃ = contra-elim pf₂₁
... | true  | [ pf₁₃ ] | false | _
  rewrite =ℕ=-true {k₁} pf₁₃ | override-= f k₃ x₁ = refl
... | false | _        | true  | [ pf₂₃ ]
  rewrite =ℕ=-true {k₂} pf₂₃ | override-= f k₃ x₂ = refl
... | false | [ pf₁₃ ] | false | [ pf₂₃ ] 
  rewrite override-≠′ (override f k₂ x₂ k₁) k₃ k₁ (override f k₂ x₂) pf₁₃
        | override-≠′ x₂ k₃ k₂ f pf₂₃
        | override-≠′ x₁ k₃ k₁ f pf₁₃ = refl

cons-head-≡ : {A : Set} → {x y : A} → {xs ys : List A} →
              x ∷ xs ≡ y ∷ ys → x ≡ y
cons-head-≡ {A} {x} {.x} {xs} {.xs} refl = refl

filter-exercise : {A : Set} → (p : A → Bool) → (x : A) → (ys pxs′ : List A) →
                  filter p ys ≡ x ∷ pxs′ → p x ≡ true
filter-exercise _ _ []        _    ()
filter-exercise p x (y ∷ ys′) pxs′ pf with p y | inspect p y
... | true  | [ pf-py ] rewrite sym (cons-head-≡ pf) = pf-py
... | false | _ = filter-exercise p x ys′ pxs′ pf

forall-bool : {A : Set} → (p : A → Bool) → (xs : List A) → Bool
forall-bool p [] = true
forall-bool p (x ∷ xs) with p x
... | true  = forall-bool p xs
... | false = false

exists-bool : {A : Set} → (p : A → Bool) → (xs : List A) → Bool
exists-bool p [] = false
exists-bool p (x ∷ xs) with p x
... | true  = true
... | false = exists-bool p xs

exists-bool′ : {A : Set} → (p : A → Bool) → (xs : List A) → Bool
exists-bool′ p xs = ¬ (forall-bool (λ x → ¬ (p x)) xs)

exists-equivalent : {A : Set} → (p : A → Bool) → (xs : List A) →
                    exists-bool′ p xs ≡ exists-bool p xs
exists-equivalent p [] = refl
exists-equivalent p (x ∷ xs) with p x
... | true  = refl
... | false rewrite exists-equivalent p xs = refl
