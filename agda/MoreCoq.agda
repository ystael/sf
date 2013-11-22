module MoreCoq where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; inspect; [_])
open import Data.Nat renaming (_≤_ to leq-rel)
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
