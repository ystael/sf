module SFInduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Basics
open import Data.Nat

∧-true-elim-1 : ∀ {b c} → b ∧ c ≡ true → b ≡ true
∧-true-elim-1 {true}  {true}  refl = refl
∧-true-elim-1 {true}  {false} ()
∧-true-elim-1 {false} {_}     ()

∧-true-elim-2 : ∀ {b c} → b ∧ c ≡ true → c ≡ true
∧-true-elim-2 {true}  {true}  refl = refl
∧-true-elim-2 {true}  {false} ()
∧-true-elim-2 {false} {_}     ()

iden-+-right : ∀ n → n + 0 ≡ n
iden-+-right zero = refl
iden-+-right (suc n) rewrite iden-+-right n = refl

minus-diag : ∀ n → n ∸ n ≡ 0
minus-diag zero = refl
minus-diag (suc n) rewrite minus-diag n = refl

absorb-*-right : ∀ n → n * 0 ≡ 0
absorb-*-right zero = refl
absorb-*-right (suc n) rewrite absorb-*-right n = refl

n-+-suc-m : ∀ n m → suc (n + m) ≡ n + (suc m)
n-+-suc-m zero    m = refl
n-+-suc-m (suc n) m rewrite n-+-suc-m n m = refl

commut-+ : ∀ n m → n + m ≡ m + n
commut-+ zero    m rewrite iden-+-right m = refl
commut-+ (suc n) m rewrite commut-+ n m | n-+-suc-m m n = refl

assoc-+ : ∀ n m p → n + (m + p) ≡ (n + m) + p
assoc-+ zero    m p = refl
assoc-+ (suc n) m p rewrite assoc-+ n m p = refl

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

double-+ : ∀ n → double n ≡ n + n
double-+ zero = refl
double-+ (suc n) rewrite double-+ n | n-+-suc-m n n = refl
