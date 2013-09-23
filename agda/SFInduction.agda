module SFInduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Basics
open import Data.Nat renaming (_≤_ to leq-rel)

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

*-zero-+′ : ∀ n m → (0 + n) * m ≡ n * m
*-zero-+′ n m with iden-+-left {n}
... | refl = refl

+-rearrange : ∀ n m p q → (n + m) + (p + q) ≡ (m + n) + (p + q)
+-rearrange n m p q rewrite commut-+ n m = refl

+-swap : ∀ n m p → n + (m + p) ≡ m + (n + p)
+-swap n m p rewrite assoc-+ n m p | assoc-+ m n p | commut-+ n m = refl

iden-*-right : ∀ n → n * 1 ≡ n
iden-*-right zero = refl
iden-*-right (suc n) rewrite iden-*-right n = refl

*-suc-right : ∀ n m → n * (suc m) ≡ n + n * m
*-suc-right zero    _ = refl
*-suc-right (suc n) m rewrite +-swap n m (n * m) | *-suc-right n m = refl

commut-* : ∀ n m → n * m ≡ m * n
commut-* zero    m rewrite absorb-*-right m = refl
commut-* (suc n) m rewrite *-suc-right m n | commut-* n m = refl

even-suc-suc : ∀ n → even (suc (suc n)) ≡ even n
even-suc-suc n = refl

even-n-odd-suc-n : ∀ n → even n ≡ ¬ (even (suc n))
even-n-odd-suc-n zero    = refl
even-n-odd-suc-n (suc n) rewrite even-n-odd-suc-n n | ¬-involutive {even (suc n)} = refl

≤-refl : ∀ n → n ≤ n ≡ true
≤-refl zero    = refl
≤-refl (suc n) rewrite ≤-refl n = refl

zero-≠-suc : ∀ n → zero =ℕ= suc n ≡ false
zero-≠-suc _ = refl

∧-false-right : ∀ b → b ∧ false ≡ false
∧-false-right true  = refl
∧-false-right false = refl

≤-left-+-compat : ∀ n m p → n ≤ m ≡ true → (p + n) ≤ (p + m) ≡ true
≤-left-+-compat n m zero    pf = pf
≤-left-+-compat n m (suc p) pf rewrite ≤-left-+-compat n m p pf = refl

suc-≠-zero : ∀ n → suc n =ℕ= zero ≡ false
suc-≠-zero _ = refl

iden-*-left : ∀ n → 1 * n ≡ n
iden-*-left n rewrite iden-+-right n = refl

all-3-spec : ∀ b c → (b ∧ c) ∨ ((¬ b) ∨ (¬ c)) ≡ true
all-3-spec true  true  = refl
all-3-spec true  false = refl
all-3-spec false true  = refl
all-3-spec false false = refl

*-+-right-distrib : ∀ n m p → (n + m) * p ≡ n * p + m * p
*-+-right-distrib zero    m p = refl
*-+-right-distrib (suc n) m p rewrite *-+-right-distrib n m p | assoc-+ p (n * p) (m * p) = refl

assoc-* : ∀ n m p → n * (m * p) ≡ (n * m) * p
assoc-* zero    m p = refl
assoc-* (suc n) m p rewrite *-+-right-distrib m (n * m) p | assoc-* n m p = refl

=ℕ=-refl : ∀ n → n =ℕ= n ≡ true
=ℕ=-refl zero = refl
=ℕ=-refl (suc n) rewrite =ℕ=-refl n = refl

bin→nat-past-bin-suc : ∀ n → bin→nat (bin-suc n) ≡ suc (bin→nat n)
bin→nat-past-bin-suc zz     = refl
bin→nat-past-bin-suc (ee n) = refl
bin→nat-past-bin-suc (oo n) rewrite iden-+-right (bin→nat (bin-suc n))
                                  | iden-+-right (bin→nat n) 
                                  | bin→nat-past-bin-suc n
                                  | n-+-suc-m (bin→nat n) (bin→nat n) = refl

nat→bin-past-bin-suc : ∀ n → nat→bin (suc n) ≡ bin-suc (nat→bin n)
nat→bin-past-bin-suc _ = refl

nat→bin→nat-roundtrip : ∀ n → bin→nat (nat→bin n) ≡ n
nat→bin→nat-roundtrip zero = refl
nat→bin→nat-roundtrip (suc n) rewrite bin→nat-past-bin-suc (nat→bin n)
                                    | nat→bin→nat-roundtrip n = refl

normal-double : BinNat → BinNat
normal-double zz     = zz
normal-double (ee n) = ee (ee n)
normal-double (oo n) = ee (oo n)

normal-double-correct : ∀ n → bin→nat (normal-double n) ≡ bin→nat n + bin→nat n
normal-double-correct zz     = refl
normal-double-correct (ee n) rewrite iden-*-left (bin→nat n)
                                   | iden-+-right (bin→nat n + bin→nat n) = refl
normal-double-correct (oo n) rewrite iden-*-left (bin→nat n)
                                   | iden-+-right (bin→nat n + bin→nat n) = refl

normalize-bin : BinNat → BinNat
normalize-bin zz     = zz
normalize-bin (ee n) = normal-double (normalize-bin n)
normalize-bin (oo n) = oo (normalize-bin n)

normalize-bin-correct : ∀ n → bin→nat (normalize-bin n) ≡ bin→nat n
normalize-bin-correct zz = refl
normalize-bin-correct (ee n) rewrite normal-double-correct (normalize-bin n)
                                   | normalize-bin-correct n
                                   | iden-+-right (bin→nat n) = refl
normalize-bin-correct (oo n) rewrite normalize-bin-correct n = refl

normal-double-bin-suc : ∀ n → normal-double (bin-suc n) ≡ bin-suc (bin-suc (normal-double n))
normal-double-bin-suc zz     = refl
normal-double-bin-suc (ee n) rewrite normal-double-bin-suc n = refl
normal-double-bin-suc (oo n) rewrite normal-double-bin-suc n = refl

nat→bin-normal-double : ∀ n → nat→bin (n + n) ≡ normal-double (nat→bin n)
nat→bin-normal-double zero    = refl
nat→bin-normal-double (suc n) rewrite sym (n-+-suc-m n n)
                                    | normal-double-bin-suc (nat→bin n)
                                    | nat→bin-normal-double n = refl

nat→bin-double-suc : ∀ n → nat→bin (suc n + suc n) ≡ ee (nat→bin (suc n))
nat→bin-double-suc zero    = refl
nat→bin-double-suc (suc n) rewrite suc-n-+-m n (suc n)
                                 | nat→bin-double-suc n = refl

bin→nat-double-lemma : ∀ n → bin-suc (nat→bin (n + n)) ≡ oo (nat→bin n)
bin→nat-double-lemma zero    = refl
bin→nat-double-lemma (suc n) rewrite nat→bin-double-suc n = refl

bin→nat→bin-normalized : ∀ n → nat→bin (bin→nat n) ≡ normalize-bin n
bin→nat→bin-normalized zz     = refl
bin→nat→bin-normalized (ee n) rewrite iden-+-right (bin→nat n)
                                    | nat→bin-normal-double (bin→nat n) 
                                    | bin→nat→bin-normalized n = refl
bin→nat→bin-normalized (oo n) rewrite iden-+-right (bin→nat n)
                                    | bin→nat-double-lemma (bin→nat n) 
                                    | bin→nat→bin-normalized n = refl

even-bin : BinNat → Bool
even-bin zz     = true
even-bin (ee _) = true 
even-bin (oo _) = false

even-bin-suc-suc : ∀ n → even-bin (bin-suc (bin-suc n)) ≡ even-bin n
even-bin-suc-suc zz     = refl
even-bin-suc-suc (ee _) = refl
even-bin-suc-suc (oo _) = refl

even-bin-correct-even : ∀ n → even-bin (nat→bin n) ≡ even n
even-bin-correct-even zero          = refl
even-bin-correct-even (suc zero)    = refl
even-bin-correct-even (suc (suc n)) rewrite even-bin-suc-suc (nat→bin n)
                                          | even-bin-correct-even n = refl
