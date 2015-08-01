module elem where

open import Data.Nat
open import Data.List using (List; _∷_; []; [_])
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Sum

infix 4 _∈_ _∉_

data _∈_ {A : Set} : (x : A) → List A → Set where
  car : ∀ {x xs} → x ∈ x ∷ xs
  cdr : ∀ {x y xs} → x ∈ xs → x ∈ y ∷ xs

data _∉_ {A : Set} : (x : A) → List A → Set where
  empty : ∀ {x} → x ∉ []
  add : ∀ {x y xs} → x ≢ y → x ∉ xs → x ∉ y ∷ xs

record Test : Set where
  test1 : 1 ∈ 1 ∷ []
  test1 = car
  test2 : 1 ∈ 0 ∷ 1 ∷ []
  test2 = cdr car
  test3 : 1 ∈ 1 ∷ 0 ∷ 1 ∷ []
  test3 = car
  test4 : 1 ∈ 0 ∷ 1 ∷ 2 ∷ []
  test4 = cdr car
  test5 : 1 ∈ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
  test5 = cdr (cdr (cdr (cdr car)))
  test6 : 1 ∈ [] → 2 ∈ []
  test6 ()
  test7 : 1 ∈ 2 ∷ 3 ∷ 4 ∷ [] → 1 ∈ 2 ∷ 3 ∷ []
  test7 (cdr (cdr (cdr ())))

  test10 : 1 ∉ []
  test10 = empty
  test11 : 1 ∉ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  test11 = add (λ ()) (add (λ ()) (add (λ ()) (add (λ ()) empty)))

  open import Relation.Nullary.Core
  open import Data.Empty

  property-1 : {x : ℕ} {xs : List ℕ} → x ∈ xs → ¬ (x ∉ xs)
  property-1 car (add x₁ ¬p) = ⊥-elim (x₁ refl)
  property-1 (cdr p) (add x₁ ¬p) with property-1 p ¬p
  ... | prf = prf

  property-2 : {x : ℕ} {xs : List ℕ} → x ∉ xs → ¬ (x ∈ xs)
  property-2 empty ()
  property-2 (add x p) car = ⊥-elim (x refl)
  property-2 (add x p) (cdr ¬p) with property-2 p ¬p
  ... | prf = prf

  contraposition : {p q : Set} → (p → q) → (¬ q → ¬ p)
  contraposition x = λ z z₁ → z (x z₁)

  Sn≡Sm→n≡m : (n m : ℕ) → suc n ≡ suc m → n ≡ m
  Sn≡Sm→n≡m x .x refl = refl
  n≡m→Sn≡Sm : (n m : ℕ) → n ≡ m → suc n ≡ suc m
  n≡m→Sn≡Sm x .x refl = refl
  n≢m→Sn≢Sm : (n m : ℕ) → ¬ n ≡ m → ¬ suc n ≡ suc m
  n≢m→Sn≢Sm n m neq = contraposition (Sn≡Sm→n≡m n m) neq

  help1 : {n m : ℕ} {xs : List ℕ} → n ≢ m → n ∈ xs ⊎ n ∉ xs → n ∈ m ∷ xs ⊎ n ∉ m ∷ xs
  help1 neq (inj₁ x) = inj₁ (cdr x)
  help1 neq (inj₂ y) = inj₂ (add neq y)

  help2 : {n m : ℕ} {xs : List ℕ} → n ≡ m → n ∈ xs ⊎ n ∉ xs → n ∈ m ∷ xs ⊎ n ∉ m ∷ xs
  help2 refl or = inj₁ car

  help3 : (n m : ℕ) → n ≡ m ⊎ n ≢ m
  help3 zero zero = inj₁ refl
  help3 zero (suc m) = inj₂ (λ ())
  help3 (suc n) zero = inj₂ (λ ())
  help3 (suc n) (suc m) with help3 n m
  help3 (suc n) (suc m) | inj₁ x = inj₁ (cong suc x)
  help3 (suc n) (suc m) | inj₂ y = inj₂ (n≢m→Sn≢Sm n m y)

  help4 : {n m : ℕ} {xs : List ℕ} → n ∈ xs ⊎ n ∉ xs → n ∈ m ∷ xs ⊎ n ∉ m ∷ xs
  help4 (inj₁ x) = inj₁ (cdr x)
  help4 {zero} {zero} (inj₂ y) = inj₁ car
  help4 {zero} {suc m} (inj₂ y) = inj₂ (add (λ ()) y)
  help4 {suc n} {zero} (inj₂ y) = inj₂ (add (λ ()) y)
  help4 {suc n} {suc m} (inj₂ y) with help3 n m
  help4 {suc n} {suc .n} (inj₂ y) | inj₁ refl = inj₁ car
  help4 {suc n} {suc m} (inj₂ y) | inj₂ y₁ = inj₂ (add (n≢m→Sn≢Sm n m y₁) y)

  property-3 : (x : ℕ) → (xs : List ℕ) → x ∈ xs ⊎ x ∉ xs
  property-3 zero [] = inj₂ empty
  property-3 zero (zero ∷ xs) = inj₁ car
  property-3 zero (suc x ∷ xs) with property-3 zero xs
  ... | prf = help1 (λ ()) prf
  property-3 (suc x) [] = inj₂ empty
  property-3 (suc x) (zero ∷ xs) with property-3 (suc x) xs
  ... | prf = help1 (λ ()) prf
  property-3 (suc x) (suc x₁ ∷ xs) with property-3 (suc x) xs
  ... | inj₁ x₂ = inj₁ (cdr x₂)
  ... | inj₂ x₂ with help3 x x₁
  property-3 (suc x) (suc .x ∷ xs) | inj₂ x₂ | inj₁ refl = inj₁ car
  ... | inj₂ x₃ = inj₂ (add (n≢m→Sn≢Sm x x₁ x₃) x₂)
