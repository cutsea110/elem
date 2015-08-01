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

  ∈→¬∉ : {x : ℕ} {xs : List ℕ} → x ∈ xs → ¬ (x ∉ xs)
  ∈→¬∉ car (add x₁ ¬p) = ⊥-elim (x₁ refl)
  ∈→¬∉ (cdr p) (add x₁ ¬p) with ∈→¬∉ p ¬p
  ... | prf = prf

  ∉→¬∈ : {x : ℕ} {xs : List ℕ} → x ∉ xs → ¬ (x ∈ xs)
  ∉→¬∈ empty ()
  ∉→¬∈ (add x p) car = ⊥-elim (x refl)
  ∉→¬∈ (add x p) (cdr ¬p) with ∉→¬∈ p ¬p
  ... | prf = prf

  contraposition : {p q : Set} → (p → q) → (¬ q → ¬ p)
  contraposition x = λ z z₁ → z (x z₁)

  Sn≡Sm→n≡m : (n m : ℕ) → suc n ≡ suc m → n ≡ m
  Sn≡Sm→n≡m x .x refl = refl

  n≡m→Sn≡Sm : (n m : ℕ) → n ≡ m → suc n ≡ suc m
  n≡m→Sn≡Sm x .x refl = refl

  n≢m→Sn≢Sm : (n m : ℕ) → n ≢ m → suc n ≢ suc m
  n≢m→Sn≢Sm n m neq = contraposition (Sn≡Sm→n≡m n m) neq

  n≡m⊎n≢m : (n m : ℕ) → n ≡ m ⊎ n ≢ m
  n≡m⊎n≢m zero zero = inj₁ refl
  n≡m⊎n≢m zero (suc m) = inj₂ (λ ())
  n≡m⊎n≢m (suc n) zero = inj₂ (λ ())
  n≡m⊎n≢m (suc n) (suc m) with n≡m⊎n≢m n m
  n≡m⊎n≢m (suc n) (suc m) | inj₁ x = inj₁ (cong suc x)
  n≡m⊎n≢m (suc n) (suc m) | inj₂ y = inj₂ (n≢m→Sn≢Sm n m y)

  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs : {n m : ℕ} {xs : List ℕ} → n ∈ xs ⊎ n ∉ xs → n ∈ m ∷ xs ⊎ n ∉ m ∷ xs
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs (inj₁ x) = inj₁ (cdr x)
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs {zero} {zero} (inj₂ y) = inj₁ car
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs {zero} {suc m} (inj₂ y) = inj₂ (add (λ ()) y)
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs {suc n} {zero} (inj₂ y) = inj₂ (add (λ ()) y)
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs {suc n} {suc m} (inj₂ y) with n≡m⊎n≢m n m
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs {suc n} {suc .n} (inj₂ y) | inj₁ refl = inj₁ car
  n∈xs⊎n∉xs→n∈m∷xs⊎n∉m∷xs {suc n} {suc m} (inj₂ y) | inj₂ y₁ = inj₂ (add (n≢m→Sn≢Sm n m y₁) y)

  ∈⊎∉ : (x : ℕ) → (xs : List ℕ) → x ∈ xs ⊎ x ∉ xs
  ∈⊎∉ zero [] = inj₂ empty
  ∈⊎∉ zero (zero ∷ xs) = inj₁ car
  ∈⊎∉ zero (suc x ∷ xs) with ∈⊎∉ zero xs
  ... | inj₁ x₁ = inj₁ (cdr x₁)
  ... | inj₂ y = inj₂ (add (λ ()) y)
  ∈⊎∉ (suc x) [] = inj₂ empty
  ∈⊎∉ (suc x) (zero ∷ xs) with ∈⊎∉ (suc x) xs
  ... | inj₁ x₁ = inj₁ (cdr x₁)
  ... | inj₂ y = inj₂ (add (λ ()) y)
  ∈⊎∉ (suc x) (suc x₁ ∷ xs) with ∈⊎∉ (suc x) xs
  ... | inj₁ x₂ = inj₁ (cdr x₂)
  ... | inj₂ x₂ with n≡m⊎n≢m x x₁
  ∈⊎∉ (suc x) (suc .x ∷ xs) | inj₂ x₂ | inj₁ refl = inj₁ car
  ... | inj₂ x₃ = inj₂ (add (n≢m→Sn≢Sm x x₁ x₃) x₂)
