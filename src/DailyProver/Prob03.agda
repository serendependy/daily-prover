module DailyProver.Prob03 where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Algebra

module _ {a} {A : Set a} where

  -- finiteness
  Injective : (A → A) → Set _
  Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  Surjective : (A → A) → Set _
  Surjective f = ∀ y → ∃ λ x → f x ≡ y

  -- associativity
  Associative : (_∙_ : A → A → A) → Set _
  Associative _∙_ = ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z

  -- cancellation
  LeftCancellitive : (A → A → A) → Set _
  LeftCancellitive _∙_ = ∀ {x y z} → x ∙ y ≡ x ∙ z → y ≡ z

  RightCancellitive : (A → A → A) → Set _
  RightCancellitive _∙_ = ∀ {x y z} → y ∙ x ≡ z ∙ x → y ≡ z

Dedekind-Finite : ∀ {a} (A : Set a) → Set _
Dedekind-Finite A = ∀ (f : A → A) → Injective f → Surjective f

module Prob3 {a} (A : Set a) (x₀ : A) (_∙_ : A → A → A)
             (dk : Dedekind-Finite A)
             (assoc : Associative _∙_)
             (lc : LeftCancellitive _∙_) (rc : RightCancellitive _∙_)
  where

  open Relation.Binary.PropositionalEquality.≡-Reasoning

  ∙-left-inj : ∀ x → Injective (x ∙_)
  ∙-left-inj x = λ eq → lc eq

  ∙-right-inj : ∀ x → Injective (_∙ x)
  ∙-right-inj x = λ eq → rc eq

  ∙-left-surj : ∀ x → Surjective (x ∙_)
  ∙-left-surj x = dk (x ∙_) (∙-left-inj x)

  ∙-right-surj : ∀ x → Surjective (_∙ x)
  ∙-right-surj x = dk (_∙ x) (∙-right-inj x)

  ε : A
  ε = proj₁ (∙-left-surj x₀ x₀)

  ε-x₀-right-id : x₀ ∙ ε ≡ x₀
  ε-x₀-right-id = proj₂ (∙-left-surj x₀ x₀)

  ε-x₀-left-id : ε ∙ x₀ ≡ x₀
  ε-x₀-left-id = ∙-left-inj x₀ (begin
    x₀ ∙ (ε ∙ x₀)
      ≡⟨ assoc x₀ ε x₀ ⟩
    ((x₀ ∙ ε) ∙ x₀)
      ≡⟨ cong (_∙ x₀) ε-x₀-right-id ⟩
    (x₀ ∙ x₀) ∎)

  ε-left-id : ∀ x → ε ∙ x ≡ x
  ε-left-id x = ∙-left-inj x₀ (begin
    x₀ ∙ (ε ∙ x)
      ≡⟨ assoc x₀ ε x ⟩
    ((x₀ ∙ ε) ∙ x)
      ≡⟨ cong (_∙ x) ε-x₀-right-id ⟩
    (x₀ ∙ x) ∎)

  ε-right-id : ∀ x → x ∙ ε ≡ x
  ε-right-id x = ∙-right-inj x₀ (begin
    (x ∙ ε) ∙ x₀
      ≡⟨ sym (assoc x ε x₀) ⟩
    x ∙ (ε ∙ x₀)
      ≡⟨ cong (x ∙_) ε-x₀-left-id ⟩
    (x ∙ x₀) ∎)

  _⁻¹ : A → A
  x ⁻¹ = proj₁ (∙-left-surj x ε)

  ⁻¹-right-inv : ∀ x → x ∙ (x ⁻¹) ≡ ε
  ⁻¹-right-inv x = proj₂ (∙-left-surj x ε)

  ⁻¹-left-inv : ∀ x → (x ⁻¹) ∙ x ≡ ε
  ⁻¹-left-inv x = ∙-left-inj x (begin
    x ∙ ((x ⁻¹) ∙ x)
      ≡⟨ assoc x (x ⁻¹) x ⟩
    (x ∙ (x ⁻¹)) ∙ x
      ≡⟨ cong (_∙ x) (⁻¹-right-inv x) ⟩
    ε ∙ x
      ≡⟨ ε-left-id x ⟩
    x
      ≡⟨ sym (ε-right-id x) ⟩
    x ∙ ε ∎)

