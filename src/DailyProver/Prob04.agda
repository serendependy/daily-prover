module DailyProver.Prob04 where

open import Level using (Level)

module ℓ where
  open import Level

open import Data.Empty
open import Data.Product
open import Data.Nat
  hiding (zero ; suc)
open import Data.Fin
open import Data.Fin.Properties

open import Function

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module _ {a b : Level} {A : Set a} {B : Set b} where

  Injective : (f : A → B) → Set _
  Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  Surjective : (f : A → B) → Set _
  Surjective f = ∀ y → ∃ λ x → f x ≡ y

module FiniteSets where

  Injection-to-Surjection : ∀ {n} (f : Fin n → Fin n) → Injective f → Surjective f
  Surjection-to-Injection : ∀ {n} (f : Fin n → Fin n) → Surjective f → Injective f

  module Lemmas where
    lfi : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n)) → Injective f → (Fin n → Fin n)
    lfi f inj i with f (suc i) | inspect f (suc i)
    ... | suc j   | _      = j
    ... | zero    | [ f-si≡z ]
      with f zero | inspect f zero
    ... | (suc k) | _    = k
    ... | zero    | [ f-z≡z ]
      with inj (trans f-si≡z (sym f-z≡z))
    ... | ()

    lfi-inj : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n))
             → (f-inj : Injective f) → Injective (lfi f f-inj)
    lfi-inj f f-inj {x} {y} lfi⟨x⟩≡lfi⟨y⟩
      with f (suc x) | inspect f (suc x) | f (suc y) | inspect f (suc y)

  -- f (suc x) ≡ suc f-sx , f (suc y) ≡ suc f⟨sy⟩ ⇒ ⊤
    ... | suc f⟨sx⟩ | [ eq-f⟨sx⟩ ] | suc f⟨sy⟩ | [ eq-f⟨sy⟩ ]
      = x≡y
      where
        f-x≡f-y : f (suc x) ≡ f (suc y)
        f-x≡f-y =
          begin                     f (suc x)
          ≡⟨ eq-f⟨sx⟩               ⟩ suc f⟨sx⟩
          ≡⟨ cong suc lfi⟨x⟩≡lfi⟨y⟩ ⟩ suc f⟨sy⟩
          ≡⟨ sym eq-f⟨sy⟩           ⟩ f (suc y)
          ∎

        x≡y = suc-injective (f-inj f-x≡f-y)

    -- f (suc x) ≡ suc f⟨sx⟩ , f (suc y) ≡ zero ⇒ ⊥
    ... | suc f⟨sx⟩ | [ eq-f⟨sx⟩ ] | zero     | [ eq-f⟨sy⟩ ]
      with f zero | inspect f zero
    --- case f-z is suc f-z
    ... | suc f-z | [ eq-f-z ]
      = ⊥-elim $ case sx≡z of (λ {()})
      where
        sx≡z : suc x ≡ zero
        sx≡z = f-inj $
          begin                     f (suc x)
          ≡⟨ eq-f⟨sx⟩               ⟩ suc f⟨sx⟩
          ≡⟨ cong suc lfi⟨x⟩≡lfi⟨y⟩ ⟩ suc f-z
          ≡⟨ sym eq-f-z             ⟩ f zero ∎
    --- case f-z is zero
    ... | zero     | [ eq-f-z ]
      = let sy≡z : suc y ≡ zero
            sy≡z = f-inj ∘ trans eq-f⟨sy⟩ ∘ sym $ eq-f-z
        in ⊥-elim $ case sy≡z of (λ {()})

    -- f (suc x) ≡ zero , f (suc y) ≡ suc f⟨sy⟩ ⇒ ⊥
    lfi-inj f f-inj {x} {y} lfi-x≡lfi-y | zero | [ eq-f⟨sx⟩ ] | suc f⟨sy⟩ | [ eq-f⟨sy⟩ ]
      with f zero | inspect f zero
    --- case f-z is suc f-z
    ... | (suc f-z) | [ eq-f-z ]
      = ⊥-elim $ case z≡sy of (λ {()})
      where
        z≡sy : zero ≡ suc y
        z≡sy = f-inj $
          begin                   f zero
          ≡⟨ eq-f-z               ⟩ suc f-z
          ≡⟨ cong suc lfi-x≡lfi-y ⟩ suc f⟨sy⟩
          ≡⟨ sym eq-f⟨sy⟩         ⟩ f (suc y) ∎
    --- case f-z is zero
    ... | zero | [ eq-f-z ]
      = let sx≡z : suc x ≡ zero
            sx≡z = f-inj ∘ trans eq-f⟨sx⟩ ∘ sym $ eq-f-z
        in case sx≡z of (λ {()})

    -- f (suc x) ≡ zero , f (suc y) ≡ zero ⇒ ⊤
    lfi-inj f f-inj {x} {y} lfi-x≡lfi-y | zero | [ eq-f⟨sx⟩ ] | zero | [ eq-f⟨sy⟩ ]
      = suc-injective ∘ f-inj $
        begin             f (suc x)
        ≡⟨ eq-f⟨sx⟩     ⟩ zero
        ≡⟨ sym eq-f⟨sy⟩ ⟩ f (suc y) ∎

    lfi-surj⇒f-surj : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n)) → (f-inj : Injective f)
              → Surjective (lfi f f-inj) → Surjective f
    -- n is zero, trivial (f : Fin 1 → Fin 1)
    lfi-surj⇒f-surj {ℕ.zero} f f-inj lfi-surj (suc ())
    lfi-surj⇒f-surj {ℕ.zero} f f-inj lfi-surj zero
      with f zero | inspect f zero
    ... | suc () | _
    ... | zero | [ eq-f⟨z⟩ ]
      = zero , eq-f⟨z⟩
    -- n is suc n
    --- y is suc y
    lfi-surj⇒f-surj {ℕ.suc n} f f-inj lfi-surj (suc y)
      with lfi-surj y
    ... | x , lfi⟨x⟩≡y
      with f (suc x) | inspect f (suc x)
    ---- f (suc x) is suc f⟨sx⟩
    ... | (suc f⟨sx⟩) | [ eq-f⟨sx⟩ ]
      = suc x , f⟨sx⟩≡sy
        where
          f⟨sx⟩≡sy =
            begin                  f (suc x)
            ≡⟨ eq-f⟨sx⟩          ⟩ suc f⟨sx⟩
            ≡⟨ cong suc lfi⟨x⟩≡y ⟩ suc y ∎

    ---- f (suc x) is zero
    ... | zero | [ eq-f⟨sx⟩ ]
      with f zero | inspect f zero
    ---- f zero is suc f⟨z⟩
    ... | (suc f⟨z⟩) | [ eq-f⟨z⟩ ]
      = zero , f⟨z⟩≡sy
      where
        f⟨z⟩≡sy =
          begin                  f zero
          ≡⟨ eq-f⟨z⟩           ⟩ suc f⟨z⟩
          ≡⟨ cong suc lfi⟨x⟩≡y ⟩ suc y ∎
    ---- f zero is zero ⇒ ⊥
    ... | zero | [ eq-f⟨z⟩ ]
      = case sx≡z of λ ()
      where
        sx≡z = f-inj (trans eq-f⟨sx⟩ (sym eq-f⟨z⟩))
    --- y is zero
    --- I hate to admit it but I wrote this before understanding it...
    lfi-surj⇒f-surj {ℕ.suc n} f f-inj lfi-surj zero
      with f zero | inspect f zero
    ... | zero | [ eq-f⟨z⟩ ]
      = zero , eq-f⟨z⟩
    ... | suc f⟨z⟩ | [ eq-f⟨z⟩ ]
      with lfi-surj f⟨z⟩
    ... | x₀ , lfi⟨x₀⟩≡f⟨z⟩
      with f (suc x₀) | inspect f (suc x₀)
    ... | zero | [ eq-f⟨sx₀⟩ ]
      = suc x₀ , eq-f⟨sx₀⟩
    ... | (suc f⟨sx₀⟩) | [ eq-f⟨sx₀⟩ ]
      = case sx₀≡z of (λ ())
        where
        f⟨sx₀⟩≡f⟨z⟩ = lfi⟨x₀⟩≡f⟨z⟩

        sx₀≡z : suc x₀ ≡ zero
        sx₀≡z = f-inj $
          begin                     f (suc x₀)
          ≡⟨ eq-f⟨sx₀⟩            ⟩ suc f⟨sx₀⟩
          ≡⟨ cong suc f⟨sx₀⟩≡f⟨z⟩ ⟩ suc f⟨z⟩
          ≡⟨ sym eq-f⟨z⟩          ⟩ f zero ∎

    f⁻¹ : ∀ {n} → (f : Fin n → Fin n) → (f-surj : Surjective f) → (Fin n → Fin n)
    f⁻¹ f f-surj x = proj₁ (f-surj x)

    f⁻¹-inj : ∀ {n} → (f : Fin n → Fin n) → (f-surj : Surjective f) → Injective (f⁻¹ f f-surj)
    f⁻¹-inj = {!!}

    iso-f-f⁻² : ∀ {n} → (f : Fin n → Fin n) → (f-surj : Surjective f)
                → ∀ x → f x ≡ f⁻¹ (f⁻¹ f f-surj) (Injection-to-Surjection _ (f⁻¹-inj f f-surj)) x
    iso-f-f⁻² = {!!}

    iso-f-h-inj : ∀ {n} → (f h : Fin n → Fin n) → (iso : ∀ i → f i ≡ h i) → (h-inj : Injective h) → Injective f
    iso-f-h-inj = {!!}


  Injection-to-Surjection {ℕ.zero} f f-inj ()
  Injection-to-Surjection {ℕ.suc n} f f-inj y
    with (Surjective $ Lemmas.lfi f f-inj)
         ∋ Injection-to-Surjection _ (Lemmas.lfi-inj f _)
  ... | lfi-surj
    = Lemmas.lfi-surj⇒f-surj f f-inj lfi-surj y

  Surjection-to-Injection f f-surj f⟨x⟩≡f⟨y⟩
    = let f⁻¹ = Lemmas.f⁻¹ f f-surj
          h   = Lemmas.f⁻¹ f⁻¹ (Injection-to-Surjection f⁻¹ (Lemmas.f⁻¹-inj f f-surj))
      in Lemmas.iso-f-h-inj f h (Lemmas.iso-f-f⁻² f f-surj) (Lemmas.f⁻¹-inj f⁻¹ ((Injection-to-Surjection f⁻¹ (Lemmas.f⁻¹-inj f f-surj)))) f⟨x⟩≡f⟨y⟩

