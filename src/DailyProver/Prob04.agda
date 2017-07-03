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
    lf : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n)) → Injective f → (Fin n → Fin n)
    lf f inj i with f (suc i) | inspect f (suc i)
    ... | suc j   | _      = j
    ... | zero    | [ f-si≡z ]
      with f zero | inspect f zero
    ... | (suc k) | _    = k
    ... | zero    | [ f-z≡z ]
      with inj (trans f-si≡z (sym f-z≡z))
    ... | ()

    lf-inj : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n))
             → (f-inj : Injective f) → Injective (lf f f-inj)
    lf-inj f f-inj {x} {y} lf⟨x⟩≡lf⟨y⟩
      with f (suc x) | inspect f (suc x) | f (suc y) | inspect f (suc y)

  -- f (suc x) ≡ suc f-sx , f (suc y) ≡ suc f⟨sy⟩ ⇒ ⊤
    ... | suc f⟨sx⟩ | [ eq-f⟨sx⟩ ] | suc f⟨sy⟩ | [ eq-f⟨sy⟩ ]
      = x≡y
      where
        f-x≡f-y : f (suc x) ≡ f (suc y)
        f-x≡f-y =
          begin                     f (suc x)
          ≡⟨ eq-f⟨sx⟩             ⟩ suc f⟨sx⟩
          ≡⟨ cong suc lf⟨x⟩≡lf⟨y⟩ ⟩ suc f⟨sy⟩
          ≡⟨ sym eq-f⟨sy⟩         ⟩ f (suc y)
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
          ≡⟨ eq-f⟨sx⟩             ⟩ suc f⟨sx⟩
          ≡⟨ cong suc lf⟨x⟩≡lf⟨y⟩ ⟩ suc f-z
          ≡⟨ sym eq-f-z           ⟩ f zero ∎
    --- case f-z is zero
    ... | zero     | [ eq-f-z ]
      = let sy≡z : suc y ≡ zero
            sy≡z = f-inj ∘ trans eq-f⟨sy⟩ ∘ sym $ eq-f-z
        in ⊥-elim $ case sy≡z of (λ {()})

    -- f (suc x) ≡ zero , f (suc y) ≡ suc f⟨sy⟩ ⇒ ⊥
    lf-inj f f-inj {x} {y} lf-x≡lf-y | zero | [ eq-f⟨sx⟩ ] | suc f⟨sy⟩ | [ eq-f⟨sy⟩ ]
      with f zero | inspect f zero
    --- case f-z is suc f-z
    ... | (suc f-z) | [ eq-f-z ]
      = ⊥-elim $ case z≡sy of (λ {()})
      where
        z≡sy : zero ≡ suc y
        z≡sy = f-inj $
          begin                   f zero
          ≡⟨ eq-f-z             ⟩ suc f-z
          ≡⟨ cong suc lf-x≡lf-y ⟩ suc f⟨sy⟩
          ≡⟨ sym eq-f⟨sy⟩       ⟩ f (suc y) ∎
    --- case f-z is zero
    ... | zero | [ eq-f-z ]
      = let sx≡z : suc x ≡ zero
            sx≡z = f-inj ∘ trans eq-f⟨sx⟩ ∘ sym $ eq-f-z
        in case sx≡z of (λ {()})

    -- f (suc x) ≡ zero , f (suc y) ≡ zero ⇒ ⊤
    lf-inj f f-inj {x} {y} lf-x≡lf-y | zero | [ eq-f⟨sx⟩ ] | zero | [ eq-f⟨sy⟩ ]
      = suc-injective ∘ f-inj $
        begin             f (suc x)
        ≡⟨ eq-f⟨sx⟩     ⟩ zero
        ≡⟨ sym eq-f⟨sy⟩ ⟩ f (suc y) ∎

    lf-surj-f : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n)) → (f-inj : Injective f)
              → Surjective (lf f f-inj) → Surjective f
    -- n is zero, trivial (f : Fin 1 → Fin 1)
    lf-surj-f {ℕ.zero} f f-inj lf-surj (suc ())
    lf-surj-f {ℕ.zero} f f-inj lf-surj zero
      with f zero | inspect f zero
    ... | suc () | _
    ... | zero | [ eq-f⟨z⟩ ]
      = zero , eq-f⟨z⟩
    -- n is suc n
    --- y is suc y
    lf-surj-f {ℕ.suc n} f f-inj lf-surj (suc y)
      with lf-surj y
    ... | x , lf⟨x⟩≡y
      with f (suc x) | inspect f (suc x)
    ---- f (suc x) is suc f⟨sx⟩
    ... | (suc f⟨sx⟩) | [ eq-f⟨sx⟩ ]
      = suc x , f⟨sx⟩≡sy
        where
          f⟨sx⟩≡sy =
            begin                 f (suc x)
            ≡⟨ eq-f⟨sx⟩         ⟩ suc f⟨sx⟩
            ≡⟨ cong suc lf⟨x⟩≡y ⟩ suc y ∎

    ---- f (suc x) is zero
    ... | zero | [ eq-f⟨sx⟩ ]
      with f zero | inspect f zero
    ... | (suc f⟨z⟩) | [ eq-f⟨z⟩ ] = {!!}
    ... | zero | eq-f⟨z⟩ = {!!}
    --- y is zero
    lf-surj-f {ℕ.suc n} f f-inj lf-surj zero = {!!}


  Injection-to-Surjection {ℕ.zero} f f-inj ()
  Injection-to-Surjection {ℕ.suc n} f f-inj y
    with (Surjective $ Lemmas.lf f f-inj)
         ∋ Injection-to-Surjection _ (Lemmas.lf-inj f _)
  ... | lf-surj
    = Lemmas.lf-surj-f f f-inj lf-surj y

  Surjection-to-Injection = {!!}

