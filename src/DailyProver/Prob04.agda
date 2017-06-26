module DailyProver.Prob04 where

open import Level
  as Level hiding (zero ; suc)
open import Function
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product
open import Data.Empty
open import Data.Fin
open import Data.Fin.Properties
  using (suc-injective)
open import Data.Nat hiding (zero ; suc)

module _ where
  the : ∀ {a} (A : Set a) → A → A
  the = _∋_

module _ {a b : Level} {A : Set a} {B : Set b} where

  Injective : (f : A → B) → Set _
  Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  Surjective : (f : A → B) → Set _
  Surjective f = ∀ x → ∃ λ y → f x ≡ y

module Lemmas where

  lower-f : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n)) → Injective f → (Fin n → Fin n)
  lower-f f inj i with f (suc i) | inspect f (suc i)
  ... | suc j   | _      = j
  ... | zero    | [ f-si≡z ]
    with f zero | inspect f zero
  ... | (suc k) | _    = k
  ... | zero    | [ f-z≡z ]
    with inj (trans f-si≡z (sym f-z≡z))
  ... | ()

  lower-f-inj : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n))
                → (inj : Injective f) → Injective (lower-f f inj)
  lower-f-inj f inj-f {x} {y} lf-x≡lf-y
    with f (suc x) | inspect f (suc x) | f (suc y) | inspect f (suc y)
  ... | suc f-sx | [ eq-f-sx ] | suc f-sy | [ eq-f-sy ]
      = x≡y
    where
      f-x≡f-y : f (suc x) ≡ f (suc y)
      f-x≡f-y =
        begin                   f (suc x)
        ≡⟨ eq-f-sx ⟩            suc f-sx
        ≡⟨ cong suc lf-x≡lf-y ⟩ suc f-sy
        ≡⟨ sym eq-f-sy ⟩        f (suc y)
        ∎

      x≡y = suc-injective (inj-f f-x≡f-y)

  ... | suc f-sx | [ eq-f-sx ] | zero     | [ eq-f-sy ]
    with f zero | inspect f zero
  ... | suc f-z | [ eq-f-z ]
    = ⊥-elim $ case sx≡z of (λ {()})
    where
      sx≡z : suc x ≡ zero
      sx≡z = inj-f $
        begin                   f (suc x)
        ≡⟨ eq-f-sx            ⟩ suc f-sx
        ≡⟨ cong suc lf-x≡lf-y ⟩ suc f-z
        ≡⟨ sym eq-f-z         ⟩ f zero ∎

  ... | zero     | [ eq-f-z ]
    = let sy≡z = the (suc y ≡ zero) $ inj-f (trans eq-f-sy (sym eq-f-z))
      in ⊥-elim $ case sy≡z of (λ {()})

  lower-f-inj f inj-f {x} {y} lf-x≡lf-y | zero | cond1 | cond2 | cond3 = {!!}

Fin-inj-to-surj : ∀ {n} (f : Fin n → Fin n) → Injective f → Surjective f
Fin-inj-to-surj f f-inj x = {!!}

Fin-surj-to-inj : ∀ {n} (f : Fin n → Fin n) → Surjective f → Injective f
Fin-surj-to-inj f f-surj fx≡fy = {!!}

