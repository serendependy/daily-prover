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

  -- f (suc x) ≡ suc f-sx , f (suc y) ≡ suc f-sy ⇒ ⊤
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

  -- f (suc x) ≡ suc f-sx , f (suc y) ≡ zero ⇒ ⊥
  ... | suc f-sx | [ eq-f-sx ] | zero     | [ eq-f-sy ]
    with f zero | inspect f zero
  --- case f-z is suc f-z
  ... | suc f-z | [ eq-f-z ]
    = ⊥-elim $ case sx≡z of (λ {()})
    where
      sx≡z : suc x ≡ zero
      sx≡z = inj-f $
        begin                   f (suc x)
        ≡⟨ eq-f-sx            ⟩ suc f-sx
        ≡⟨ cong suc lf-x≡lf-y ⟩ suc f-z
        ≡⟨ sym eq-f-z         ⟩ f zero ∎
  --- case f-z is zero
  ... | zero     | [ eq-f-z ]
    = let sy≡z : suc y ≡ zero
          sy≡z = inj-f ∘ trans eq-f-sy ∘ sym $ eq-f-z
      in ⊥-elim $ case sy≡z of (λ {()})

  -- f (suc x) ≡ zero , f (suc y) ≡ suc f-sy ⇒ ⊥
  lower-f-inj f inj-f {x} {y} lf-x≡lf-y | zero | [ eq-f-sx ] | suc f-sy | [ eq-f-sy ]
    with f zero | inspect f zero
  --- case f-z is suc f-z
  ... | (suc f-z) | [ eq-f-z ]
    = ⊥-elim $ case z≡sy of (λ {()})
    where
      z≡sy : zero ≡ suc y
      z≡sy = inj-f $
        begin                   f zero
        ≡⟨ eq-f-z             ⟩ suc f-z
        ≡⟨ cong suc lf-x≡lf-y ⟩ suc f-sy
        ≡⟨ sym eq-f-sy        ⟩ f (suc y) ∎
  --- case f-z is zero
  ... | zero | [ eq-f-z ]
    = let sx≡z : suc x ≡ zero
          sx≡z = inj-f ∘ trans eq-f-sx ∘ sym $ eq-f-z
      in case sx≡z of (λ {()})

  -- f (suc x) ≡ zero , f (suc y) ≡ zero ⇒ ⊤
  lower-f-inj f inj-f {x} {y} lf-x≡lf-y | zero | [ eq-f-sx ] | zero | [ eq-f-sy ]
    = suc-injective ∘ inj-f $
      begin            f (suc x)
      ≡⟨ eq-f-sx     ⟩ zero
      ≡⟨ sym eq-f-sy ⟩ f (suc y) ∎

  lower-f-surj : ∀ {n} (f : Fin (ℕ.suc n) → Fin (ℕ.suc n)) → (f-inj : Injective f)
                 → Surjective (lower-f f f-inj) → Surjective f
  -- f : Fin 1 → Fin 1
  lower-f-surj {ℕ.zero} f f-inj lf-surj (suc ())
  lower-f-surj {ℕ.zero} f f-inj lf-surj zero
    with f zero
  ... | suc ()
  ... | zero
    = zero , refl
  -- f : Fin (ss n) → Fin (ss n)
  --- x is suc x
  lower-f-surj {ℕ.suc n} f f-inj lf-surj (suc x) with lf-surj x
  ... | lf-surj⟨x⟩
    with f (suc x) | inspect f (suc x)
  ---- f (suc x) ≡ suc f⟨sx⟩
  ... | suc f⟨sx⟩ | [ eq-f⟨sx⟩ ]
    = (f (suc x)) , sym eq-f⟨sx⟩
  ---- f (suc x) ≡ zero
  ... | zero | [ eq-f⟨sx⟩ ]
    with f zero | inspect f zero
  ---- f zero ≡ suc f⟨z⟩
  ... | (suc f⟨z⟩) | [ eq-f⟨z⟩ ]
    = f (suc x) , (sym eq-f⟨sx⟩)
  ---- f zero ≡ zero ⇒ ⊥
  ... | zero | [ eq-f⟨z⟩ ] with f-inj (trans eq-f⟨sx⟩ (sym eq-f⟨z⟩))
  ... | ()
  --- x is zero
  lower-f-surj {ℕ.suc n} f f-inj lf-surj zero = {!!}

Fin-inj-to-surj : ∀ {n} (f : Fin n → Fin n) → Injective f → Surjective f
Fin-inj-to-surj {ℕ.zero} f f-inj ()
Fin-inj-to-surj {ℕ.suc n} f f-inj (suc x)
  with the (Surjective $ Lemmas.lower-f f f-inj) $
       Fin-inj-to-surj _ (Lemmas.lower-f-inj f _)
... | lf-surj
  = Lemmas.lower-f-surj f f-inj lf-surj (suc x)
Fin-inj-to-surj {ℕ.suc n} f f-inj zero = {!!}

Fin-surj-to-inj : ∀ {n} (f : Fin n → Fin n) → Surjective f → Injective f
Fin-surj-to-inj f f-surj fx≡fy = {!!}

