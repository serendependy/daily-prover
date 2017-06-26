module DailyProver.Prob04 where

open import Level
  as Level hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product
open import Data.Fin
open import Data.Fin.Properties
  using (suc-injective)
open import Data.Nat hiding (zero ; suc)

module _ {a b : Level} {A : Set a} {B : Set b} where

  Injective : (f : A → B) → Set _
  Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  Surjective : (f : A → B) → Set _
  Surjective f = ∀ x → ∃ λ y → f x ≡ y

Fin-inj-to-surj : ∀ {n} (f : Fin n → Fin n) → Injective f → Surjective f
Fin-inj-to-surj f f-inj x = {!!}

Fin-surj-to-inj : ∀ {n} (f : Fin n → Fin n) → Surjective f → Injective f
Fin-surj-to-inj f f-surj fx≡fy = {!!}

