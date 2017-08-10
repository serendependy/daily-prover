module DailyProver.Prob01 where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Definitions where

  decr : (f : ℕ → ℕ) → Set
  decr f = ∀ n → f (suc n) ≤′ f n

  valley : (f : ℕ → ℕ) → (n x : ℕ) → Set
  valley f n x = (y : ℕ) → x ≤′ y → y ≤′ n + x → f y ≡ f x

open Definitions

module Lemmas where
  open import Data.Nat.Properties
  open import Relation.Binary
  open DecTotalOrder decTotalOrder

  ≤′-antisym : Antisymmetric _≡_ _≤′_
  ≤′-antisym x≤′y y≤′x
    with ≤′⇒≤ x≤′y | ≤′⇒≤ y≤′x
  ... | x≤y | y≤x = antisym x≤y y≤x

open Lemmas

module Proof (f : ℕ → ℕ) (decr-f : decr f) where
  open import Data.Nat.Properties using (n≤′m+n)

  {-# TERMINATING #-}
  decrValleysH : ∀ n (o : ℕ) → Σ[ x ∈ ℕ ] valley f n x
  decrValleysH zero o
    = o , (λ y y≤o o≤y → cong f (≤′-antisym o≤y y≤o))
  decrValleysH (suc n) o
    with decrValleysH n o
  ... | x , ind
    with decr-f (n + x)
  ... | f⟨sn+x⟩≤f⟨n+x⟩
    with f (suc (n + x)) | f (n + x)
    | inspect f (suc (n + x)) | inspect f (n + x)
  decrValleysH (suc n) o -- case f⟨sn+x⟩≤f⟨n+x⟩
    | x , ind
    | ≤′-refl
    | f⟨sn+x⟩ | .f⟨sn+x⟩
    | [ eq-f⟨sn+x⟩ ] | [ eq-f⟨n+x⟩ ]
    = x , h
    where
      h : ∀ y → x ≤′ y → y ≤′ suc (n + x) → f y ≡ f x
      h y x≤y (≤′-step y≤n+x)
        = ind y x≤y y≤n+x
      h .(suc (n + x)) x≤y ≤′-refl
        = begin                                  f (suc (n + x))
          ≡⟨ eq-f⟨sn+x⟩                        ⟩ f⟨sn+x⟩
          ≡⟨ sym eq-f⟨n+x⟩                     ⟩ f (n + x)
          ≡⟨ ind (n + x) (n≤′m+n n x) ≤′-refl  ⟩ f x ∎
  decrValleysH (suc n) o
    | x , ind
    | (≤′-step f⟨sn+x⟩≤f⟨n+x⟩)
    | f⟨sn+x⟩ | .(suc _) | _ | _
    = decrValleysH (suc n) (suc (n + x))

  decrValleys : ∀ n → Σ[ x ∈ ℕ ] valley f n x
  decrValleys n = decrValleysH n 0

open Proof

private
  module Tests where

  f : ℕ → ℕ
  f 0 = 1
  f 1 = 1
  f 2 = 1
  f (suc (suc (suc x))) = 0

  decr-f : decr f
  decr-f 0 = ≤′-refl
  decr-f 1 = ≤′-refl
  decr-f 2 = ≤′-step ≤′-refl
  decr-f (suc (suc (suc x))) = ≤′-refl

  f-valley₁ : Σ[ x ∈ ℕ ] valley f 2 x
  f-valley₁ = decrValleys f decr-f 2

  f-valley₁≡0 : proj₁ f-valley₁ ≡ 0
  f-valley₁≡0 = refl

  f-valley₂ : Σ[ x ∈ ℕ ] valley f 10 x
  f-valley₂ = decrValleys f decr-f 10

  f-valley₂≡3 : proj₁ f-valley₂ ≡ 3
  f-valley₂≡3 = refl
