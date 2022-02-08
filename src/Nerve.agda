{-# OPTIONS --cubical --safe #-}
module Nerve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function hiding (_∘_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Sum hiding (map) renaming (rec to srec)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.NatPlusOne
open import Cubical.Data.List

open import Prelude
open import SimplicialSet
open import PCategory


private
  variable
    ℓ ℓ₀ ℓ₁ : Level

Nerve : ∀{ℓ} → (pCategory {ℓ}) → ΔSet² {ℓ}
Nerve C = simp ( ob ) (λ x y → ∣ hom x y ∣ₚ)
  λ {x} {y} {z} f g h → h ≤[ hom x z ] (g ∘ f)
  where open pCategory C


Nerve₁ : ∀{ℓ} {C D : pCategory {ℓ}} → pFunctor C D → ΔMap (Nerve C) (Nerve D)
Nerve₁ {ℓ} {C} {D} F = smap fmap₀ fmap₁ map₂
  where
  private
    module C = pCategory C
    module D = pCategory D
    module ΔC = ΔSet² (Nerve C)
    module ΔD = ΔSet² (Nerve D)
  open pFunctor F
  map₂ : {x y z : ΔC.C⁰} {f : ΔC.C¹ x y} {g : ΔC.C¹ y z} {h : ΔC.C¹ x z}
    → ( ΔC.C² f g h ) → ( ΔD.C² (fmap₁ f) (fmap₁ g) (fmap₁ h) )
  map₂ {x} {y} {z} {f} {g} {h} p =
    fmap₁ h ≤⟨ fmap₁-mono h (g C.∘ f) p ⟩
    fmap₁ (g C.∘ f) ≤⟨ comp-law f g ⟩
    fmap₁ g D.∘ fmap₁ f ◾
    where open PosetReasoning (D.hom (fmap₀ x) (fmap₀ z))
