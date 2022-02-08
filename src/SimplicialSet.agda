{-# OPTIONS --cubical --safe #-}
module SimplicialSet where

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

private
  variable
    ℓ ℓ₀ ℓ₁ : Level

record ΔSet² {ℓ} : Type (ℓ-suc ℓ) where
  constructor simp
  field
    C⁰ : Type ℓ
    C¹ : C⁰ → C⁰ → Type ℓ
    C² : {x y z : C⁰} → C¹ x y → C¹ y z → C¹ x z → Type ℓ
  [C¹] : Type ℓ
  [C¹] = (Σ[ x ∈ C⁰ ] (Σ[ y ∈ C⁰ ] ( C¹ x y )))

  [C²] : Type ℓ
  [C²] = (Σ[ x ∈ ( C⁰ ) ] Σ[ y ∈ ( C⁰ ) ] Σ[ z ∈ ( C⁰ ) ]
               Σ[ f ∈ ( C¹ x y ) ] Σ[ g ∈ ( C¹ y z ) ] Σ[ h ∈ ( C¹ x z ) ]
                ( (C² f g h) ))

record ΔMap {ℓ} (X Y : ΔSet² {ℓ}) : Type ℓ where
  constructor smap

  module X = ΔSet² X
  module Y = ΔSet² Y

  field
    smap₀ : ( X.C⁰ ) → ( Y.C⁰ )
    smap₁ : {x y : ( X.C⁰ )} → ( X.C¹ x y ) → ( Y.C¹ (smap₀ x) (smap₀ y) )
    smap₂ : {x y z : ( X.C⁰ )} → {f : ( X.C¹ x y )} → {g : ( X.C¹ y z )} → {h : ( X.C¹ x z )}
      → ( X.C² f g h ) → ( Y.C² (smap₁ f) (smap₁ g) (smap₁ h) )

  [smap₁] : {x y : ( X.C⁰ )} → ( X.C¹ x y ) → ( Y.[C¹] )
  [smap₁] {x} {y} k = smap₀ x , smap₀ y , smap₁ k

  [smap₂] : {x y z : ( X.C⁰ )} → {f : ( X.C¹ x y )} → {g : ( X.C¹ y z )}
    → {h : ( X.C¹ x z )} → ( X.C² f g h ) → ( Y.[C²] )
  [smap₂] {x} {y} {z} {f} {g} {h} ϕ = smap₀ x , smap₀ y , smap₀ z ,
    smap₁ f , smap₁ g , smap₁ h , smap₂ ϕ
