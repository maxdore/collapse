{-# OPTIONS --cubical --safe #-}
module Realization where

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
open import Nerve


private
  variable
    ℓ ℓ₀ ℓ₁ : Level

module _ where
  open ΔSet²
  data ∣_∣ˢ (X : ΔSet² {ℓ}) : Type ℓ where
    vert : C⁰ X → ∣ X ∣ˢ
    edge : {x y : C⁰ X} → C¹ X x y → vert x ≡ vert y
    triangle : {x y z : C⁰ X} {f : C¹ X x y} {g : C¹ X y z} {h : C¹ X x z} (ϕ : C² X f g h)
      → Square (edge f) refl (edge h) (edge g)
    trunc : isGroupoid ∣ X ∣ˢ

module Δ∣_∣elim {X : ΔSet² {ℓ₀}} {P : ∣ X ∣ˢ → Type ℓ₁} (Pgpd : ∀ a → isGroupoid (P a))
              (vert* : (a : ( ΔSet².C⁰ X )) → P (vert a))
              (edge* : {a b : ( ΔSet².C⁰ X )} (f : ( ΔSet².C¹ X a b )) → PathP (λ i → P (edge f i)) (vert* a) (vert* b))
              (triangle* : {a b c : ( ΔSet².C⁰ X )} {f : ( ΔSet².C¹ X a b )} {g : ( ΔSet².C¹ X b c )}
                         {h : ( ΔSet².C¹ X a c )} (ϕ : ( ΔSet².C² X f g h ))
                         → SquareP (λ i j → P (triangle ϕ i j)) (edge* f) (λ j → vert* c) (edge* h) (edge* g))
                          where
  fun : (a : ∣ X ∣ˢ) → P a
  fun (vert x) = vert* x
  fun (edge f i) = edge* f i
  fun (triangle ϕ i j) = triangle* ϕ i j
  fun (trunc x y p q α β i j k) = isOfHLevel→isOfHLevelDep 3 Pgpd
                                   (fun x) (fun y)
                                   (cong fun p) (cong fun q)
                                   (cong (cong fun) α) (cong (cong fun) β)
                                   (trunc x y p q α β) i j k



Δ∣_∣₁ : {X Y : ΔSet² {ℓ₀}} → ΔMap X Y → ∣ X ∣ˢ → ∣ Y ∣ˢ
Δ∣_∣₁ {X} {Y} F = Δ∣_∣elim.fun
  (λ a → trunc)
  (λ x → vert (smap₀ x))
  (λ f i → edge (smap₁ f) i)
  (λ ϕ i j → triangle (smap₂ ϕ) i j)
  where open ΔMap F


module _ {X : ΔSet² {ℓ₀}} where
  open ΔSet² X
  ◤ : {x y z : C⁰} {f : C¹ x y} {g : C¹ y z}
     {h : C¹ x z} (ϕ : C² f g h)
      → Square refl (edge {ℓ₀} {X} g) (edge f) (edge h)
  ◤ ϕ = slideSquare (flipSquare (triangle ϕ))

  module _ {w x y z : C⁰} {f : C¹ w x} {g : C¹ w y} {f' : C¹ x z}
    {g' : C¹ y z} where

    doubleTriangle : (h : C¹ w z) → (C² f f' h) → (C² g g' h)
      → Square (edge f) (edge g') (edge g) (edge f')
    doubleTriangle h ϕ ψ i j = hcomp (λ k → λ {
            (i = i0) → edge f j
          ; (i = i1) → edge g' (j ∨ (~ k))
          ; (j = i0) → ◤ ψ i (~ k)
          ; (j = i1) → edge f' i
          }) (triangle ϕ i j)
