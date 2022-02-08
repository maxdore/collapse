{-# OPTIONS --cubical --safe #-}
module LSet where

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
open import List

private
  variable
    ℓ ℓ₀ ℓ₁ : Level

open BinaryRelation

record lSet {ℓ ℓ'} : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  constructor lset
  field
    carrier : Type ℓ
    dec : Discrete carrier
    _⊏_ : carrier → carrier → Type ℓ'
    ⊏-prop : isPropValued _⊏_
    ⊏-irreflexive : isIrreflexive _⊏_
    ⊏-trans : isTrans _⊏_

  carrier-isSet : isSet carrier
  carrier-isSet = Discrete→isSet dec

  ⊏→≢ : {x y : carrier} → x ⊏ y → ¬Type (x ≡ y)
  ⊏→≢ {x} {y} p q = absurd (⊏-irreflexive x (subst (x ⊏_) (sym q) p))


  ordered : List carrier → Type ℓ'
  ordered [] = Unit*
  ordered (x ∷ []) = Unit*
  ordered (x ∷ y ∷ xs) = (x ⊏ y) × ordered (y ∷ xs)

  discreteOrdered : (xs : List carrier) → Discrete (ordered (xs))
  discreteOrdered [] tt* tt* = yes refl
  discreteOrdered (x ∷ []) tt* tt* = yes refl
  discreteOrdered (x ∷ y ∷ xs) = discreteΣ (λ p q → yes (⊏-prop x y p q)) λ _ → discreteOrdered (y ∷ xs)

  ordered-isProp : {xs : List carrier} → isProp (ordered (xs))
  ordered-isProp {[]} = isPropUnit*
  ordered-isProp {x ∷ []} = isPropUnit*
  ordered-isProp {x ∷ y ∷ xs} = isProp× (⊏-prop x y) ordered-isProp
