{-# OPTIONS --cubical --safe #-}
module Prelude where

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

private
  variable
    ℓ ℓ₀ ℓ₁ : Level


¬Type_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬Type P = P → ⊥

⊤Prop : hProp ℓ
⊤Prop = Unit* , (λ _ _ _ → tt*)
⊥Prop : hProp ℓ
⊥Prop = (⊥* , isProp⊥*)

hProp→hSet : hProp ℓ → hSet ℓ
hProp→hSet (A , p) = A , isOfHLevelSuc 1 p

⊤Set : hSet ℓ
⊤Set = hProp→hSet ⊤Prop
⊥Set : hSet ℓ
⊥Set = hProp→hSet ⊥Prop

open BinaryRelation

isIrreflexive : {A : Type ℓ₀} → Rel A A ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isIrreflexive {A = X} R = (x : X) → ¬Type (R x x)

isTotal : {A : Type ℓ₀} → Rel A A ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isTotal {A = X} R = (x y : X) → ¬Type (x ≡ y) → (R x y) ⊎ (R y x)

hProp→Poset : hProp ℓ → Poset ℓ ℓ
hProp→Poset (A , isProp) = poset A (λ _ _ → Unit*) (isposet (isProp→isSet isProp)
  (λ _ _ _ _ _ → tt*) (λ _ → lift tt) (λ _ _ _ _ _ → lift tt) λ a b p q → isProp a b)

⊤Poset : Poset ℓ ℓ
⊤Poset = hProp→Poset ⊤Prop
⊥Poset : Poset ℓ ℓ
⊥Poset = hProp→Poset ⊥Prop


≡⇒≤ : ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → {x y : P} → x ≡ y → x ≤ y
≡⇒≤ (P , (posetstr _≤_ Pstr)) {x = x} p = subst (λ z → x ≤ z) p (is-refl x)
  where
  open IsPoset Pstr

∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ P ∣ₚ = fst P

isMonotonic : (P Q : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type (ℓ-max ℓ₀ ℓ₁)
isMonotonic (P , (posetstr _≤P_ Pstr)) (Q , (posetstr _≤Q_ Qstr)) f = ((x y : P) → x ≤P y → f x ≤Q f y)

≤P :  ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → P → P → Type ℓ₁
≤P (P , (posetstr _≤_ Pstr)) x y = x ≤ y

syntax ≤P P x y = x ≤[ P ] y

pstr : ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → IsPoset _≤_
pstr P = PosetStr.isPoset (snd P)

P-max : ((P , _) : Poset ℓ₀ ℓ₁) → P → Type (ℓ-max ℓ₀ ℓ₁)
P-max {_} {_} (P , posetstr _≤_ _) x = (∀ y → y ≤ x)

P-min : ((P , _) : Poset ℓ₀ ℓ₁) → P → Type (ℓ-max ℓ₀ ℓ₁)
P-min {_} {_} (P , posetstr _≤_ _) x = (∀ y → x ≤ y)
