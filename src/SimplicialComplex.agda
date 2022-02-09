{-# OPTIONS --cubical --safe #-}
module SimplicialComplex where

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
open import LSet
open import NeSet


private
  variable
    ℓ ℓ₀ ℓ₁ : Level


record SimplicialComplex : Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁)) where
  constructor simpcomp
  field
    lcarrier : lSet {ℓ₀} {ℓ₁}
  open neSet lcarrier
  field
    faces : List neSet
    faces-closed : (X : neSet) → X ∈ faces → (Y : neSet) → Y ⊆ X → Y ∈ faces
  face : Type (ℓ-max ℓ₀ ℓ₁)
  face = Σ[ X ∈ neSet ] X ∈ faces

  getList : face → List carrier
  getList X = toList (fst X)

  _isVertex?_ : (x : carrier) → (X : face) → Dec (x ∈ getList X)
  _isVertex?_ x X = _∈?_ {Adec = dec} x (getList X)

  face-isSet : isSet face
  face-isSet = isSetΣ (isSetΣ carrier-isSet (λ x → isSetΣ (isOfHLevelList 0
    carrier-isSet) (λ xs → isOfHLevelSuc 1 ordered-isProp))) (λ x → isProp→isSet trunc)

  decFace : Discrete face
  decFace = discreteΣ discreteneSet (λ a p q → yes (trunc p q))

  dim : face → ℕ
  dim X = length (getList X)

  _≽_ : Rel face face ℓ₀
  X ≽ Y = fst Y ⊆ fst X


  ≽-Poset : Poset _ _
  ≽-Poset = face , (posetstr _≽_ (isposet face-isSet
    (λ X Y → is-prop-valued (fst Y) (fst X))
    (λ X → is-refl (fst X))
    (λ X Y Z p q → is-trans (fst Z) (fst Y) (fst X) q p)
    λ X Y p q → ΣPathP ((is-antisym (fst X) (fst Y) q p) ,
      (toPathP ((trunc (transport (λ i → is-antisym (fst X) (fst Y) q p i ∈ faces) (snd X)) (snd Y)))))))
    where open IsPoset ⊆-IsPoset

  _≻_ : Rel face face _
  X ≻ Y = fst Y ⊂ fst X -- (X ≽ Y) × (dim Y < dim X)

  ≻-LSet : lSet
  ≻-LSet = lset face decFace _≻_
    (λ X Y → ⊂LSet.⊏-prop (fst Y) (fst X))
    (λ X → ⊂LSet.⊏-irreflexive (fst X))
    λ X Y Z p q → ⊂LSet.⊏-trans (fst Z) (fst Y) (fst X) q p
    where
    module ⊂LSet = lSet ⊂LSet

  ≽→≻ : (X Y : face) → X ≽ Y → ¬Type (X ≡  Y) → X ≻ Y
  ≽→≻ X Y P ¬Q = P , (⊆→⊂ (fst Y) (fst X) P (λ x → ¬Q (ΣPathP ((toneSet≡ _ _ x) , (toPathP (trunc _ _))))))

  ≽≻-trans : (X Y Z : face) → X ≽ Y → Y ≻ Z → X ≻ Z
  ≽≻-trans X Y Z P Q = ⊂⊆-trans (fst Z) (fst Y) (fst X) Q P

  ≻≽-trans : (X Y Z : face) → X ≻ Y → Y ≽ Z → X ≻ Z
  ≻≽-trans X Y Z P Q = ⊆⊂-trans (fst Z) (fst Y) (fst X) Q P

  ≽→≡⊎≻ : {X Y : face} → X ≽ Y → (X ≡ Y) ⊎ (X ≻ Y)
  ≽→≡⊎≻ {X} {Y} P with ⊆→≡⊎⊂ (fst Y) (fst X) P
  ... | inl p = inl (ΣPathP (sym p , toPathP (trunc _ _)))
  ... | inr q = inr q



module _ where
  open neSet ℕlSet

  ℕSC : (faces : List neSet) → faces closedUnder _⊆_
    → SimplicialComplex
  ℕSC = simpcomp ℕlSet
