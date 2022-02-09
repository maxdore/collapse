{-# OPTIONS --cubical --safe #-}
module Examples.Subsets where

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

open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Sum hiding (map) renaming (rec to srec)
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Prelude
open import List
open import LSet
open import NeSet


private
  variable
    ℓ₀ ℓ₁ : Level


open BinaryRelation

module Subsets {ℓ₀ ℓ₁} (O : lSet {ℓ₀} {ℓ₁}) where
  open neSet O

  -- To make Agda's termination checker see that the functions are structurally
  -- recursive, we need to pull out the components of the Σ type.

  subsetsₛ : (x : carrier) → (xs : List carrier) → ordered (x ∷ xs) → List neSet

  subsetsₛ-corr : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y , ys , es) ∈ subsetsₛ x xs ds
    → (y , ys , es) ⊆ (x , xs , ds)

  x⊏subsetsₛ : (x : carrier) {x' : carrier} {xs : List carrier} → ((d , ds) : ordered (x ∷ x' ∷ xs))
    → ⊏List x (subsetsₛ x' xs ds)
  x⊏subsetsₛ x (d , ds) (y , ys , es) p with (split⊆ ds es (subsetsₛ-corr ds es p))
  ... | inl q = subst _ q d
  ... | inr q = ⊏-trans _ _ _ d q

  insertSubsetsₛ : (x : carrier) {x' : carrier} {xs : List carrier} → (ordered (x ∷ x' ∷ xs)) → List neSet
  insertSubsetsₛ x {x'} {xs} (d , ds) = insertList x (subsetsₛ x' xs ds) (x⊏subsetsₛ x (d , ds))

  subsetsₛ x [] ds = [ singleton x ]
  subsetsₛ x (x' ∷ xs) (d , ds) = [ singleton x ] ++ subsetsₛ x' xs ds ++ insertSubsetsₛ x (d , ds)

  subsetsₛ-corr {x} {[]} tt* {y} {ys} es P = subst (_⊆ (singleton x)) (sym (x∈[y]→x≡y neSet-isSet P)) (IsPoset.is-refl (⊆-IsPoset) _)

  subsetsₛ-corr {x} {x' ∷ xs} (d , ds) {y} {[]} es P with dec++ discreteneSet _ [ singleton x ] _ P
  ... | inl Q = λ z z∈[y] → here (x∈[y]→x≡y carrier-isSet z∈[y] ∙ cons-inj₁ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q)))
  ... | inr Q with dec++ discreteneSet _ (subsetsₛ x' xs ds) (insertSubsetsₛ x (d , ds)) Q
  ... |       inl R = λ y' p → there (subsetsₛ-corr ds es R y' p)
  ... |       inr R = subst (λ a → [ a ] ⊆L (x ∷ x' ∷ xs))
                        (sym (insertList-head (x⊏subsetsₛ x (d , ds)) es R))
                        λ x₁ x₂ → here (x∈[y]→x≡y carrier-isSet x₂)

  subsetsₛ-corr {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with dec++ discreteneSet _ [ singleton x ] _ P
  ... | inl Q = absurd (¬cons≡nil (cons-inj₂ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q))))
  ... | inr Q with dec++ discreteneSet _ (subsetsₛ x' xs ds) (insertSubsetsₛ x (d , ds)) Q
  ... |       inl R = λ z p → there (subsetsₛ-corr ds (e , es) R z p)
  ... |       inr R =  subst (λ a → (a ∷ y' ∷ ys) ⊆L (x ∷ x' ∷ xs))
                          (sym (insertList-head (x⊏subsetsₛ x (d , ds)) (e , es) R) )
                          (xs⊆Lys→xxs⊆Lxys _ _ x (subsetsₛ-corr ds es (insertList-tail (x⊏subsetsₛ x (d , ds)) (e , es) R)))


  subsetsₛ-comp : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y , ys , es) ⊆ (x , xs , ds)
    → (y , ys , es) ∈ subsetsₛ x xs ds
  subsetsₛ-comp {x} {[]} ds {y} {ys} es P = here (toneSet≡ _ _ (ys⊆[x] es P))
  subsetsₛ-comp {x} {x' ∷ xs} (d , ds) {y} {[]} tt* P with
    split⊆ (d , ds) _ P
  ... | inl p = here (ΣPathP ((sym p) , ΣPathP (refl , refl)))
  ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsetsₛ x' xs ds) _
            (there (subsetsₛ-comp ds tt* (⊏-step (d , ds) tt* P (⊏→≢ p))))
  subsetsₛ-comp {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with
    split⊆ (d , ds) (e , es) P
  ... | inl p = x∈xs→x∈ys++xs _ (insertList x (subsetsₛ x' xs ds) (x⊏subsetsₛ x (d , ds))) _
                  (subst (_∈ insertList x (subsetsₛ x' xs ds) (x⊏subsetsₛ x (d , ds))) (toneSet≡ _ _ (cong (_∷ y' ∷ ys) p)) lemma )
                  where
                  IH = subsetsₛ-comp ds es (⊆-skip (d , ds) (e , es) P p)
                  lemma = insertList-corr (x⊏subsetsₛ x (d , ds)) (y' , ys , es) (subst (_⊏ y') (sym p) e) IH
  ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsetsₛ x' xs ds) _
            (there (subsetsₛ-comp ds (e , es) (⊏-step (d , ds) (e , es) P (⊏→≢ p))))


  -- We now create wrappers to compute subsets for proper neSets

  subsets : neSet → List neSet
  subsets (x , xs , ds) = subsetsₛ x xs ds

  subsets-corr : {X Y : neSet} → Y ∈ subsets X → Y ⊆ X
  subsets-corr {x , xs , ds} {y , ys , es} P = subsetsₛ-corr ds es P

  subsets-comp : {X Y : neSet} → Y ⊆ X → Y ∈ subsets X
  subsets-comp {x , xs , ds} {y , ys , es} P = subsetsₛ-comp ds es P
