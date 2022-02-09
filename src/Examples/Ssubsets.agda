{-# OPTIONS --cubical --safe #-}
module Examples.Ssubsets where

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
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Sum hiding (map) renaming (rec to srec)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Prelude
open import List
open import LSet
open import NeSet
open import Examples.Subsets


private
  variable
    ℓ₀ ℓ₁ : Level



open BinaryRelation

module Ssubsets {ℓ₀ ℓ₁} (O : lSet {ℓ₀} {ℓ₁}) where
  open neSet O
  open Subsets O

  ssubsetsₛ : (x : carrier) → (xs : List carrier) → ordered (x ∷ xs) → List neSet

  ssubsetsₛ-corr : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y , ys , es) ∈ ssubsetsₛ x xs ds
    → (y , ys , es) ⊂ (x , xs , ds)

  x⊏ssubsetsₛ : (x : carrier) {x' : carrier} {xs : List carrier} → ((d , ds) : ordered (x ∷ x' ∷ xs))
    → ⊏List x (ssubsetsₛ x' xs ds)
  x⊏ssubsetsₛ x (d , ds) (y , ys , es) p with (split⊆ ds es (fst (ssubsetsₛ-corr ds es p)))
  ... | inl q = subst _ q d
  ... | inr q = ⊏-trans _ _ _ d q

  insertSsubsetsₛ : (x : carrier) {x' : carrier} {xs : List carrier} → (ordered (x ∷ x' ∷ xs)) → List neSet
  insertSsubsetsₛ x {x'} {xs} (d , ds) = insertList x (ssubsetsₛ x' xs ds) (x⊏ssubsetsₛ x (d , ds))

  ssubsetsₛ x [] ds = []
  ssubsetsₛ x (x' ∷ xs) (d , ds) = [ singleton x ] ++ subsetsₛ x' xs ds ++ insertSsubsetsₛ x (d , ds)

  ssubsetsₛ-corr {x} {[]} tt* {y} {ys} es P = absurd (¬x∈[] P)

  ssubsetsₛ-corr {x} {x' ∷ xs} (d , ds) {y} {[]} es P with dec++ discreteneSet _ [ singleton x ] _ P
  ... | inl Q = (λ z z∈[y] → here (x∈[y]→x≡y carrier-isSet z∈[y] ∙ cons-inj₁ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q)))) , arith (length xs)
  ... | inr Q with dec++ discreteneSet _ (subsetsₛ x' xs ds) (insertSsubsetsₛ x (d , ds)) Q
  ... |       inl R = (λ x₁ x₂ → there (sub x₁ x₂)) , arith (length xs)
    where sub = (subsetsₛ-corr ds tt* R)
  ... |       inr R = (subst (λ a → [ a ] ⊆L (x ∷ x' ∷ xs))
                        (sym (insertList-head (x⊏ssubsetsₛ x (d , ds)) es R))
                        λ x₁ x₂ → here (x∈[y]→x≡y carrier-isSet x₂)) , arith (length xs)

  ssubsetsₛ-corr {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with dec++ discreteneSet _ [ singleton x ] _ P
  ... | inl Q = absurd (¬cons≡nil (cons-inj₂ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q))))
  ... | inr Q with dec++ discreteneSet _ (subsetsₛ x' xs ds) (insertSsubsetsₛ x (d , ds)) Q
  ... |       inl R = (λ x₁ x₂ → there (sub x₁ x₂)) , suc-≤-suc (⊆→length (e , es) ds sub)
    where sub = (subsetsₛ-corr ds (e , es) R)
  ... |       inr R = mmh , (suc-≤-suc (snd IH))
    where
    IH = ssubsetsₛ-corr ds es (insertList-tail (x⊏ssubsetsₛ x (d , ds)) (e , es) R)
    mmh = subst (λ a → (a ∷ y' ∷ ys) ⊆L (x ∷ x' ∷ xs))
                          (sym (insertList-head (x⊏ssubsetsₛ x (d , ds)) (e , es) R) )
                          (xs⊆Lys→xxs⊆Lxys _ _ x (fst IH))



  ssubsetsₛ-comp : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y , ys , es) ⊂ (x , xs , ds)
    → (y , ys , es) ∈ ssubsetsₛ x xs ds
  ssubsetsₛ-comp {x} {[]} ds {y} {ys} es P = absurd (¬-<-zero (pred-≤-pred (snd P)))
  ssubsetsₛ-comp {x} {x' ∷ xs} (d , ds) {y} {[]} tt* P with
    split⊆ (d , ds) _ (fst P)
  ... | inl p = here (ΣPathP ((sym p) , ΣPathP (refl , refl)))
  ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsetsₛ x' xs ds) _ (there IH)
                where
                IH = subsetsₛ-comp ds tt* ((⊏-step (d , ds) tt* (fst P) (⊏→≢ p)))
  ssubsetsₛ-comp {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with
    split⊆ (d , ds) (e , es) (fst P)
  ... | inl p = x∈xs→x∈ys++xs _ (insertList x (ssubsetsₛ x' xs ds) (x⊏ssubsetsₛ x (d , ds))) _
                (subst (_∈ insertList x (ssubsetsₛ x' xs ds) (x⊏ssubsetsₛ x (d , ds))) (toneSet≡ _ _ (cong (_∷ y' ∷ ys) p)) lemma )
                  where
                  IH = ssubsetsₛ-comp ds es ((⊆-skip (d , ds) (e , es) (fst P) p) , (pred-≤-pred (snd P)))
                  lemma = insertList-corr (x⊏ssubsetsₛ x (d , ds)) (y' , ys , es) (subst (_⊏ y') (sym p) e) IH
  ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsetsₛ x' xs ds) _ (there (subsetsₛ-comp ds (e , es) (⊏-step (d , ds) (e , es) (fst P) (⊏→≢ p))))



  ssubsets : neSet → List neSet
  ssubsets (x , xs , ds) = ssubsetsₛ x xs ds

  ssubsets-corr : {X Y : neSet} → Y ∈ ssubsets X → Y ⊂ X
  ssubsets-corr {x , xs , ds} {y , ys , es} P = ssubsetsₛ-corr ds es P

  ssubsets-comp : {X Y : neSet} → Y ⊂ X → Y ∈ ssubsets X
  ssubsets-comp {x , xs , ds} {y , ys , es} P = ssubsetsₛ-comp ds es P
