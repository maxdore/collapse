{-# OPTIONS --cubical --safe #-}
module Examples.HornFaces where

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
open import Examples.Ssubsets


private
  variable
    ℓ₀ ℓ₁ : Level



open BinaryRelation

module HornFaces {ℓ₀ ℓ₁} (O : lSet {ℓ₀} {ℓ₁}) where
  open neSet O
  open Ssubsets O

  module WithoutΣ where
    Λfaces : (x : carrier) (x' : carrier) (xs : List carrier) → ordered (x ∷ x' ∷ xs) → List neSet
    Λfaces x x' xs (d , ds) = [ singleton x ] ++ ssubsetsₛ x' xs ds ++ insertSsubsetsₛ x (d , ds)

    -- Showing that Λfaces is closed under taking subsets, i.e., that Y ∈ Λfaces X and Z ⊆ Y imply Z
    -- ∈ Λfaces X can be done by induction on X, Y, Z:
    Λclosed : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ Λfaces x x' xs (ds)
      → (Z : neSet) → Z ⊆ (y , ys , es) → Z ∈ Λfaces x x' xs (ds)
    Λclosed {x} {x'} {[]} (d , ds) {y} {ys} es P (z , zs , fs) Q =
      subst (_∈ Λfaces x x' [] (d , ds)) (sym Z≡Y) P
      where
      Y≡[x] : (y , ys , es) ≡ singleton x
      Y≡[x] = x∈[y]→x≡y neSet-isSet P
      ys≡[] : ys ≡ []
      ys≡[] = fst (PathPΣ (snd (PathPΣ Y≡[x])))
      zzs⊆[y] : (z , zs , fs) ⊆ (y , [] , tt*)
      zzs⊆[y] = subst (λ a → (z ∷ zs) ⊆L (y ∷ a)) ys≡[] Q
      zzs≡[y] : z ∷ zs ≡ y ∷ []
      zzs≡[y] = ys⊆[x] fs zzs⊆[y]
      Z≡Y : (z , zs , fs) ≡ (y , ys , es)
      Z≡Y = toneSet≡ _ _ (Listη (cons-inj₁ zzs≡[y]) (cons-inj₂ zzs≡[y] ∙ sym ys≡[]))
    Λclosed {x} {x'} {x'' ∷ xs} (d , ds) {y} {[]} es P Z Q =
      subst (_∈ Λfaces x x' (x'' ∷ xs) (d , ds))
            (sym (toneSet≡ _ _ (ys⊆[x] (snd (snd Z)) Q)))
            P
    Λclosed {x} {x'} {x'' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P (z , [] , fs) Q
      with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl R = absurd (¬cons≡nil (fst (PathPΣ (snd (PathPΣ (x∈[y]→x≡y neSet-isSet R))))))
    ... | inr R with dec++ discreteneSet _ (ssubsetsₛ x' (x'' ∷ xs) ds) (insertSsubsetsₛ x (d , ds)) R
    ... | inl S = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , [] , tt*) _ _
                          (ssubsetsₛ-comp ds tt*
                            (⊆⊂-trans (z , [] , tt*) (y , y' ∷ ys , e , es) (x' , x'' ∷ xs , ds)
                            Q
                            (ssubsetsₛ-corr ds (e , es) S))))
    ... | inr S with split⊆ (e , es) fs Q
    ... | inl p = here (toneSet≡ _ _ (Listη (sym p ∙ insertList-head (x⊏ssubsetsₛ x (d , ds)) (e , es) S) refl))
    ... | inr p = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , [] , tt*) _ _
                          (ssubsetsₛ-comp ds tt*
                            (⊆⊂-trans (z , [] , tt*) (y' , ys , es) (x' , x'' ∷ xs , ds)
                              (⊏-step (e , es) tt* Q (⊏→≢ p))
                              (ssubsetsₛ-corr ds es ((insertList-tail (x⊏ssubsetsₛ x (d , ds)) (e , es) S))))))
    Λclosed {x} {x'} {x'' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P (z , z' ∷ zs , fs) Q
      with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl R = absurd (¬cons≡nil (fst (PathPΣ (snd (PathPΣ (x∈[y]→x≡y neSet-isSet R))))))
    ... | inr R with dec++ discreteneSet _ (ssubsetsₛ x' (x'' ∷ xs) ds) (insertSsubsetsₛ x (d , ds)) R
    ... | inl S = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , z' ∷ zs , fs) _ _
                        (ssubsetsₛ-comp ds fs
                          (⊆⊂-trans (z , z' ∷ zs , fs) (y , y' ∷ ys , e , es) (x' , x'' ∷ xs , ds) Q
                          (ssubsetsₛ-corr ds (e , es) S))))
    ... | inr S with split⊆ (e , es) fs Q
    ... | inl p = there (x∈xs→x∈ys++xs _ _ (ssubsetsₛ x' (x'' ∷ xs) ds) goalCoerced)
      where
      y'ys∈ssubsets : (y' , ys , es) ∈ ssubsetsₛ x' (x'' ∷ xs) ds
      y'ys∈ssubsets = insertList-tail (x⊏ssubsetsₛ x (d , ds)) (e , es) S
      y'ys⊂x'x''xs : (y' , ys , es) ⊂ (x' , x'' ∷ xs , ds)
      y'ys⊂x'x''xs = ssubsetsₛ-corr ds (es) y'ys∈ssubsets
      y≡x = (insertList-head (x⊏ssubsetsₛ x (d , ds)) (e , es) S)
      z'zs⊆y'ys :  (z' , zs , snd fs) ⊆ (y' , ys , es)
      z'zs⊆y'ys = ⊆-skip (e , es) fs Q p
      z'zs⊂x'x''xs : (z' , zs , snd fs) ⊂ (x' , x'' ∷ xs , ds)
      z'zs⊂x'x''xs = ⊆⊂-trans (z' , zs , snd fs) (y' , ys , es) (x' , x'' ∷ xs , ds) z'zs⊆y'ys y'ys⊂x'x''xs
      goal = insertList-corr (x⊏ssubsetsₛ x (d , ds))
                               (z' , zs , snd fs)
                               (subst (_⊏ z') (sym p ∙ y≡x) (fst fs))
                               (ssubsetsₛ-comp (ds) (snd fs) z'zs⊂x'x''xs)
      goalCoerced = subst (_∈ insertList x (ssubsetsₛ x' (x'' ∷ xs) ds) (x⊏ssubsetsₛ x (d , ds)))
                   (ΣPathP ((sym y≡x ∙ p) , (ΣPathP (refl , toPathP (ordered-isProp _ _)))))
                   goal
    ... | inr p = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , z' ∷ zs , fs) _ _
                          (ssubsetsₛ-comp ds fs
                            (⊆⊂-trans (z , z' ∷ zs , fs) (y' , ys , es) (x' , x'' ∷ xs , ds)
                              (⊏-step (e , es) fs Q (⊏→≢ p))
                              (ssubsetsₛ-corr ds es ((insertList-tail (x⊏ssubsetsₛ x (d , ds)) (e , es) S))))))


    -- The following lemmas are necessary to show that we can insert x in the beginning of a face
    -- not containing x. For that purpose, we first locate a face not containing x in the list of
    -- computed faces as being a strict subset of x' ∷ xs

    Λadjoin-where : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ Λfaces x x' xs (ds)
      → ¬Type (x ∈ (y ∷ ys))
      → (y , ys , es) ∈ ssubsetsₛ x' xs (snd ds)
    Λadjoin-where {x} {x'} {xs} (d , ds) {y} {ys} es P ¬p with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl Q = absurd (¬p (here (sym (fst (PathPΣ (x∈[y]→x≡y neSet-isSet Q))))))
    ... | inr Q with dec++ discreteneSet _ (ssubsetsₛ x' xs ds) (insertSsubsetsₛ x (d , ds)) Q
    ... | inr R = absurd (¬p (here (sym (insertList-head (x⊏ssubsetsₛ x (d , ds)) es R))))
    ... | inl R = R

    -- We can use this lemma to show that x will be greater than all other elements in faces not
    -- containing x, and that adjoining x to them will also be computed by Λfaces.
    Λadjoin : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ Λfaces x x' xs (ds)
      → ¬Type (x ∈ (y ∷ ys)) → x ⊏ y
    Λadjoin {x} {x'} {xs} (d , ds) {y} {ys} es P ¬p
      with split⊆ ds es (fst (ssubsetsₛ-corr ds es (Λadjoin-where (d , ds) es P ¬p)))
    ... | inl p = subst (x ⊏_) p d
    ... | inr p = ⊏-trans x x' y d p

    Λadjoin-corr : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (P : (y , ys , es) ∈ Λfaces x x' xs ds)
      → (¬p : ¬Type (x ∈ (y ∷ ys)))
      → insert x (y , ys , es) (Λadjoin ds es P ¬p) ∈ Λfaces x x' xs ds
    Λadjoin-corr {x} {x'} {xs} (d , ds) {y} {ys} es P ¬p = there (x∈xs→x∈ys++xs _
      (insertSsubsetsₛ x (d , ds)) (ssubsetsₛ x' xs ds)
       (insertList-corr (x⊏ssubsetsₛ x (d , ds)) (y , ys , es) (Λadjoin (d , ds) es P ¬p) (Λadjoin-where (d , ds) es P ¬p)))



  Λfaces = WithoutΣ.Λfaces

  Λclosed : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
    → Λfaces x x' xs ds closedUnder _⊆_
  Λclosed {x} {x'} {xs} (d , ds) (y , ys , es) = WithoutΣ.Λclosed (d , ds) es

  Λadjoin : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
    → ((y , ys , es) : neSet)
    → (y , ys , es) ∈ Λfaces x x' xs (ds)
    → ¬Type (x ∈ (y ∷ ys)) → x ⊏ y
  Λadjoin ds (y , ys , es) = WithoutΣ.Λadjoin ds es

  Λadjoin-corr : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
    → ((y , ys , es) : neSet)
    → (P : (y , ys , es) ∈ Λfaces x x' xs (ds))
    → (¬p : ¬Type (x ∈ (y ∷ ys)))
    → insert x (y , ys , es) (Λadjoin ds (y , ys , es) P ¬p) ∈ Λfaces x x' xs ds
  Λadjoin-corr ds (y , ys , es) = WithoutΣ.Λadjoin-corr ds es
