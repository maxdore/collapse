{-# OPTIONS --cubical --safe #-}
module Examples.Collapse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Poset

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.NatPlusOne
open import Cubical.Data.List

open import Prelude
open import NeSet
open import List
open import SimplicialComplex
open import SimplicialSet
open import PCategory
open import EntrancePath
open import Nerve
open import Realization
open import ClassifyingSpace

open import Examples.HornFaces

private
  variable
    ℓ₀ ℓ₁ : Level


open neSet ℕlSet
open HornFaces ℕlSet
module ⊆Pos = IsPoset ⊆-IsPoset

-- The simplicial complex resulting from collapsing the standard simplex
Λ : ((1+ n) : ℕ₊₁) → SimplicialComplex
Λ (1+ n) = ℕSC (Λfaces (suc n) (fst r) (fst (snd r)) sucn-ordered)
  (Λclosed sucn-ordered)
  where
  r = (n)-to-0

module _ ((1+ n) : ℕ₊₁) where
  open SimplicialComplex.SimplicialComplex (Λ (1+ n))
  center : face
  center = singleton (suc n) , here refl

  -- Given a face X in Λ, we create another face which is a coface of both X and {n}
  adjoin : (X : face) → Σ[ X' ∈ face ] (X' ≽ X) × (X' ≽ center)
  fst (adjoin X) = withHelper (suc n isVertex? X)
    where
    withHelper : Dec (suc n ∈ getList X) → face
    withHelper (yes p) = X
    withHelper (no ¬p) = (insert (suc n) (fst X)
                             (Λadjoin sucn-ordered (fst X) (snd X) ¬p)) ,
                              Λadjoin-corr sucn-ordered (fst X) (snd X) ¬p
  snd (adjoin X) with (suc n) isVertex? X
  ...| yes p = IsPoset.is-refl (pstr ≽-Poset) X , λ x x₁ →
          subst (λ a → Any (PathP (λ i → ℕ) a) (fst (fst X) ∷ fst (snd (fst X))))
                (sym (x∈[y]→x≡y isSetℕ x₁))
                p
  ...| no ¬p = (λ _ q → there q) , λ m p → here (x∈[y]→x≡y carrier-isSet p)


  ≽-adjoinLeft : {X Y : face} → X ≽ Y → fst (adjoin X) ≽ Y
  ≽-adjoinLeft {X} {Y} = IsPoset.is-trans (pstr ≽-Poset) (fst X') X Y (fst (snd X'))
    where X' = adjoin X

  ≽-adjoin : {X Y : face} → X ≽ Y → fst (adjoin X) ≽ fst (adjoin Y)
  ≽-adjoin {X} {Y} P with (suc n) isVertex? X | (suc n) isVertex? Y
  ... | yes p | yes q = P
  ... | yes p | no ¬q = ∈⊆case isSetℕ P p
  ... | no ¬p | yes q = λ x r → there (P x r)
  ... | no ¬p | no ¬q = xs⊆Lys→xxs⊆Lxys _ _ _ P


  open FacePoset (Λ (1+ n))

  -- The proof that our contraction is continuous
  FacePosetΛn-isContr : isContr (𝓑 FacePoset)
  fst FacePosetΛn-isContr = vert center
  snd FacePosetΛn-isContr = Δ∣_∣elim.fun (λ a → isOfHLevelSuc 2 (trunc (vert center) a))
    con mor
    λ {x} {y} {z} {f} {g} {h} ϕ → isGroupoid→isGroupoid' trunc
    (mor f) (λ _ → con z)
    (mor h) (mor g)
    (λ _ _ → vert center) (triangle ϕ)

    where
    adjoinX≡X : (X : face) → vert (fst (adjoin X)) ≡ vert X
    adjoinX≡center : (X : face) → vert (fst (adjoin X)) ≡ vert center
    adjoinX≡X X = edge (fst (snd (adjoin X)))
    adjoinX≡center X = edge (snd (snd (adjoin X)))
    con : (X : face) → vert center ≡ vert X
    con X = sym (adjoinX≡center X) ∙ adjoinX≡X X
    mor : {X Y : face} (f : X ≽ Y) →
      Square (con X) (con Y) (λ _ → vert center) (edge f)
    mor {X} {Y} f i j = hcomp (λ k → λ {
        (i = i0) → compPath-filler (sym (adjoinX≡center X)) (adjoinX≡X X) k j
      ; (i = i1) → compPath-filler (sym (adjoinX≡center Y)) (adjoinX≡X Y) k j
      ; (j = i0) → vert center
      ; (j = i1) → doubleTriangle {ℓ-zero} {Nerve FacePoset} {fst (adjoin X)}
        {fst (adjoin Y)} {X} {Y} {≽-adjoin f} {fst (snd (adjoin X))} {fst (snd (adjoin Y))} {f}
        (≽-adjoinLeft {X} {Y} f) tt* tt* k i
      }) (triangle {_} {_} {fst (adjoin X)} {fst (adjoin Y)} {center}
                        {≽-adjoin f} {snd (snd (adjoin Y))} {snd (snd (adjoin X))} tt* (~ j) i)

  open EntPath

  -- Proving the base case of Nanda, Discrete Morse Theory and Localization, 2019
  EntΛn-isContr : isContr (𝓑 (Ent (Λ (1+ n))))
  EntΛn-isContr = subst isContr (sym (Ent≡FacePoset (Λ (1+ n)))) FacePosetΛn-isContr
