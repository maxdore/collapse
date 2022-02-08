{-# OPTIONS --cubical --safe #-}
module Examples where

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



private
  variable
    ℓ ℓ₀ ℓ₁ : Level


module _ where
  open ℕSet

  _-to-0 : (n : ℕ) → neSet
  lemma : (n : ℕ) → fst (n -to-0) ≡ n

  zero -to-0 = singleton 0
  suc n -to-0 = let r = n -to-0 in suc n , toList r , (0 , (cong suc (lemma n))) , snd (snd r)

  lemma zero = refl
  lemma (suc n) = refl

  module ⊆Pos = IsPoset ⊆-IsPoset

  Δ : ℕ → SimplicialComplex
  Δ n = ℕSC (subsets (n -to-0)) closed where
    closed : subsets (n -to-0) closedUnder _⊆_
    closed X P Y Q = subsets-comp (⊆Pos.is-trans Y X (n -to-0) Q (subsets-corr P))

  module ΔFaces (n : ℕ) where
    open SimplicialComplex.SimplicialComplex (Δ n)
    open FacePoset
    open EntPath

    topcell : Initial (FacePoset (Δ n))
    fst topcell = n -to-0 , subsets-comp (⊆Pos.is-refl (n -to-0))
    snd topcell Y = (subsets-corr (snd Y)) , (λ y → tt*)

    Δn-isContr : isContr (𝓑 (Ent (Δ n)))
    Δn-isContr = subst isContr (sym (Ent≡FacePoset (Δ n))) (Initial-IsContr (FacePoset (Δ n)) topcell)

  ∂ : ℕ → SimplicialComplex
  ∂ n = ℕSC (ssubsets (n -to-0)) closed where
    closed : ssubsets (n -to-0) closedUnder _⊆_
    closed X P Y Q = ssubsets-comp (⊆⊂-trans Y X (n -to-0) Q (ssubsets-corr P))

  sucn-ordered : {(1+ n) : ℕ₊₁} → ordered (suc n ∷ fst (n -to-0) ∷ fst (snd (n -to-0)))
  sucn-ordered {1+ n} = ((0 , cong suc (lemma n)) , snd (snd (n -to-0)))

  Λ : ((1+ n) : ℕ₊₁) → SimplicialComplex
  Λ (1+ n) = ℕSC (Λfaces (suc n) (fst r) (fst (snd r)) sucn-ordered)
    (Λclosed sucn-ordered)
    where
    r = (n)-to-0

  module ΛFaces ((1+ n) : ℕ₊₁) where
    open SimplicialComplex.SimplicialComplex (Λ (1+ n))
    center : face
    center = singleton (suc n) , here refl

    adjoin : (X : face) → Σ[ X' ∈ face ] (X' ≽ X) × (X' ≽ center)
    fst (adjoin X) = withHelper (suc n isVertex? X)
      where
      withHelper : Dec (suc n ∈ getList X) → face
      withHelper (yes p) = X
      withHelper (no ¬p) = (insert (suc n) (fst X) (Λadjoin sucn-ordered (fst X) (snd X) ¬p)) , Λadjoin-corr sucn-ordered (fst X) (snd X) ¬p
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

    EntΛn-isContr : isContr (𝓑 (Ent (Λ (1+ n))))
    EntΛn-isContr = subst isContr (sym (Ent≡FacePoset (Λ (1+ n)))) FacePosetΛn-isContr
