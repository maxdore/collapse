{-# OPTIONS --cubical --safe #-}
module Examples.StandardSimplex where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Poset
open import Cubical.Data.Nat
open import Cubical.Data.List

open import Prelude
open import NeSet
open import List
open import SimplicialComplex
open import PCategory
open import EntrancePath
open import ClassifyingSpace

open import Examples.Subsets

open neSet ℕlSet
open Subsets ℕlSet
open FacePoset
open EntPath
module ⊆Pos = IsPoset ⊆-IsPoset

Δ : ℕ → SimplicialComplex
Δ n = ℕSC (subsets (n -to-0)) closed where
  closed : subsets (n -to-0) closedUnder _⊆_
  closed X P Y Q = subsets-comp (⊆Pos.is-trans Y X (n -to-0) Q (subsets-corr P))

module _ (n : ℕ) where
  open SimplicialComplex.SimplicialComplex (Δ n)

  topcell : Initial (FacePoset (Δ n))
  fst topcell = n -to-0 , subsets-comp (⊆Pos.is-refl (n -to-0))
  snd topcell Y = (subsets-corr (snd Y)) , (λ y → tt*)

  Δn-isContr : isContr (𝓑 (Ent (Δ n)))
  Δn-isContr = subst isContr (sym (Ent≡FacePoset (Δ n))) (Initial-IsContr (FacePoset (Δ n)) topcell)
