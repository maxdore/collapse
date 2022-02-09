{-# OPTIONS --cubical --safe #-}
module Examples.Boundary where

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

open import Examples.Ssubsets


open neSet ℕlSet
open Ssubsets ℕlSet
open FacePoset
open EntPath
module ⊆Pos = IsPoset ⊆-IsPoset

∂ : ℕ → SimplicialComplex
∂ n = ℕSC (ssubsets (n -to-0)) closed where
  closed : ssubsets (n -to-0) closedUnder _⊆_
  closed X P Y Q = ssubsets-comp (⊆⊂-trans Y X (n -to-0) Q (ssubsets-corr P))
