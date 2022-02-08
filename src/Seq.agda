{-# OPTIONS --cubical --safe #-}
module Seq where

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


module Seq {ℓ ℓ'} (O : lSet {ℓ} {ℓ'}) where
  open neSet O public

  Seq : carrier → carrier → Type (ℓ-max ℓ ℓ')
  Seq X Y = Σ[ Ws ∈ List carrier ] ordered (X ∷ (Ws ++ [ Y ])) -- ()

  toneSet : {X Y : carrier} → Seq X Y → neSet
  toneSet {X} {Y} (Ws , ds) = X , Ws ++ [ Y ] , ds


  toSeq≡ : {X Y : carrier} {f g : Seq X Y} → toneSet f ≡ toneSet g
    → f ≡ g
  toSeq≡ {X} {Y} {Ws , ds} {Vs , es} p = ΣPathP (++inj₁ (fst (PathPΣ (snd (PathPΣ p)))) , toPathP (ordered-isProp _ _) )


  Seq++ : {X Y Z : carrier} {Ws Vs : List carrier} → ordered (X ∷ (Ws ++ [ Y ])) → ordered (Y ∷ (Vs ++ [ Z ]))
    → ordered (X ∷ ((Ws ++ Vs) ++ [ Z ]))
  Seq++ {X} {Y} {Z} {[]} {[]} (d , tt*) (e , tt*) = ⊏-trans _ _ _ d e , tt*
  Seq++ {X} {Y} {Z} {[]} {V ∷ Vs} (d , tt*) (e , es) = (⊏-trans _ _ _ d e) , es
  Seq++ {X} {Y} {Z} {W ∷ Ws} {Vs} (d , ds) es = d , Seq++ ds es



  ordered-tail : {W Y : carrier} {Ws : List carrier}
    → ordered (W ∷ Ws ++ [ Y ])
    → ordered (Ws ++ [ Y ])
  ordered-tail {W} {Y} {[]} _ = tt*
  ordered-tail {W} {Y} {V ∷ Ws} (d , ds) = ds

  SeqL6 : {X Y Z : carrier} {Ws Vs : List carrier}
    → ordered (Y ∷ Ws ++ [ Z ])
    → ordered (Y ∷ Vs ++ [ Z ])
    → (Y ∷ Ws ++ [ Z ]) ⊆L (Y ∷ Vs ++ [ Z ])
    → (X ∷ Ws ++ [ Z ]) ⊆L (X ∷ Vs ++ [ Z ])
  SeqL6 {X} {Y} {Z} {Ws} {Vs} ds es P = xs⊆Lys→xxs⊆Lxys _ _ _ (⊆-skip es ds P refl)



  lemma : {Ws Vs : List carrier} {Y : carrier}
    → ordered (Ws ++ [ Y ]) → ordered (Vs ++ [ Y ])
    → (Ws ++ [ Y ]) ⊆L (Vs ++ [ Y ])
    → Ws ⊆L Vs
  lemma {[]} {Vs} {Y} ds es P = []⊆Lxs Vs
  lemma {W ∷ Ws} {[]} {Y} ds es P = absurd (¬xs++[x]≡nil (cons-inj₂ (ys⊆[x] ds P)))
  lemma {W ∷ Ws} {V ∷ Vs} ds es P with split⊆ es ds P
  ... | inl p = λ x → ∈rec trunc (λ x₁ → here (x₁ ∙ sym p)) (λ x₁ → there (IH x x₁))
    where IH = lemma (ordered-tail ds) (ordered-tail es) (⊆-skip es ds P p)
  ... | inr p = λ x x₁ → there (IH x x₁)
    where IH = lemma {Ws = W ∷ Ws} ds (ordered-tail es) (⊏-step es ds P (⊏→≢ p))




  SeqL2 : {X Y Z : carrier} {Ws Vs : List carrier}
    → ordered (X ∷ Vs ++ [ Y ]) → ordered (X ∷ Ws ++ [ Y ])
    → (X ∷ Ws ++ Y ∷ []) ⊆L (X ∷ Vs ++ Y ∷ [])
    → (X ∷ Ws ++ Z ∷ []) ⊆L (X ∷ Vs ++ Z ∷ [])
  SeqL2 {X} {Y} {Z} {Ws} {Vs} es ds P  = xs⊆Lys→xxs⊆Lxys _ _ _ (helper (⊆-skip es ds P refl))
    where
    helper : (Ws ++ Y ∷ []) ⊆L (Vs ++ Y ∷ []) → (Ws ++ Z ∷ []) ⊆L (Vs ++ Z ∷ [])
    helper Q E R with dec++ dec _ Ws [ Z ] R
    ... | inl S = x∈xs→x∈xs++ys {Adec = dec} _ _ _
                  (lemma (ordered-tail ds) (ordered-tail es) Q E S)
    ... | inr S = x∈xs→x∈ys++xs _ _ _ (here (x∈[y]→x≡y carrier-isSet S))


  SeqL5 : {X Y Z : carrier} {Ws Vs Us : List carrier}
    → ordered (Y ∷ Us ++ [ Z ])
    → ordered (X ∷ Vs ++ [ Y ])
    → ordered (X ∷ Ws ++ [ Y ])
    → (X ∷ Ws ++ [ Y ]) ⊆L (X ∷ Vs ++ [ Y ])
    → (X ∷ (Ws ++ Us) ++ [ Z ]) ⊆L (X ∷ (Vs ++ Us) ++ [ Z ])
  SeqL5 {X} {Y} {Z} {Ws} {Vs} {Us} es ds fs P = xs⊆Lys→xxs⊆Lxys _ _ _ helper
    where
    actual = lemma (ordered-tail fs) (ordered-tail ds) (⊆-skip ds fs P refl)
    helper : ((Ws ++ Us) ++ [ Z ]) ⊆L ((Vs ++ Us) ++ [ Z ])
    helper E R with dec++ dec E (Ws ++ Us) [ Z ] R
    ... | inl S = x∈xs→x∈xs++ys {Adec = dec} _ (Vs ++ Us) [ Z ] (helper2 (dec++ dec _ _ _ S))
      where
      helper2 : (E ∈ Ws) ⊎ (E ∈ Us) → E ∈ (Vs ++ Us)
      helper2 (inl x) = x∈xs→x∈xs++ys {Adec = dec} _ _ _ (actual E x)
      helper2 (inr x) = x∈xs→x∈ys++xs _ _ _ x
    ... | inr S = x∈xs→x∈ys++xs _ _ _ S

  SeqL7 : {X Y Z : carrier} {Ws Vs Us : List carrier}
    → ordered (Y ∷ Vs ++ [ Z ]) → ordered (Y ∷ Us ++ [ Z ])
    → (Y ∷ Vs ++ [ Z ]) ⊆L (Y ∷ Us ++ [ Z ])
    → (X ∷ (Ws ++ Vs) ++ [ Z ]) ⊆L (X ∷ (Ws ++ Us) ++ [ Z ])
  SeqL7 {X} {Y} {Z} {Ws} {Vs} {Us} ds es P = xs⊆Lys→xxs⊆Lxys _ _ _ helper
    where
    actual = lemma (ordered-tail ds) (ordered-tail es) (⊆-skip es ds P refl)
    helper : ((Ws ++ Vs) ++ [ Z ]) ⊆L ((Ws ++ Us) ++ [ Z ])
    helper E R with dec++ dec _ (Ws ++ Vs) [ Z ] R
    ... | inl S = x∈xs→x∈xs++ys {Adec = dec} _ (Ws ++ Us) [ Z ] (helper2 (dec++ dec _ _ _ S))
      where
      helper2 : (E ∈ Ws) ⊎ (E ∈ Vs) → E ∈ (Ws ++ Us)
      helper2 (inl x) = x∈xs→x∈xs++ys {Adec = dec} _ _ _ x
      helper2 (inr x) = x∈xs→x∈ys++xs _ _ _ (actual E x)
    ... | inr S = x∈xs→x∈ys++xs _ _ _ S
