{-# OPTIONS --cubical --safe #-}
module EntrancePath where

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
open import Seq
open import SimplicialComplex
open import PCategory

private
  variable
    ℓ ℓ₀ ℓ₁ : Level


module EntPath (K : SimplicialComplex {ℓ₀} {ℓ₀}) where
  open SimplicialComplex.SimplicialComplex K
  open Seq.Seq ≻-LSet

  entpath : face → face → Type ℓ₀
  entpath X Y = (X ≽ Y) ⊎ Seq X Y

  ≽→entpath : {X Y : face} → X ≽ Y → entpath X Y
  ≽→entpath {X} {Y} P = inl P

  entpath→≽ : {X Y : face} → entpath X Y → X ≽ Y
  entpath→≽ {X} {Y} (inl p) = p
  entpath→≽ {X} {Y} (inr (Ws , ds)) = fst (x⊏xs ds Y x∈xsx)

  entpath-isSet : {X Y : face} → isSet (entpath X Y)
  entpath-isSet {X} {Y} = isOfHLevel⊎ 0 (isProp→isSet (IsPoset.is-prop-valued (pstr ≽-Poset) X Y))
    (isSetΣ (isOfHLevelList 0 face-isSet) (λ Ws → isOfHLevelSuc 1 ordered-isProp))

  ordered++ : {Ws : List face} {X Y Z : face} → Y ≽ Z → ordered (X ∷ Ws ++ [ Y ])
    → ordered (X ∷ Ws ++ [ Z ])
  ordered++ {[]} {X} {Y} {Z} P f = ≻≽-trans X Y Z (fst f) P , tt*
  ordered++ {W ∷ Ws} {X} {Y} {Z} P (f , fs) = f , (ordered++ P fs)


  open BinaryRelation

  Ent : pCategory
  Ent = pcat face hom pid pcomp left-id right-id left-whisker right-whisker passoc
    where
    module _ {X Y : face} where
      open IsPoset

      order : Rel (entpath X Y) (entpath X Y) _
      order (inl p) (inl q) = Unit*
      order (inl p) (inr g) = Unit*
      order (inr f) (inl q) = ⊥*
      order (inr f) (inr g) = toneSet f ⊆ toneSet g

      order-prop : isPropValued order
      order-prop (inl p) (inl q) = isPropUnit*
      order-prop (inl p) (inr q) = isPropUnit*
      order-prop (inr p) (inr q) = is-prop-valued ⊆-IsPoset (toneSet p) (toneSet q)

      order-is-refl : isRefl order
      order-is-refl (inl p) = tt*
      order-is-refl (inr f) = is-refl ⊆-IsPoset (toneSet f)

      order-is-trans : isTrans order
      order-is-trans (inl x₂) (inl x₃) (inl x₄) x x₁ = tt*
      order-is-trans (inl x₂) (inl x₃) (inr x₄) x x₁ = tt*
      order-is-trans (inl x₂) (inr x₃) (inr x₄) x x₁ = tt*
      order-is-trans (inr f) (inr g) (inr h) = is-trans ⊆-IsPoset (toneSet f) (toneSet g) (toneSet h)

      order-is-antisym : isAntisym order
      order-is-antisym (inl p) (inl q) tt* tt* = cong inl (is-prop-valued (pstr ≽-Poset) X Y p q)
      order-is-antisym (inl p) (inr g) a ()
      order-is-antisym (inr f) (inl q) () b
      order-is-antisym (inr f) (inr g) a b = cong inr (toSeq≡ (is-antisym ⊆-IsPoset (toneSet f) (toneSet g) a b))


    hom : face → face → Poset ℓ₀ ℓ₀
    hom X Y = (entpath X Y) , (posetstr order (isposet entpath-isSet order-prop order-is-refl order-is-trans order-is-antisym))

    module _ where
      open IsPoset (pstr ≽-Poset)

      pid : {X : face} → entpath X X
      pid {X} = inl (is-refl X)

      pcomp : {X Y Z : face } → entpath X Y → entpath Y Z → entpath X Z
      pcomp {X} {Y} {Z} (inl p) (inl q) = inl (is-trans X Y Z p q)
      pcomp {X} {Y} {Z} (inl p) (inr ([] , Y≻Z , tt*)) = inr ([] , (≽≻-trans X Y Z p Y≻Z , tt*))
      pcomp {X} {Y} {Z} (inl p) (inr (V ∷ Vs , Y≻V , g)) = inr (V ∷ Vs , ≽≻-trans X Y V p Y≻V , g)
      pcomp {X} {Y} {Z} (inr (Ws , f)) (inl q) = inr (Ws , ordered++ q f)
      pcomp {X} {Y} {Z} (inr (Ws , f)) (inr (Vs , g)) = inr (Ws ++ (Vs) , Seq++ f g)

      module _ {X Y : face} where
        left-id : {f : entpath X Y} → pcomp pid f ≡ f
        left-id {inl p} = cong inl (is-prop-valued X Y _ _)
        left-id {inr ([] , f , tt*)} = cong inr (ΣPathP (refl , ΣPathP ((lSet.⊏-prop ≻-LSet X Y _ f) , refl)))
        left-id {inr (W ∷ Ws , f , fs)} = cong inr (ΣPathP (refl , (ΣPathP ((lSet.⊏-prop ≻-LSet X W _ f) , refl))))

        right-id : {f : entpath X Y} → pcomp f pid ≡ f
        right-id {inl p} = cong inl (is-prop-valued X Y _ _)
        right-id {inr ([] , f , tt*)} = cong inr (ΣPathP (refl , ΣPathP ((lSet.⊏-prop ≻-LSet X Y _ f) , refl)))
        right-id {inr (W ∷ Ws , f , fs)} = cong inr (ΣPathP (refl , ΣPathP (refl , (ordered-isProp (ordered++ (is-refl Y) fs) fs))))


    module  _ {X Y Z : face} where
      open IsPoset ⊆-IsPoset

      left-whisker : (f g : entpath X Y) → (h : entpath Y Z)
        → f ≤[ hom X Y ] g → pcomp f h ≤[ hom X Z ] pcomp g h
      left-whisker (inl p) (inl q) (inl r) ϕ = tt*
      left-whisker (inl p) (inl q) (inr ([] , hs)) ϕ = is-refl (toneSet ([] , ≽≻-trans X Y Z q (fst hs) , tt*))
      left-whisker (inl p) (inl q) (inr (U ∷ Us , hs)) ϕ = is-refl (toneSet (U ∷ Us , ≽≻-trans X Y U p (fst hs) , snd hs))
      left-whisker (inl p) (inr x₁) (inl x₂) ϕ = tt*
      left-whisker (inl p) (inr (Vs , gs)) (inr ([] , hs)) ϕ = SeqL1
      left-whisker (inl p) (inr (Vs , gs)) (inr (U ∷ Us , hs)) ϕ = SeqL3 {Ws = U ∷ Us} {Vs = Vs}
      left-whisker (inr (Ws , f)) (inr (Vs , gs)) (inl r) ϕ = SeqL2 gs f ϕ
      left-whisker (inr (Ws , f)) (inr (Vs , gs)) (inr (Us , hs)) ϕ = SeqL5 hs gs f ϕ

      right-whisker : (f : entpath X Y) → (g h : entpath Y Z)
        → g ≤[ hom Y Z ] h → pcomp f g ≤[ hom X Z ] pcomp f h
      right-whisker (inl p) (inl q) (inl r) ϕ = tt*
      right-whisker (inl p) (inl q) (inr ([] , hs)) ϕ = tt*
      right-whisker (inl p) (inl q) (inr (U ∷ Us , hs)) ϕ = tt*
      right-whisker (inl p) (inr ([] , g)) (inr ([] , hs)) ϕ = is-refl (toneSet ([] , ≽≻-trans X Y Z p (fst hs) , tt*))
      right-whisker (inl p) (inr ([] , g)) (inr (U ∷ Us , hs)) ϕ = SeqL1 {Ws = U ∷ Us}
      right-whisker (inl p) (inr (V ∷ Vs , g)) (inr ([] , hs)) ϕ = SeqL6 {Ws = V ∷ Vs} {Vs = []} g hs ϕ
      right-whisker (inl p) (inr (V ∷ Vs , g)) (inr (U ∷ Us , hs)) ϕ = SeqL6 {Ws = V ∷ Vs} {Vs = U ∷ Us} g hs ϕ
      right-whisker (inr (Ws , f)) (inl q) (inl r) ϕ = is-refl (toneSet (Ws , ordered++ r f))
      right-whisker (inr (Ws , f)) (inl q) (inr (Us , hs)) ϕ = SeqL4 {Adec = decFace}
      right-whisker (inr (Ws , f)) (inr (Vs , g)) (inr (Us , hs)) ϕ = SeqL7 g hs ϕ


    module  _ {X Y Z W : face} where
      -- open IsPoset (pstr ≽-Poset)
      -- open lSet ≻-LSet

      passoc : {f : ∣ hom X Y ∣ₚ} {g : ∣ hom Y Z ∣ₚ} {h : ∣ hom Z W ∣ₚ}
        → pcomp f (pcomp g h) ≡ pcomp (pcomp f g) h
      passoc {inl p} {inl q} {inl r} = refl
      passoc {inl p} {inl q} {inr ([] , hs)} = cong inr (ΣPathP (refl , ΣPathP (lSet.⊏-prop ≻-LSet X W _ _ , refl)))
      passoc {inl p} {inl q} {inr (U ∷ Us , hs)} = cong inr (ΣPathP (refl , ΣPathP ((lSet.⊏-prop ≻-LSet X U _ _) , refl)))
      passoc {inl p} {inr ([] , gs)} {inl r} = cong inr (ΣPathP (refl , (ΣPathP (lSet.⊏-prop ≻-LSet X W _ _ , refl))))
      passoc {inl p} {inr (V ∷ Vs , gs)} {inl r} = cong inr (ΣPathP (refl , (ΣPathP ((lSet.⊏-prop ≻-LSet X V _ _) , (ordered-isProp _ _)))))
      passoc {inl p} {inr ([] , gs)} {inr ([] , hs)} = cong inr (ΣPathP (refl , (ΣPathP ((lSet.⊏-prop ≻-LSet X W _ _) , refl))))
      passoc {inl p} {inr ([] , gs)} {inr (U ∷ Us , hs)} = cong inr (ΣPathP (refl , (ΣPathP ((lSet.⊏-prop ≻-LSet X U _ _) , refl))))
      passoc {inl p} {inr (V ∷ Vs , gs)} {inr (Us , hs)} = cong inr (ΣPathP (refl , (ΣPathP ((lSet.⊏-prop ≻-LSet X V _ _) , (ordered-isProp _ _)))))
      passoc {inr (Ws , fs)} {inl q} {inl r} = cong inr (ΣPathP (refl , (ordered-isProp _ _)))
      passoc {inr ([] , fs)} {inl q} {inr ([] , hs)} = cong inr (ΣPathP (refl , (ΣPathP ((lSet.⊏-prop ≻-LSet X W _ _) , refl))))
      passoc {inr ([] , fs)} {inl q} {inr (U ∷ Us , hs)} = cong inr (ΣPathP (refl , (ΣPathP (lSet.⊏-prop ≻-LSet X U _ _ , refl))))
      passoc {inr (W ∷ Ws , fs)} {inl q} {inr ([] , hs)} = cong inr (ΣPathP (refl , (ΣPathP (refl , (ordered-isProp _ _)))))
      passoc {inr (W ∷ Ws , fs)} {inl q} {inr (U ∷ Us , hs)} = cong inr (ΣPathP (refl , ΣPathP (refl , ordered-isProp _ _)))
      passoc {inr (Ws , fs)} {inr (Vs , gs)} {inl r} = cong inr (ΣPathP (refl , (ordered-isProp _ _)))
      passoc {inr (Ws , fs)} {inr (Vs , gs)} {inr (Us , hs)} = cong inr (ΣPathP ((sym (++-assoc Ws Vs Us)) , toPathP (ordered-isProp _ _)))

  inlLeft : {X Y : face} → (p : X ≽ Y) (g : entpath X Y)
    → (≤P (pCategory.hom Ent X Y) (inl p) g)
  inlLeft p (inl x) = tt*
  inlLeft p (inr x) = tt*


module FacePoset (K : SimplicialComplex {ℓ₀} {ℓ₀}) where
  open SimplicialComplex.SimplicialComplex K
  open Seq.Seq ≻-LSet

  open EntPath K

  FacePoset : pCategory
  FacePoset = Poset→pCategory ≽-Poset

  module FacePoset = pCategory FacePoset
  module Ent = pCategory FacePoset

  FacePoset≃Ent : CatEquiv Ent FacePoset
  FacePoset≃Ent = cateq G F μ η
    where
    F : pFunctor FacePoset Ent
    F = pfunct (idfun face) ≽→entpath (λ _ _ _ → tt*) (λ {X} → refl) λ _ _ → tt*

    G : pFunctor Ent FacePoset
    G = pfunct (idfun face) entpath→≽ (λ _ _ _ → tt*) (λ {X} → refl) λ _ _ → tt*

    η : pNatTrans (Fcomp G F) (pId Ent)
    η = pnat (λ X → inl (⊆L-refl _)) λ f → inlLeft _ _

    μ : pNatTrans (pId FacePoset) (Fcomp F G)
    μ = pnat (λ X → ⊆L-refl _) λ f → tt*
