{-# OPTIONS --cubical --safe #-}
module ClassifyingSpace where

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
open import SimplicialComplex
open import SimplicialSet
open import PCategory
open import EntrancePath
open import Nerve
open import Realization


private
  variable
    ℓ ℓ₀ ℓ₁ : Level



𝓑 : pCategory → Type ℓ
𝓑 C = ∣ Nerve C ∣ˢ

𝓑₁ : {C D : pCategory {ℓ}} → pFunctor C D → 𝓑 C → 𝓑 D
𝓑₁ F = Δ∣ Nerve₁ F ∣₁


𝓑₁-id : {C : pCategory {ℓ}} → (a : 𝓑 C) → 𝓑₁ (pId C) a ≡ a
𝓑₁-id {ℓ} {C} = Δ∣_∣elim.fun
  (λ a → isOfHLevelSuc 2 (trunc (𝓑₁ (pId C) a) a) )
  (λ x → refl)
  (λ f i → refl)
  λ {x} {y} {z} {f} {g} {h} ϕ → isGroupoid→isGroupoid' trunc
    (λ i _ → 𝓑₁ (pId C) (edge f i)) (λ j _ → 𝓑₁ (pId C) (vert z))
    (λ i _ → 𝓑₁ (pId C) (edge h i)) (λ i _ → 𝓑₁ (pId C) (edge g i))
    (λ i j → 𝓑₁ (pId C) (triangle ϕ i j)) (triangle ϕ)
  where open pCategory C

𝓑₁-comp : {C D E : pCategory {ℓ}} (F : pFunctor C D) (G : pFunctor D E)
  → ((a : 𝓑 C) → 𝓑₁ G (𝓑₁ F a) ≡ 𝓑₁ (G ∘₁ F) a)
𝓑₁-comp F G = Δ∣_∣elim.fun
  (λ a → isOfHLevelSuc 2 (trunc (𝓑₁ G (𝓑₁ F a)) (𝓑₁ (Fcomp F G) a)))
  (λ x → refl)
  (λ f i → refl)
  λ {x} {y} {z} {f} {g} {h} ϕ → isGroupoid→isGroupoid' trunc
    (λ i _ → 𝓑₁ G (𝓑₁ F (edge f i))) (λ j _ → 𝓑₁ G (𝓑₁ F (vert z)))
    (λ i _ → 𝓑₁ G (𝓑₁ F (edge h i))) (λ i _ → 𝓑₁ G (𝓑₁ F (edge g i)))
    (λ i j → 𝓑₁ G (𝓑₁ F (triangle ϕ i j))) (λ i j → 𝓑₁ (Fcomp F G) (triangle ϕ i j))


module _ {C : pCategory {ℓ}} where
  open pCategory C

  squareCommMorphism : {x y z w : ( ob )} → {f : ∣ hom x y ∣ₚ}
    → {g : ∣ hom x z ∣ₚ} → {f' : ∣ hom y w ∣ₚ} → {g' : ∣ hom z w ∣ₚ}
    → (pcomp g g') ≤[ hom x w ] (pcomp f f')
    → Square (edge {ℓ} {Nerve C} f) (edge g') (edge g) (edge f')
  squareCommMorphism {x} {y} {z} {w} {f} {g} {f'} {g'} ϕ =
    doubleTriangle (g' ∘ g) ϕ (is-refl (g' ∘ g))
    where open IsPoset (pstr (hom x w))






module _ {C D : pCategory {ℓ}} where
  pNatTrans→Homotopy : (F G : pFunctor C D) → pNatTrans F G
    → ((a : 𝓑 C) → 𝓑₁ F a ≡ 𝓑₁ G a)
  pNatTrans→Homotopy F G η = Δ∣_∣elim.fun
    (λ a → isOfHLevelSuc 2 (trunc (𝓑₁ F a) (𝓑₁ G a)))
    (λ x → edge (η.α x))
    (λ {x} {y} f i → doubleTriangle (η.α y D.∘ F.smap₁ f) (η.comm f) (IsPoset.is-refl (pstr (D.hom (F.smap₀ x) (G.smap₀ y))) (η.α y D.∘ F.smap₁ f)) i)
    λ {x} {y} {z} {f} {g} {h} ϕ → isGroupoid→isGroupoid' trunc
      (squareCommMorphism {C = D} (η.comm f)) (λ l → edge (η.α z))
      (squareCommMorphism {C = D} (η.comm h)) (squareCommMorphism {C = D} (η.comm g))
      (triangle (F.smap₂ ϕ)) (triangle (G.smap₂ ϕ))
    where
    module D = pCategory D
    module F = ΔMap (Nerve₁ F)
    module G = ΔMap (Nerve₁ G)
    module η = pNatTrans η




pNatTrans→retract : {C D : pCategory {ℓ}} (F : pFunctor C D) (G : pFunctor D C)
  → pNatTrans (G ∘₁ F) (pId C) → retract (𝓑₁ F) (𝓑₁ G)
pNatTrans→retract {ℓ} {C} {D} F G η x = 𝓑₁-comp F G x ∙(pNatTrans→Homotopy (G ∘₁ F) (pId C) η x) ∙ 𝓑₁-id {C = C} x

pNatTrans→section : {C D : pCategory {ℓ}} (F : pFunctor C D) (G : pFunctor D C)
  → pNatTrans (pId D) (F ∘₁ G)  → section (𝓑₁ F) (𝓑₁ G)
pNatTrans→section  {ℓ} {C} {D} F G η x = 𝓑₁-comp G F x ∙ sym (pNatTrans→Homotopy (pId D) (F ∘₁ G) η x) ∙ 𝓑₁-id {C = D} x

module _ {C D : pCategory {ℓ}} where
  CatEquiv→HomEquiv : CatEquiv C D → 𝓑 C ≡ 𝓑 D
  CatEquiv→HomEquiv (cateq F G η ν) = isoToPath (iso (𝓑₁ F) (𝓑₁ G) ι ρ) where
    ι : (x : 𝓑 D) → 𝓑₁ F (𝓑₁ G x) ≡ x
    ι x = 𝓑₁-comp G F x ∙ sym (pNatTrans→Homotopy (pId D) (F ∘₁ G) η x) ∙ 𝓑₁-id {C = D} x
    ρ : (x : 𝓑 C) → 𝓑₁ G (𝓑₁ F x) ≡ x
    ρ x = 𝓑₁-comp F G x ∙ (pNatTrans→Homotopy (G ∘₁ F) (pId C) ν x) ∙ 𝓑₁-id {C = C} x



⊤pCategory-isContr : isContr (𝓑 (⊤pCategory {ℓ}))
fst ⊤pCategory-isContr = vert tt*
snd ⊤pCategory-isContr = Δ∣_∣elim.fun (λ a → isOfHLevelSuc 2 (trunc (vert tt*) a))
  (λ _ → edge tt*) (λ _ → flipSquare (◤ tt*))
  λ ϕ → isGroupoid→isGroupoid' trunc
    (flipSquare (◤ tt*)) (λ j → edge tt*)
    (flipSquare (◤ tt*)) (flipSquare (◤ tt*))
    (λ _ _ → vert tt*) (triangle ϕ)


module _ (C : pCategory {ℓ}) where
  pMax-IsContr : (z : pMax C) → isContr (𝓑 C)
  pMax-IsContr z = subst isContr (CatEquiv→HomEquiv (C-ispMax→C≃⊤pCategory C z)) ⊤pCategory-isContr

  Initial-IsContr : (z : Initial C) → isContr (𝓑 C)
  Initial-IsContr z = subst isContr (sym (CatEquiv→HomEquiv (C-isInitial→C≃⊤pCategory C z))) ⊤pCategory-isContr



module _ where
  open FacePoset
  open EntPath

  Ent≡FacePoset : (K : SimplicialComplex {ℓ₀} {ℓ₀}) → 𝓑 (Ent K) ≡ 𝓑 (FacePoset K)
  Ent≡FacePoset K = CatEquiv→HomEquiv (FacePoset≃Ent K)
