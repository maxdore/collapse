{-# OPTIONS --cubical --safe #-}
module PCategory where

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

private
  variable
    ℓ ℓ₀ ℓ₁ : Level



record pCategory {ℓ : Level} : Type (ℓ-suc ℓ) where
  constructor pcat
  field
    ob : Type ℓ
    hom : ob → ob → Poset ℓ ℓ
    pid : ∀ {x} → ∣ hom x x ∣ₚ
    pcomp : ∀ {x y z} → ∣ hom x y ∣ₚ → ∣ hom y z ∣ₚ → ∣ hom x z ∣ₚ
    left-id : ∀ {x y} {f : ∣ hom x y ∣ₚ} → (pcomp pid f) ≡ f
    right-id : ∀ {x y} {f : ∣ hom x y ∣ₚ} → (pcomp f pid) ≡ f
    left-whisker : ∀ {x y z} → (f g : ∣ hom x y ∣ₚ) → (h : ∣ hom y z ∣ₚ)
      → f ≤[ hom x y ] g → pcomp f h ≤[ hom x z ] pcomp g h
    right-whisker : ∀ {x y z} → (f : ∣ hom x y ∣ₚ) → (g h : ∣ hom y z ∣ₚ)
      → g ≤[ hom y z ] h → pcomp f g ≤[ hom x z ] pcomp f h
    passoc : ∀ {x y z w} {f : ∣ hom x y ∣ₚ} {g : ∣ hom y z ∣ₚ} {h : ∣ hom z w ∣ₚ}
      → pcomp f (pcomp g h) ≡ pcomp (pcomp f g) h
  syntax pcomp f g = g ∘ f

⊤pCategory : ∀{ℓ} → pCategory {ℓ}
⊤pCategory {ℓ} = pcat Unit*
  (λ _ _ → ⊤Poset)
  tt*
  (λ _ _ → tt*)
  (λ i → tt*) (λ i → tt*)
  (λ _ _ _ _ → tt*) (λ _ _ _ _ → tt*)
  refl

record pFunctor {ℓ : Level} (C D : pCategory {ℓ}) : Type ℓ where
  constructor pfunct
  private
    module C = pCategory C
    module D = pCategory D
  field
    fmap₀ : ( C.ob ) → ( D.ob )
    fmap₁ : ∀ {x y} → ∣ C.hom x y ∣ₚ → ∣ D.hom (fmap₀ x) (fmap₀ y) ∣ₚ
    fmap₁-mono : ∀ {x y} → isMonotonic (C.hom x y) (D.hom (fmap₀ x) (fmap₀ y)) fmap₁

    id-law : ∀ {x} → fmap₁ (C.pid {x}) ≡ D.pid
    comp-law : ∀ {x y z} (f : ∣ C.hom x y ∣ₚ) (g : ∣ C.hom y z ∣ₚ)
      → fmap₁ (g C.∘ f) ≤[ D.hom (fmap₀ x) (fmap₀ z) ] (fmap₁ g D.∘ fmap₁ f)


Fcomp : {ℓ : Level} {C D E : pCategory {ℓ}} → pFunctor C D → pFunctor D E → pFunctor C E
Fcomp {ℓ} {C} {D} {E} F G = pfunct fmap₀ fmap₁ fmap₁-mono id-law comp-law
  where
  private
    module C = pCategory C
    module D = pCategory D
    module E = pCategory E
    module F = pFunctor F
    module G = pFunctor G

  fmap₀ : ( C.ob ) → ( E.ob )
  fmap₀ x = G.fmap₀ (F.fmap₀ x)

  fmap₁ : {x y : ( C.ob )} → ∣ C.hom x y ∣ₚ → ∣ E.hom (fmap₀ x) (fmap₀ y) ∣ₚ
  fmap₁ f = G.fmap₁ (F.fmap₁ f)

  fmap₁-mono : {x y : ( C.ob )} → isMonotonic (C.hom x y) (E.hom (fmap₀ x) (fmap₀ y)) fmap₁
  fmap₁-mono {x} {y} f g ϕ = G.fmap₁-mono (F.fmap₁ f) (F.fmap₁ g) (F.fmap₁-mono f g ϕ)

  id-law : {x : ( C.ob )} → fmap₁ {x} {x} C.pid ≡ E.pid
  id-law {x} = G.fmap₁ (F.fmap₁ C.pid) ≡⟨ cong G.fmap₁ F.id-law ⟩ G.fmap₁ D.pid ≡⟨ G.id-law ⟩ E.pid ∎

  comp-law : {x y z : ( C.ob )} (f : ∣ C.hom x y ∣ₚ) (g : ∣ C.hom y z ∣ₚ) →
     (fmap₁ (C.pcomp f g)) ≤[ E.hom (fmap₀ x) (fmap₀ z) ] (E.pcomp (fmap₁ f) (fmap₁ g))
  comp-law {x} {y} {z} f g =
    fmap₁ (C.pcomp f g) ≤⟨  G.fmap₁-mono (F.fmap₁ (g C.∘ f)) (F.fmap₁ g D.∘ (F.fmap₁ f)) (F.comp-law f g) ⟩
    G.fmap₁ ((F.fmap₁ g) D.∘ (F.fmap₁ f)) ≤⟨ G.comp-law (F.fmap₁ f) (F.fmap₁ g) ⟩
    (fmap₁ g) E.∘ (fmap₁ f) ◾
    where open PosetReasoning (E.hom (fmap₀ x) (fmap₀ z))


syntax Fcomp F G = G ∘₁ F

pId : (C : pCategory {ℓ}) → pFunctor C C
pId C = pfunct (λ x → x) (λ f → f) (λ _ _ p → p) refl
  (λ {x} {y} {z} → λ f g → (pstr (hom x z)).IsPoset.is-refl (g ∘ f))
  where
  open pCategory C

record pNatTrans {C D : pCategory {ℓ}} (F G : pFunctor C D) : Type ℓ where
  constructor pnat
  private
    open pFunctor
    module C = pCategory C
    module D = pCategory D
  field
    α : (x : ( C.ob )) → ∣ D.hom (fmap₀ F x) (fmap₀ G x) ∣ₚ
    comm : {x y : ( C.ob )} → (f : ∣ C.hom x y ∣ₚ)
      → (α y D.∘ fmap₁ F f) ≤[ D.hom (fmap₀ F x) (fmap₀ G y) ] (fmap₁ G f D.∘ α x)

record CatEquiv (C D : pCategory {ℓ}) : Type ℓ where
  constructor cateq
  field
    F : pFunctor C D
    G : pFunctor D C
    η : pNatTrans (pId D) (F ∘₁ G)
    ν : pNatTrans (G ∘₁ F) (pId C)

pMax : (C : pCategory {ℓ}) → Type ℓ
pMax C = Σ[ z ∈ ( ob ) ] ((w : ( ob )) → Σ[ f ∈ ∣ hom w z ∣ₚ ] P-max (hom w z) f)
  where open pCategory C

Initial : (C : pCategory {ℓ}) → Type ℓ
Initial C = Σ[ z ∈ ( ob ) ] ((w : ( ob )) → Σ[ f ∈ ∣ hom z w ∣ₚ ] P-min (hom z w) f)
  where open pCategory C

C-ispMax→C≃⊤pCategory : ∀{ℓ} (C : pCategory {ℓ}) → (z : pMax C) → CatEquiv ⊤pCategory C
C-ispMax→C≃⊤pCategory {ℓ} C (z , z-isMax) = cateq F G η μ
  where
  private
    module C = pCategory C
  open IsPoset

  F : pFunctor ⊤pCategory C
  F = pfunct (λ _ → z) (λ _ → C.pid) (λ _ _ _ → IsPoset.is-refl (pstr (C.hom z z)) C.pid) refl
    λ _ _ → ≡⇒≤ (C.hom z z) (sym C.left-id)

  G : pFunctor C ⊤pCategory
  G = pfunct (λ _ → tt*) (λ _ → tt*) (λ _ _ _ → tt*) refl λ _ _ → tt*

  η : pNatTrans (pId C) (Fcomp G F)
  η = pnat (λ w → fst (z-isMax w)) λ {x} {y} g → (pstr (C.hom x z)).is-trans _ _
    _ ((snd (z-isMax x) (C.pcomp g (fst (z-isMax y))))) ((≡⇒≤ (C.hom x z) ( sym (C.right-id {f = fst (z-isMax x)}) )))

  μ : pNatTrans (Fcomp F G) (pId ⊤pCategory)
  μ = pnat (λ _ → tt*) λ _ → tt*


C-isInitial→C≃⊤pCategory : ∀{ℓ} (C : pCategory {ℓ}) → (z : Initial C) → CatEquiv C ⊤pCategory
C-isInitial→C≃⊤pCategory C (z , z-isMin) = cateq F G η μ
  where
  private
    module C = pCategory C
  open IsPoset

  F : pFunctor C ⊤pCategory
  F = pfunct (λ _ → tt*) (λ _ → tt*) (λ _ _ _ → tt*) refl λ _ _ → tt*

  G : pFunctor ⊤pCategory C
  G = pfunct (λ _ → z) (λ _ → C.pid) (λ _ _ _ → IsPoset.is-refl (pstr (C.hom z z)) C.pid) refl
    λ _ _ → ≡⇒≤ (C.hom z z) (sym C.left-id)

  η : pNatTrans (pId ⊤pCategory) (Fcomp G F)
  η = pnat (λ _ → tt*) (λ _ → tt*)

  μ : pNatTrans (Fcomp F G) (pId C)
  μ = pnat (λ x → fst (z-isMin x)) λ {x} {y} g →
    (pstr (C.hom z y)).is-trans _ _ _ (≡⇒≤ (C.hom z y) (C.left-id {f = fst (z-isMin y)})) (snd (z-isMin y) (C.pcomp (fst (z-isMin x)) g))

Poset→pCategory : Poset ℓ₀ ℓ₀ → pCategory {ℓ₀}
Poset→pCategory (P , posetstr _≤_ Pstr) = pcat ob hom pid pcomp left-id right-id
  (λ {x} {y} {z} f g h _ → lift tt) (λ {x} {y} {z} f g h _ → lift tt) compassoc
  where
  private
    module Pstr = IsPoset Pstr

  ob : Type _
  ob = P
  hom : ( ob ) → ( ob ) → Poset _ _
  hom x y = hProp→Poset (x ≤ y , Pstr.is-prop-valued x y)
  pid : {x : ( ob )} → ∣ hom x x ∣ₚ
  pid {x} = Pstr.is-refl x
  pcomp : {x y z : ( ob )} → ∣ hom x y ∣ₚ → ∣ hom y z ∣ₚ → ∣ hom x z ∣ₚ
  pcomp {x} {y} {z} f g = Pstr.is-trans x y z f g
  left-id : {x y : ( ob )} {f : ∣ hom x y ∣ₚ} → pcomp pid f ≡ f
  left-id {x} {y} {f} = Pstr.is-prop-valued x y (pcomp pid f) f
  right-id : {x y : ( ob )} {f : ∣ hom x y ∣ₚ} → pcomp f pid ≡ f
  right-id {x} {y} {f} = Pstr.is-prop-valued x y (pcomp f pid) f
  compassoc : {x y z w : ( ob )} {f : ∣ hom x y ∣ₚ} {g : ∣ hom y z ∣ₚ}
      {h : ∣ hom z w ∣ₚ} → pcomp f (pcomp g h) ≡ pcomp (pcomp f g) h
  compassoc {x} {y} {z} {w} {f} {g} {h} = Pstr.is-prop-valued x w (pcomp f (pcomp g h)) (pcomp (pcomp f g) h)
