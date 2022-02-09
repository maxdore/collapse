{-# OPTIONS --cubical --safe #-}
module NeSet where

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
-- open import Cubical.Data.Bool
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


private
  variable
    ℓ ℓ₀ ℓ₁ : Level



open BinaryRelation

module neSet {ℓ₀ ℓ₁} (O : lSet {ℓ₀} {ℓ₁}) where
  open lSet O public

  neSet : Type (ℓ-max ℓ₀ ℓ₁)
  neSet = Σ[ x ∈ carrier ] Σ[ xs ∈ List carrier ] ordered (x ∷ xs)

  discreteneSet : Discrete neSet
  discreteneSet = discreteΣ dec (λ x → discreteΣ (discreteList dec) (λ xs → discreteOrdered (x ∷ xs)))

  neSet-isSet : isSet neSet
  neSet-isSet = Discrete→isSet (discreteneSet)

  toList : neSet → List carrier
  toList (x , xs , _) = x ∷ xs

  card : neSet → ℕ
  card X = length (toList X)

  toList≡ : (X Y : neSet) → X ≡ Y → toList X ≡ toList Y
  toList≡ (x , xs , ds) (y , ys , es) p = Listη (fst (PathPΣ p)) (fst (PathPΣ (snd (PathPΣ p))))

  toneSet≡ : (X Y : neSet) → toList X ≡ toList Y → X ≡ Y
  toneSet≡ (x , xs , ds) (y , ys , es) p  =
    ΣPathP ((cons-inj₁ p) , (ΣPathP ((cons-inj₂ p) , toPathP (ordered-isProp _ _))))

  singleton : carrier → neSet
  singleton x = x , [] , tt*

  _⊆_ : neSet → neSet → Type ℓ₀
  X ⊆ Y = toList X ⊆L toList Y

  _⊂_ : neSet → neSet → Type ℓ₀
  X ⊂ Y = (X ⊆ Y) × (card X < card Y)


  x⊏xs : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → (z : carrier) → (z ∈ xs) → x ⊏ z
  x⊏xs {x} {[]} ds z P = absurd (¬x∈[] P)
  x⊏xs {x} {y ∷ xs} (d , ds) z (here px) = subst (x ⊏_) (sym px) d
  x⊏xs {x} {y ∷ xs} (d , ds) z (there P) = ⊏-trans x y z d (x⊏xs ds z P)
  x⊏xs {x} {y ∷ xs} ds z (trunc P Q i) = ⊏-prop x z (x⊏xs ds z P) (x⊏xs ds z Q) i

  ⊆total : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y ∷ ys) ⊆L (x ∷ xs) → ¬Type (x ≡ y) → x ⊏ y
  ⊆total {x} {xs} ds {y} {ys} es P ¬p = ∈rec (⊏-prop x y) (λ px → absurd (¬p (sym px))) (x⊏xs ds y) (P y (here refl))

  ⊏-step : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y ∷ ys) ⊆L (x ∷ xs) → ¬Type (x ≡ y)
    → (y ∷ ys) ⊆L xs
  ⊏-step {x} {xs} ds {y} {ys} es P p z z∈Y = listStep (λ q → ⊏→≢ (x⊏xs (⊆total ds es P p , es) z z∈Y) (sym q)) (P z z∈Y)

  split⊆ : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y , ys , es) ⊆ (x , xs , ds) → (x ≡ y) ⊎ (x ⊏ y)
  split⊆ {x} {[]} ds {y} {ys} es P with dec x y
  ... | yes p = inl p
  ... | no ¬p = absurd (¬xs⊆L[] _ _ (⊏-step ds es P ¬p))
  split⊆ {x} {x' ∷ xs} (d , ds) {y} {ys} es P with dec x y
  ... | yes p = inl p
  ... | no ¬p = inr (srec (λ q → subst (x ⊏_) q d) (⊏-trans _ _ _ d) IH)
    where
    IH = split⊆ ds es (⊏-step (d , ds) es P ¬p)


  ⊆-skip : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y ∷ ys) ⊆L (x ∷ xs) → x ≡ y → ys ⊆L xs
  ⊆-skip {x} {xs} ds {y} {ys} es P p z z∈Y = listStep (λ q → ⊏→≢ ( subst (_⊏ z) (sym p) (x⊏xs es z z∈Y)) (sym q)) (P z (there z∈Y))

  ⊆singleton-extract : {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys)) {x : carrier}
    → (y , ys , es) ⊆ (singleton x) → y ≡ x
  ⊆singleton-extract {y} {[]} es {x} P = x∈[y]→x≡y carrier-isSet (P y (here refl))
  ⊆singleton-extract {y} {y' ∷ ys} es {x} P = x∈[y]→x≡y carrier-isSet (P y (here refl))

  ⊆singleton-extract' : {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys)) {x : carrier}
    → (y , ys , es) ⊆ (singleton x) → ys ≡ []
  ⊆singleton-extract' {y} {[]} es {x} P = refl
  ⊆singleton-extract' {y} {y' ∷ ys} es {x} P with dec x y
  ... | yes p = absurd (¬x∈[] (⊆-skip tt* es P p y' (here refl)))
  ... | no ¬p = absurd (¬p (sym (x∈[y]→x≡y carrier-isSet (P y (here refl)))))

  ys⊆[x] : {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys)) {x : carrier}
    → (y , ys , es) ⊆ (singleton x) → y ∷ ys ≡ x ∷ []
  ys⊆[x] {y} {ys} es {x} P = Listη (⊆singleton-extract es P) (⊆singleton-extract' es P)



  arith : (m : ℕ) → Σ ℕ (λ k → k + 2 ≡ suc (suc m))
  arith m = m , +-suc (m) 1 ∙ cong suc (+-suc (m) 0) ∙ cong suc (cong suc (+-zero (m)))


  ⊆→length : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (x , xs , ds) ⊆ (y , ys , es)
    → length (x ∷ xs) ≤ length (y ∷ ys)
  ⊆→length {x} {xs} ds {y} {[]} es P = 0 , cong length (ys⊆[x] ds P)
  ⊆→length {x} {[]} ds {y} {y' ∷ ys} (e , es) P = (suc (length ys)) , cong suc (+-suc (length ys) 0 ∙ cong suc (+-zero _))
  ⊆→length {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with split⊆ (e , es) (d , ds) P
  ... | inl p = suc-≤-suc (⊆→length ds es (⊆-skip (e , es) (d , ds) P p))
  ... | inr p = ≤-suc (⊆→length (d , ds) es (⊏-step (e , es) (d , ds) P (⊏→≢ p)))


  ⊆→≡→< : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (x , xs , ds) ⊆ (y , ys , es)
    → ¬Type (PathP (λ i → List carrier) (y ∷ ys) (x ∷ xs))
    → length (x ∷ xs) < length (y ∷ ys)
  ⊆→≡→< {x} {[]} ds {y} {ys} es P Q with split⊆ es ds P
  ... | inl p =  suc-≤-suc (0<length (⊆L-≡step Q p))
  ... | inr p = suc-≤-suc (0<length (∈→¬[] ((⊏-step (es) (ds) P (⊏→≢ p)) x (here refl))))
  ⊆→≡→< {x} {x' ∷ xs} (d , ds) {y} {[]} es P Q = absurd (¬-<-zero (pred-≤-pred (⊆→length (d , ds) es P)))
  ⊆→≡→< {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P Q with split⊆ (e , es) (d , ds) P
  ... | inl p = suc-≤-suc (⊆→≡→< ds es (⊆-skip (e , es) (d , ds) P p) (⊆L-≡step Q p))
  ... | inr p = suc-≤-suc (⊆→length (d , ds) es (⊏-step (e , es) (d , ds) P (⊏→≢ p)))

  ⊆→≤ : (X Y : neSet) → X ⊆ Y → card X ≤ card Y
  ⊆→≤ (x , xs , ds) (y , ys , es) = ⊆→length ds es

  ⊆→⊂ : (X Y : neSet) → X ⊆ Y → ¬Type (toList Y ≡ toList X) → card X < card Y
  ⊆→⊂ (x , xs , ds) (y , ys , es) = ⊆→≡→< ds es

  ⊆→≡⊎⊂ : (X Y : neSet) → X ⊆ Y → (X ≡ Y) ⊎ (X ⊂ Y)
  ⊆→≡⊎⊂ X Y P with discreteneSet X Y
  ... | yes p = inl p
  ... | no ¬p = inr (P , ⊆→⊂ X Y P (λ q → ¬p (toneSet≡ X Y (sym q))))








  ⊆-IsPoset : IsPoset _⊆_
  ⊆-IsPoset = isposet neSet-isSet (λ xs ys → ⊆L-isProp)
    (λ X → ⊆L-refl (toList X))
    (λ X Y Z → ⊆L-trans (toList X) (toList Y) (toList Z))
    λ (x , xs , ds) (y , ys , es) P Q → toneSet≡ _ _ (lantisym  x xs ds y ys es P Q)
    where
    lantisym : (x : carrier) (xs : List carrier) (ds : ordered (x ∷ xs))
              (y : carrier) (ys : List carrier) (es : ordered (y ∷ ys))
              → (x , xs , ds) ⊆ (y , ys , es)
              → (y , ys , es) ⊆ (x , xs , ds)
              → PathP (λ i → List carrier) (x ∷ xs) (y ∷ ys)
    lantisym x [] ds y [] es P Q = ys⊆[x] ds P
    lantisym x [] ds y (x₁ ∷ ys) es P Q = sym (ys⊆[x] es Q)
    lantisym x (x₁ ∷ xs) ds y [] es P Q = ys⊆[x] ds P
    lantisym x (x' ∷ xs) (d , ds) y (y' ∷ ys) (e , es) P Q
      with split⊆ (e , es) (d , ds) P | split⊆ (d , ds) (e , es) Q
    ... | inl p | inl q = Listη q (lantisym _ _ ds _ _ es (⊆-skip (e , es) (d , ds) P p) (⊆-skip (d , ds) (e , es) Q q))
    ... | inl p | inr q = absurd (⊏-irreflexive _ (subst (x ⊏_) p q))
    ... | inr p | inl q = absurd (⊏-irreflexive _ (subst (y ⊏_) q p))
    ... | inr p | inr q = absurd (⊏-irreflexive _ (⊏-trans _ _ _ p q))


  ⊂LSet : lSet
  ⊂LSet = lset neSet discreteneSet _⊂_ ⊂-prop  (λ X (P , k) → ¬m<m k) ⊂-trans
    where
    ⊂-prop : isPropValued _⊂_
    ⊂-prop X Y = isProp× (IsPoset.is-prop-valued ⊆-IsPoset X Y) m≤n-isProp
    ⊂-trans : isTrans _⊂_
    ⊂-trans X Y Z (P , k) (Q , l) = (IsPoset.is-trans ⊆-IsPoset X Y Z P Q) , (<-trans k l)

  ⊆⊂-trans : (X Y Z : neSet) → X ⊆ Y → Y ⊂ Z → X ⊂ Z
  ⊆⊂-trans X Y Z p q = IsPoset.is-trans (⊆-IsPoset) X Y Z p (fst q) , ≤<-trans (⊆→≤ X Y p) (snd q)

  ⊂⊆-trans : (X Y Z : neSet) → X ⊂ Y → Y ⊆ Z → X ⊂ Z
  ⊂⊆-trans X Y Z p q = IsPoset.is-trans (⊆-IsPoset) X Y Z (fst p) q , <≤-trans (snd p) (⊆→≤ Y Z q)

  insert : (x : carrier) → (Z : neSet) → x ⊏ fst Z → neSet
  insert x (z , zs , es) p = x , z ∷ zs , p , es

  ⊏List : carrier → (List neSet) → Type _
  ⊏List x Ys = (Y : neSet) → Y ∈ Ys → x ⊏ fst Y

  ⊏List-there : {x : carrier} {Y : neSet} {Ys : List neSet}
    → ⊏List x (Y ∷ Ys) → ⊏List x Ys
  ⊏List-there {x} {Y} {Ys} P Y' Q = P Y' (there Q)

  module _ (x : carrier) (Ys : List neSet) (desc : ⊏List x Ys) where
    insertList : List neSet
    insertList = map∈ Ys λ (Y , p) → insert x Y (desc Y p)

  -- Alternative direct way:
  -- insertList : (x : carrier) (Ys : List neSet) (desc : ⊏List x Ys) → List neSet
  -- insertList x [] desc = []
  -- insertList x (Y ∷ Ys) desc = insert x Y (desc Y (here refl)) ∷ insertList x Ys (⊏List-there desc)

  insertList-corr : {x : carrier} {Zs : List neSet} (desc : ⊏List x Zs)
    → (Y : neSet) → (d : x ⊏ fst Y) → Y ∈ Zs
    → insert x Y d ∈ insertList x Zs desc
  insertList-corr {x} {[]} desc Y d P = absurd (¬x∈[] P)
  insertList-corr {x} {Z ∷ Zs} desc Y d = ∈rec trunc
    (λ px → here (toneSet≡ _ _  (cong (x ∷_) (toList≡ Y Z px))))
    λ pxs → there (insertList-corr (⊏List-there desc) Y d pxs)

  insertList-head : {x : carrier} {Zs : List neSet} (desc : ⊏List x Zs)
    → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
    → (y , ys , es) ∈ insertList x Zs desc → y ≡ x
  insertList-head {x} {[]} desc {y} {ys} es P = absurd (¬x∈[] P)
  insertList-head {x} {Z ∷ Zs} desc {y} {ys} es = ∈rec (carrier-isSet y x)
    (λ px → fst (PathPΣ px))
    (insertList-head (⊏List-there desc) es)

  insertList-tail : {x : carrier} {Zs : List neSet} (desc : ⊏List x Zs)
    → {y y' : carrier} {ys : List carrier} ((e , es) : ordered (y ∷ y' ∷ ys))
    → (y , y' ∷ ys , e , es) ∈ insertList x Zs desc → (y' , ys , es) ∈ Zs
  insertList-tail {x} {[]} desc (e , es) P = absurd (¬x∈[] P)
  insertList-tail {x} {Z ∷ Zs} desc (e , es) = ∈rec trunc
    (λ px → here (toneSet≡ _ _ (fst (PathPΣ( snd (PathPΣ px))))))
    (λ pxs → there (insertList-tail (⊏List-there desc) (e , es) pxs))


_>_ : Rel ℕ ℕ ℓ-zero
m > n = (n < m)

ℕlSet = lset ℕ discreteℕ _>_ (λ m n → m≤n-isProp) (λ x → ¬m<m) (λ m n o p q → <-trans q p)


module _ where
  open neSet ℕlSet

  _-to-0 : (n : ℕ) → neSet
  fstn-to-0≡n : (n : ℕ) → fst (n -to-0) ≡ n

  zero -to-0 = singleton 0
  suc n -to-0 = let r = n -to-0 in suc n , toList r , (0 , (cong suc (fstn-to-0≡n n))) , snd (snd r)

  fstn-to-0≡n zero = refl
  fstn-to-0≡n (suc n) = refl

  sucn-ordered : {(1+ n) : ℕ₊₁} → ordered (suc n ∷ fst (n -to-0) ∷ fst (snd (n -to-0)))
  sucn-ordered {1+ n} = ((0 , cong suc (fstn-to-0≡n n)) , snd (snd (n -to-0)))
