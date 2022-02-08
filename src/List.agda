{-# OPTIONS --cubical --safe #-}
module List where

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

module _ {A : Type ℓ₀} where

  Listη : {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
  Listη {x} {y} {xs} {ys} p q =  subst (λ a → x ∷ xs ≡ a ∷ ys) p (cong (x ∷_) q)

  ¬xs++[x]≡nil : ∀ {x : A} {xs} → ¬Type (xs ++ [ x ] ≡ [])
  ¬xs++[x]≡nil {x} {[]} = ¬cons≡nil
  ¬xs++[x]≡nil {x} {y ∷ xs} = ¬cons≡nil

  ++inj₁ : {xs ys : List A} {z : A} → xs ++ z ∷ [] ≡ ys ++ z ∷ [] → xs ≡ ys
  ++inj₁ {[]} {[]} {z} p = refl
  ++inj₁ {[]} {y ∷ ys} {z} p = absurd (¬xs++[x]≡nil (sym (cons-inj₂ p)))
  ++inj₁ {x ∷ xs} {[]} {z} p = absurd (¬xs++[x]≡nil (cons-inj₂ p))
  ++inj₁ {x ∷ xs} {y ∷ ys} {z} p = Listη (cons-inj₁ p) (++inj₁ (cons-inj₂ p))


  -- We propositionally truncate Any. Note that there might in general be
  -- multiple inhabitants of Any, but the only property we are concerned with is
  -- membership in a set, which can be shown to be a proposition.

  data Any (P : A → Type ℓ₁) : (List A) → Type (ℓ-max ℓ₀ ℓ₁) where
    here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
    there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)
    trunc : ∀ {xs} → isProp (Any P xs)

  module AnyRec (P : A → Type ℓ₁) {y : A} {xs : List A} {B : Type ℓ} (B-isProp : isProp B)
    (here* : (P y) → B)
    (there* : (Any P xs) → B)
    where
    fun : (Any P (y ∷ xs)) → B
    fun (here px) = here* px
    fun (there pxs) = there* pxs
    fun (trunc y z i) = B-isProp (fun y) (fun z) i


module _ {A : Type ℓ₀} where

  _∈_ : A → List A → Type ℓ₀
  _∈_ x = Any (x ≡_)

  ∈rec : {x y : A} {xs : List A} {B : Type ℓ} (B-isProp : isProp B)
    (here* : (x ≡ y) → B)
    (there* : (x ∈ (xs)) → B)
    → (x ∈ (y ∷ xs)) → B
  ∈rec {A} {x} {xs} = AnyRec.fun (x ≡_)


_closedUnder_ : {A : Type ℓ₀} → List A → (_⊑_ : A → A → Type ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
_closedUnder_ {A = A} C _⊑_ = (X : A) → X ∈ C → (Y : A) → Y ⊑ X → Y ∈ C

module _ {A : Type ℓ₀} where
  map∈ : ∀ {ℓ'} {B : Type ℓ'} → (xs : List A) → (Σ[ x ∈ A ] x ∈ xs → B) → List B
  map∈ [] f = []
  map∈ (x ∷ xs) f = f (x , (here refl)) ∷ map∈ xs λ (y , y∈xs) → f (y , (there y∈xs))

  0<length : {xs : List A} → ¬Type (xs ≡ []) → 0 < length xs
  0<length {[]} P = absurd (P refl)
  0<length {x ∷ xs} P = (length xs) , (+-suc (length xs) 0 ∙ cong suc (+-zero (length xs)))

module _ {A : Type ℓ₀} where
  ¬x∈[] : {x : A} → ¬Type (x ∈ [])
  ¬x∈[] {x} (trunc p q i) = isProp⊥ (¬x∈[] p) (¬x∈[] q) i

  x∈xsx : {x : A} {xs : List A} → x ∈ (xs ++ [ x ])
  x∈xsx {x} {[]} = here refl
  x∈xsx {x} {y ∷ xs} = there x∈xsx

  ∈→¬[] : {x : A} {xs : List A} → x ∈ xs → ¬Type (xs ≡ [])
  ∈→¬[] {x} {[]} P = absurd (¬x∈[] P)
  ∈→¬[] {x} {x₁ ∷ xs} P = ¬cons≡nil

module _ {A : Type ℓ₀} (A-isSet : isSet A) where
  x∈[y]→x≡y : {x y : A} → x ∈ [ y ] → x ≡ y
  x∈[y]→x≡y = ∈rec (A-isSet _ _) (λ px → px) λ pxs → absurd (¬x∈[] pxs)

module _ {A : Type ℓ₀} where
  _∈?_ : {Adec : Discrete A} → (x : A) (xs : List A) → Dec (x ∈ xs)
  _∈?_ {Adec} x [] = no (¬x∈[])
  _∈?_ {Adec} x (y ∷ xs) with Adec x y | _∈?_ {Adec} x xs
  ... | yes p | _ = yes (here p)
  ... | no ¬p | yes p = yes (there p)
  ... | no ¬p | no ¬q = no (∈rec isProp⊥ ¬p ¬q)

  _∈D_ : {Adec : Discrete A} → (x : A) (xs : List A) → Discrete (x ∈ xs)
  (x ∈D xs) p q = yes (trunc p q)


listStep : {A : Type ℓ₀} {x y : A} {xs : List A} → ¬ x ≡ y → x ∈ (y ∷ xs)  → x ∈ xs
listStep p = ∈rec trunc (λ px → absurd (p px)) (idfun _)


module _ {A : Type ℓ₀} {Adec : Discrete A} where
  y∈xs→y≢xs→⊥ : {y : A} {xs : List A} → y ∈ xs → ((x : A) → (x ∈ xs) → ¬Type (y ≡ x)) → ⊥
  y∈xs→y≢xs→⊥ {y} {[]} y∈xs y≢xs = ¬x∈[] y∈xs
  y∈xs→y≢xs→⊥ {y} {x ∷ xs} y∈xs y≢xs with Adec y x
  ... | yes p = y≢xs x (here refl) p
  ... | no ¬p = y∈xs→y≢xs→⊥ {y} {xs} (listStep ¬p y∈xs) λ x₁ x₂ x₃ → y≢xs y y∈xs refl



module _ {A : Type ℓ₀} (Adec : Discrete A) where
  dec++ : (z : A) (xs ys : List A) → z ∈ (xs ++ ys) → (z ∈ xs) ⊎ (z ∈ ys)
  dec++ z [] ys p = inr p
  dec++ z (x ∷ xs) ys p with Adec z x
  ... | yes q = inl (here q)
  ... | no ¬q with dec++ z xs ys (listStep ¬q p)
  ... | inl r = inl (there r)
  ... | inr r = inr r

module _ {A : Type ℓ₀} {B : Type ℓ₁} where
  mapcomm : (xs ys : List A) (f : A → B)
    → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
  mapcomm [] ys f = refl
  mapcomm (x ∷ xs) ys f = cong (f x ∷_) (mapcomm xs ys f)



module _ {A : Type ℓ₀} where
  x∈xs→x∈ys++xs : (x : A) (xs ys : List A) → x ∈ xs → x ∈ (ys ++ xs)
  x∈xs→x∈ys++xs x xs [] p = p
  x∈xs→x∈ys++xs x xs (y ∷ ys) p = there (x∈xs→x∈ys++xs x xs ys p)

  x∈xs→x∈xs++ys : {Adec : Discrete A} (x : A) (xs ys : List A) → x ∈ xs → x ∈ (xs ++ ys)
  x∈xs→x∈xs++ys x [] ys p = absurd (¬x∈[] p)
  x∈xs→x∈xs++ys {Adec} x (x' ∷ xs) ys p with Adec x x'
  ... | yes q = here q
  ... | no ¬q = there (x∈xs→x∈xs++ys {Adec} _ _ _ (listStep ¬q p))


module _ {A : Type ℓ₀} where
  _⊆L_ : List A → List A → Type ℓ₀
  xs ⊆L ys = (x : A) → (x ∈ xs) → (x ∈ ys)

  ⊆L-isProp : {xs ys : List A} → isProp (xs ⊆L ys)
  ⊆L-isProp = isPropΠ (λ x → isPropΠ (λ x∈xs → trunc))

  []⊆Lxs : (xs : List A) → [] ⊆L xs
  []⊆Lxs xs x p = absurd (¬x∈[] p)

  ¬xs⊆L[] : (x : A) (xs : List A) → ¬Type ((x ∷ xs) ⊆L [])
  ¬xs⊆L[] x xs p = absurd (¬x∈[] (p x (here refl)))


  open BinaryRelation

  ⊆L-refl : isRefl _⊆L_
  ⊆L-refl xs x x∈xs = x∈xs

  ⊆L-trans : isTrans _⊆L_
  ⊆L-trans xs ys zs xs⊆Lys ys⊆Lzs x x∈xs = ys⊆Lzs x (xs⊆Lys x x∈xs)

  ∈⊆case : (Adec : isSet A) {xs ys : List A} {x : A} → xs ⊆L ys → x ∈ ys → (x ∷ xs) ⊆L ys
  ∈⊆case Adec {xs} {[]} {x} P p = absurd (¬x∈[] p)
  ∈⊆case Adec {xs} {y ∷ ys} {x} P p z = ∈rec trunc (λ px → subst (_∈ (y ∷ ys)) (sym px) p) (λ q → P z q)

  ¬xxs⊆L[] : {x : A} {xs : List A} → ¬Type ((x ∷ xs) ⊆L [])
  ¬xxs⊆L[] {x} {xs} p = ¬x∈[] (p x (here refl))

  xs⊆Lys→xs⊆Lyys : {xs ys : List A} → (y : A) → xs ⊆L ys → xs ⊆L (y ∷ ys)
  xs⊆Lys→xs⊆Lyys {xs} {ys} y p x x∈xs = there (p x x∈xs)

  xs⊆Lys→xxs⊆Lxys : (xs ys : List A) (x : A) → (xs ⊆L ys)
    → (x ∷ xs) ⊆L (x ∷ ys)
  xs⊆Lys→xxs⊆Lxys xs ys x P z = ∈rec trunc here λ pxs → there (P z pxs)


  ⊆L-skip : {x : A} {xs ys : List A} → (x ∷ xs) ⊆L ys → xs ⊆L ys
  ⊆L-skip {x} {xs} {ys} P z z∈xs = P z (there z∈xs)

  ⊆L-≡step : {x : A} {xs : List A} {y : A} {ys : List A} → ¬Type (x ∷ xs ≡ y ∷ ys) → x ≡ y
    → ¬Type (xs ≡ ys)
  ⊆L-≡step {x} {[]} {y} {[]} ¬P p = absurd (¬P (Listη p refl))
  ⊆L-≡step {x} {[]} {y} {y' ∷ ys} ¬P p = ¬nil≡cons
  ⊆L-≡step {x} {x' ∷ xs} {y} {[]} ¬P p = ¬cons≡nil
  ⊆L-≡step {x} {x' ∷ xs} {y} {y' ∷ ys} ¬P p = λ Q → absurd (¬P (Listη p Q))


module _ {A : Type ℓ₀} where
  SeqL1 : {X Z : A} {Ws : List A} → (X ∷ [] ++ [ Z ]) ⊆L (X ∷ Ws ++ [ Z ])
  SeqL1 {X} {Z} {Ws} E = ∈rec trunc here λ px → (there (x∈xs→x∈ys++xs _ _ _ px))

  SeqL3 : {X Z : A} {Ws Vs : List A} → (X ∷ Ws ++ [ Z ]) ⊆L (X ∷ (Vs ++ Ws) ++ [ Z ])
  SeqL3 {X} {Z} {Ws} {Vs} E = ∈rec trunc here
    (λ px → there (transport
      (cong (Any (_≡_ E))
      (sym (++-assoc Vs Ws [ Z ]))) (x∈xs→x∈ys++xs _ _ Vs px)))

  SeqL4 : {Adec : Discrete A} {X Z : A} {Ws Vs : List A} → (X ∷ Ws ++ [ Z ]) ⊆L (X ∷ (Ws ++ Vs) ++ [ Z ])
  SeqL4 {Adec} {X} {Z} {Ws} {Vs} E = ∈rec trunc here helper
    where
    helper : E ∈ (Ws ++ [ Z ]) → E ∈ (X ∷ (Ws ++ Vs) ++ [ Z ])
    helper P with dec++ Adec E Ws [ Z ] P
    ... | inl Q = there (x∈xs→x∈xs++ys {Adec = Adec} _ _ _
                         (x∈xs→x∈xs++ys {Adec = Adec} _ _ _ Q))
    ... | inr Q = there (x∈xs→x∈ys++xs _ _ _ Q)
