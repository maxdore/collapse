\begin{code}[hide]
{-# OPTIONS --cubical --safe #-}
module code.Code where

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


-- CHANGES TO MAKE AT THE END
-- RENAME SimplicialComplex to ASC? I think not...
-- RENAME neSet to neSet, lSet to lSet
-- Remove hSet for pCategory
-- Remove Latex tags

\end{code}

\begin{code}[hide]
private
  variable
    ℓ ℓ₀ ℓ₁ : Level

¬Type_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬Type P = P → ⊥

⊤Prop : hProp ℓ
⊤Prop = Unit* , (λ _ _ _ → tt*)
⊥Prop : hProp ℓ
⊥Prop = (⊥* , isProp⊥*)

hProp→hSet : hProp ℓ → hSet ℓ
hProp→hSet (A , p) = A , isOfHLevelSuc 1 p

⊤Set : hSet ℓ
⊤Set = hProp→hSet ⊤Prop
⊥Set : hSet ℓ
⊥Set = hProp→hSet ⊥Prop

open BinaryRelation

isIrreflexive : {A : Type ℓ₀} → Rel A A ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isIrreflexive {A = X} R = (x : X) → ¬Type (R x x)

isTotal : {A : Type ℓ₀} → Rel A A ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isTotal {A = X} R = (x y : X) → ¬Type (x ≡ y) → (R x y) ⊎ (R y x)



hProp→Poset : hProp ℓ → Poset ℓ ℓ
hProp→Poset (A , isProp) = poset A (λ _ _ → Unit*) (isposet (isProp→isSet isProp)
  (λ _ _ _ _ _ → tt*) (λ _ → lift tt) (λ _ _ _ _ _ → lift tt) λ a b p q → isProp a b)

⊤Poset : Poset ℓ ℓ
⊤Poset = hProp→Poset ⊤Prop
⊥Poset : Poset ℓ ℓ
⊥Poset = hProp→Poset ⊥Prop


≡⇒≤ : ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → {x y : P} → x ≡ y → x ≤ y
≡⇒≤ (P , (posetstr _≤_ Pstr)) {x = x} p = subst (λ z → x ≤ z) p (is-refl x)
  where
  open IsPoset Pstr

∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ P ∣ₚ = fst P

isMonotonic : (P Q : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type (ℓ-max ℓ₀ ℓ₁)
isMonotonic (P , (posetstr _≤P_ Pstr)) (Q , (posetstr _≤Q_ Qstr)) f = ((x y : P) → x ≤P y → f x ≤Q f y)

≤P :  ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → P → P → Type ℓ₁
≤P (P , (posetstr _≤_ Pstr)) x y = x ≤ y

syntax ≤P P x y = x ≤[ P ] y

pstr : ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → IsPoset _≤_
pstr P = PosetStr.isPoset (snd P)

P-max : ((P , _) : Poset ℓ₀ ℓ₁) → P → Type (ℓ-max ℓ₀ ℓ₁)
P-max {_} {_} (P , posetstr _≤_ _) x = (∀ y → y ≤ x)

P-min : ((P , _) : Poset ℓ₀ ℓ₁) → P → Type (ℓ-max ℓ₀ ℓ₁)
P-min {_} {_} (P , posetstr _≤_ _) x = (∀ y → x ≤ y)
-- S² S³ Sⁿ ≢
\end{code}





\newcommand{\susp}{%
\begin{code}
data Susp (A : Type) : Type where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south
\end{code}}

\newcommand{\nsphere}{%
\begin{code}
_-sphere : ℕ → Type
(0)-sphere = Bool
(suc n)-sphere = Susp ((n)-sphere)
\end{code}}








\begin{code}[hide]

module _ {A : Type ℓ₀} where

  -- concat : List (List A) -> List A
  -- concat = foldr _++_ []

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



record lSet {ℓ ℓ'} : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  constructor lset
  field
    carrier : Type ℓ
    dec : Discrete carrier
    _⊏_ : carrier → carrier → Type ℓ'
    ⊏-prop : isPropValued _⊏_
    ⊏-irreflexive : isIrreflexive _⊏_
    ⊏-trans : isTrans _⊏_

  carrier-isSet : isSet carrier
  carrier-isSet = Discrete→isSet dec

  ⊏→≢ : {x y : carrier} → x ⊏ y → ¬Type (x ≡ y)
  ⊏→≢ {x} {y} p q = absurd (⊏-irreflexive x (subst (x ⊏_) (sym q) p))


  ordered : List carrier → Type ℓ'
  ordered [] = Unit*
  ordered (x ∷ []) = Unit*
  ordered (x ∷ y ∷ xs) = (x ⊏ y) × ordered (y ∷ xs)

  discreteOrdered : (xs : List carrier) → Discrete (ordered (xs))
  discreteOrdered [] tt* tt* = yes refl
  discreteOrdered (x ∷ []) tt* tt* = yes refl
  discreteOrdered (x ∷ y ∷ xs) = discreteΣ (λ p q → yes (⊏-prop x y p q)) λ _ → discreteOrdered (y ∷ xs)

  ordered-isProp : {xs : List carrier} → isProp (ordered (xs))
  ordered-isProp {[]} = isPropUnit*
  ordered-isProp {x ∷ []} = isPropUnit*
  ordered-isProp {x ∷ y ∷ xs} = isProp× (⊏-prop x y) ordered-isProp





module neSet {ℓ₀ ℓ₁} (O : lSet {ℓ₀} {ℓ₁}) where
  open lSet O public


\end{code}
\newcommand{\neset}{%
\begin{code}
  neSet : Type (ℓ-max ℓ₀ ℓ₁)
  neSet = Σ[ x ∈ carrier ] Σ[ xs ∈ List carrier ] ordered (x ∷ xs)
\end{code}}
\begin{code}[hide]

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


  module WithoutΣ where
\end{code}

\newcommand{\subsets}{%
\begin{AgdaAlign}\begin{AgdaSuppressSpace}
\begin{code}
    subsets : (x : carrier) → (xs : List carrier) → ordered (x ∷ xs) → List neSet
\end{code}
\begin{code}[hide]
    subsets-corr : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ subsets x xs ds
      → (y , ys , es) ⊆ (x , xs , ds)

    x⊏subsets : (x : carrier) {x' : carrier} {xs : List carrier} → ((d , ds) : ordered (x ∷ x' ∷ xs))
      → ⊏List x (subsets x' xs ds)
    x⊏subsets x (d , ds) (y , ys , es) p with (split⊆ ds es (subsets-corr ds es p))
    ... | inl q = subst _ q d
    ... | inr q = ⊏-trans _ _ _ d q

    insertSubsets : (x : carrier) {x' : carrier} {xs : List carrier} → (ordered (x ∷ x' ∷ xs)) → List neSet
    insertSubsets x {x'} {xs} (d , ds) = insertList x (subsets x' xs ds) (x⊏subsets x (d , ds))
\end{code}
\begin{code}
    subsets x [] ds = [ singleton x ]
    subsets x (x' ∷ xs) (d , ds) = [ singleton x ] ++ subsets x' xs ds ++ insertSubsets x (d , ds)
\end{code}
\end{AgdaSuppressSpace}\end{AgdaAlign}
}
\begin{code}[hide]

    subsets-corr {x} {[]} tt* {y} {ys} es P = subst (_⊆ (singleton x)) (sym (x∈[y]→x≡y neSet-isSet P)) (IsPoset.is-refl (⊆-IsPoset) _)

    subsets-corr {x} {x' ∷ xs} (d , ds) {y} {[]} es P with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl Q = λ z z∈[y] → here (x∈[y]→x≡y carrier-isSet z∈[y] ∙ cons-inj₁ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q)))
    ... | inr Q with dec++ discreteneSet _ (subsets x' xs ds) (insertSubsets x (d , ds)) Q
    ... |       inl R = λ y' p → there (subsets-corr ds es R y' p)
    ... |       inr R = subst (λ a → [ a ] ⊆L (x ∷ x' ∷ xs))
                         (sym (insertList-head (x⊏subsets x (d , ds)) es R))
                         λ x₁ x₂ → here (x∈[y]→x≡y carrier-isSet x₂)

    subsets-corr {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl Q = absurd (¬cons≡nil (cons-inj₂ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q))))
    ... | inr Q with dec++ discreteneSet _ (subsets x' xs ds) (insertSubsets x (d , ds)) Q
    ... |       inl R = λ z p → there (subsets-corr ds (e , es) R z p)
    ... |       inr R =  subst (λ a → (a ∷ y' ∷ ys) ⊆L (x ∷ x' ∷ xs))
                           (sym (insertList-head (x⊏subsets x (d , ds)) (e , es) R) )
                           (xs⊆Lys→xxs⊆Lxys _ _ x (subsets-corr ds es (insertList-tail (x⊏subsets x (d , ds)) (e , es) R)))


    subsets-comp : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ⊆ (x , xs , ds)
      → (y , ys , es) ∈ subsets x xs ds
    subsets-comp {x} {[]} ds {y} {ys} es P = here (toneSet≡ _ _ (ys⊆[x] es P))
    subsets-comp {x} {x' ∷ xs} (d , ds) {y} {[]} tt* P with
      split⊆ (d , ds) _ P
    ... | inl p = here (ΣPathP ((sym p) , ΣPathP (refl , refl)))
    ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsets x' xs ds) _
              (there (subsets-comp ds tt* (⊏-step (d , ds) tt* P (⊏→≢ p))))
    subsets-comp {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with
      split⊆ (d , ds) (e , es) P
    ... | inl p = x∈xs→x∈ys++xs _ (insertList x (subsets x' xs ds) (x⊏subsets x (d , ds))) _
                   (subst (_∈ insertList x (subsets x' xs ds) (x⊏subsets x (d , ds))) (toneSet≡ _ _ (cong (_∷ y' ∷ ys) p)) lemma )
                   where
                   IH = subsets-comp ds es (⊆-skip (d , ds) (e , es) P p)
                   lemma = insertList-corr (x⊏subsets x (d , ds)) (y' , ys , es) (subst (_⊏ y') (sym p) e) IH
    ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsets x' xs ds) _
             (there (subsets-comp ds (e , es) (⊏-step (d , ds) (e , es) P (⊏→≢ p))))
\end{code}

\newcommand{\ssubsets}{%
\begin{AgdaAlign}\begin{AgdaSuppressSpace}
\begin{code}
    ssubsets : (x : carrier) → (xs : List carrier) → ordered (x ∷ xs) → List neSet
\end{code}
\begin{code}[hide]

    ssubsets-corr : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ ssubsets x xs ds
      → (y , ys , es) ⊂ (x , xs , ds)

    x⊏ssubsets : (x : carrier) {x' : carrier} {xs : List carrier} → ((d , ds) : ordered (x ∷ x' ∷ xs))
      → ⊏List x (ssubsets x' xs ds)
    x⊏ssubsets x (d , ds) (y , ys , es) p with (split⊆ ds es (fst (ssubsets-corr ds es p)))
    ... | inl q = subst _ q d
    ... | inr q = ⊏-trans _ _ _ d q

    insertSsubsets : (x : carrier) {x' : carrier} {xs : List carrier} → (ordered (x ∷ x' ∷ xs)) → List neSet
    insertSsubsets x {x'} {xs} (d , ds) = insertList x (ssubsets x' xs ds) (x⊏ssubsets x (d , ds))

\end{code}
\begin{code}
    ssubsets x [] ds = []
    ssubsets x (x' ∷ xs) (d , ds) = [ singleton x ] ++ subsets x' xs ds ++ insertSsubsets x (d , ds)
\end{code}
\end{AgdaSuppressSpace}\end{AgdaAlign}
}
\begin{code}[hide]


    ssubsets-corr {x} {[]} tt* {y} {ys} es P = absurd (¬x∈[] P)

    ssubsets-corr {x} {x' ∷ xs} (d , ds) {y} {[]} es P with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl Q = (λ z z∈[y] → here (x∈[y]→x≡y carrier-isSet z∈[y] ∙ cons-inj₁ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q)))) , arith (length xs)
    ... | inr Q with dec++ discreteneSet _ (subsets x' xs ds) (insertSsubsets x (d , ds)) Q
    ... |       inl R = (λ x₁ x₂ → there (sub x₁ x₂)) , arith (length xs)
      where sub = (subsets-corr ds tt* R)
    ... |       inr R = (subst (λ a → [ a ] ⊆L (x ∷ x' ∷ xs))
                         (sym (insertList-head (x⊏ssubsets x (d , ds)) es R))
                         λ x₁ x₂ → here (x∈[y]→x≡y carrier-isSet x₂)) , arith (length xs)

    ssubsets-corr {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl Q = absurd (¬cons≡nil (cons-inj₂ (toList≡ _ _ (x∈[y]→x≡y neSet-isSet Q))))
    ... | inr Q with dec++ discreteneSet _ (subsets x' xs ds) (insertSsubsets x (d , ds)) Q
    ... |       inl R = (λ x₁ x₂ → there (sub x₁ x₂)) , suc-≤-suc (⊆→length (e , es) ds sub)
      where sub = (subsets-corr ds (e , es) R)
    ... |       inr R = mmh , (suc-≤-suc (snd IH))
      where
      IH = ssubsets-corr ds es (insertList-tail (x⊏ssubsets x (d , ds)) (e , es) R)
      mmh = subst (λ a → (a ∷ y' ∷ ys) ⊆L (x ∷ x' ∷ xs))
                           (sym (insertList-head (x⊏ssubsets x (d , ds)) (e , es) R) )
                           (xs⊆Lys→xxs⊆Lxys _ _ x (fst IH))



    ssubsets-comp : {x : carrier} {xs : List carrier} (ds : ordered (x ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ⊂ (x , xs , ds)
      → (y , ys , es) ∈ ssubsets x xs ds
    ssubsets-comp {x} {[]} ds {y} {ys} es P = absurd (¬-<-zero (pred-≤-pred (snd P)))
    ssubsets-comp {x} {x' ∷ xs} (d , ds) {y} {[]} tt* P with
      split⊆ (d , ds) _ (fst P)
    ... | inl p = here (ΣPathP ((sym p) , ΣPathP (refl , refl)))
    ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsets x' xs ds) _ (there IH)
                  where
                  IH = subsets-comp ds tt* ((⊏-step (d , ds) tt* (fst P) (⊏→≢ p)))
    ssubsets-comp {x} {x' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P with
      split⊆ (d , ds) (e , es) (fst P)
    ... | inl p = x∈xs→x∈ys++xs _ (insertList x (ssubsets x' xs ds) (x⊏ssubsets x (d , ds))) _
                  (subst (_∈ insertList x (ssubsets x' xs ds) (x⊏ssubsets x (d , ds))) (toneSet≡ _ _ (cong (_∷ y' ∷ ys) p)) lemma )
                   where
                   IH = ssubsets-comp ds es ((⊆-skip (d , ds) (e , es) (fst P) p) , (pred-≤-pred (snd P)))
                   lemma = insertList-corr (x⊏ssubsets x (d , ds)) (y' , ys , es) (subst (_⊏ y') (sym p) e) IH
    ... | inr p = x∈xs→x∈xs++ys {Adec = discreteneSet} _ (_ ∷ subsets x' xs ds) _ (there (subsets-comp ds (e , es) (⊏-step (d , ds) (e , es) (fst P) (⊏→≢ p))))




\end{code}
\newcommand{\hornComp}{%
\begin{code}
    Λfaces : (x : carrier) (x' : carrier) (xs : List carrier) → ordered (x ∷ x' ∷ xs) → List neSet
    Λfaces x x' xs (d , ds) = [ singleton x ] ++ ssubsets x' xs ds ++ insertSsubsets x (d , ds)
\end{code}}
\begin{code}[hide]

    Λclosed : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ Λfaces x x' xs (ds)
      → (Z : neSet) → Z ⊆ (y , ys , es) → Z ∈ Λfaces x x' xs (ds)
    Λclosed {x} {x'} {[]} (d , ds) {y} {ys} es P (z , zs , fs) Q = subst (_∈ Λfaces x x' [] (d , ds)) (sym Z≡Y) P
      where
      mmh = x∈[y]→x≡y neSet-isSet P
      ys≡[] = fst (PathPΣ (snd (PathPΣ mmh)))
      jaa = subst (λ a → (z ∷ zs) ⊆L (y ∷ a)) ys≡[] Q
      ooh = ys⊆[x] fs jaa
      Z≡Y : (z , zs , fs) ≡ (y , ys , es)
      Z≡Y = toneSet≡ _ _ (Listη (cons-inj₁ ooh) (cons-inj₂ ooh ∙ sym ys≡[]))


    Λclosed {x} {x'} {x'' ∷ xs} (d , ds) {y} {[]} es P Z Q = subst (_∈ Λfaces x x' (x'' ∷ xs) (d , ds)) (sym (toneSet≡ _ _ (ys⊆[x] (snd (snd Z)) Q))) P


    Λclosed {x} {x'} {x'' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P (z , [] , fs) Q with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl R = absurd (¬cons≡nil (fst (PathPΣ (snd (PathPΣ (x∈[y]→x≡y neSet-isSet R))))))
    ... | inr R with dec++ discreteneSet _ (ssubsets x' (x'' ∷ xs) ds) (insertSsubsets x (d , ds)) R
    ... | inl S = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , [] , tt*) _ _
                          (ssubsets-comp ds tt*
                            (⊆⊂-trans (z , [] , tt*) (y , y' ∷ ys , e , es) (x' , x'' ∷ xs , ds)
                              Q
                              (ssubsets-corr ds (e , es) S))))
    ... | inr S with split⊆ (e , es) fs Q
    ... | inl p = here (toneSet≡ _ _ (Listη (sym p ∙ insertList-head (x⊏ssubsets x (d , ds)) (e , es) S) refl))
    ... | inr p = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , [] , tt*) _ _
                          (ssubsets-comp ds tt*
                            (⊆⊂-trans (z , [] , tt*) (y' , ys , es) (x' , x'' ∷ xs , ds)
                              (⊏-step (e , es) tt* Q (⊏→≢ p))
                              (ssubsets-corr ds es ((insertList-tail (x⊏ssubsets x (d , ds)) (e , es) S))))))


    Λclosed {x} {x'} {x'' ∷ xs} (d , ds) {y} {y' ∷ ys} (e , es) P (z , z' ∷ zs , fs) Q with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl R = absurd (¬cons≡nil (fst (PathPΣ (snd (PathPΣ (x∈[y]→x≡y neSet-isSet R))))))
    ... | inr R with dec++ discreteneSet _ (ssubsets x' (x'' ∷ xs) ds) (insertSsubsets x (d , ds)) R
    ... | inl S = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , z' ∷ zs , fs) _ _
                        (ssubsets-comp ds fs
                          (⊆⊂-trans (z , z' ∷ zs , fs) (y , y' ∷ ys , e , es) (x' , x'' ∷ xs , ds) Q
                          (ssubsets-corr ds (e , es) S))))
    ... | inr S with split⊆ (e , es) fs Q
    ... | inl p = there (x∈xs→x∈ys++xs _ _ (ssubsets x' (x'' ∷ xs) ds) goal)
      where
      mmh = (insertList-tail (x⊏ssubsets x (d , ds)) (e , es) S)
      ooh = ssubsets-corr ds (es) mmh
      aah = (insertList-head (x⊏ssubsets x (d , ds)) (e , es) S)
      arg :  (z' , zs , snd fs) ⊆ (y' , ys , es)
      arg = ⊆-skip (e , es) fs Q p
      transs = ⊆⊂-trans (z' , zs , snd fs) (y' , ys , es) (x' , x'' ∷ xs , ds) arg ooh
      comput = ssubsets-comp (ds) (snd fs) transs
      almost = insertList-corr (x⊏ssubsets x (d , ds)) (z' , zs , snd fs) (subst (_⊏ z') (sym p ∙ aah) (fst fs)) comput
      goal = subst (_∈ insertList x (ssubsets x' (x'' ∷ xs) ds) (x⊏ssubsets x (d , ds))) (ΣPathP ((sym aah ∙ p) , (ΣPathP (refl , toPathP (ordered-isProp _ _))))) almost

    ... | inr p = there (x∈xs→x∈xs++ys {Adec = discreteneSet} (z , z' ∷ zs , fs) _ _
                          (ssubsets-comp ds fs
                            (⊆⊂-trans (z , z' ∷ zs , fs) (y' , ys , es) (x' , x'' ∷ xs , ds)
                              (⊏-step (e , es) fs Q (⊏→≢ p))
                              (ssubsets-corr ds es ((insertList-tail (x⊏ssubsets x (d , ds)) (e , es) S))))))


    Λadjoin-where : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ Λfaces x x' xs (ds)
      → ¬Type (x ∈ (y ∷ ys))
      → (y , ys , es) ∈ ssubsets x' xs (snd ds)
    Λadjoin-where {x} {x'} {xs} (d , ds) {y} {ys} es P ¬p with dec++ discreteneSet _ [ singleton x ] _ P
    ... | inl Q = absurd (¬p (here (sym (fst (PathPΣ (x∈[y]→x≡y neSet-isSet Q))))))
    ... | inr Q with dec++ discreteneSet _ (ssubsets x' xs ds) (insertSsubsets x (d , ds)) Q
    ... | inr R = absurd (¬p (here (sym (insertList-head (x⊏ssubsets x (d , ds)) es R))))
    ... | inl R = R

    Λadjoin : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (y , ys , es) ∈ Λfaces x x' xs (ds)
      → ¬Type (x ∈ (y ∷ ys)) → x ⊏ y
    Λadjoin {x} {x'} {xs} (d , ds) {y} {ys} es P ¬p with split⊆ ds es (fst (ssubsets-corr ds es (Λadjoin-where (d , ds) es P ¬p)))
    ... | inl p = subst (x ⊏_) p d
    ... | inr p = ⊏-trans x x' y d p


    Λadjoin-corr : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
      → {y : carrier} {ys : List carrier} (es : ordered (y ∷ ys))
      → (P : (y , ys , es) ∈ Λfaces x x' xs ds)
      → (¬p : ¬Type (x ∈ (y ∷ ys)))
      → insert x (y , ys , es) (Λadjoin ds es P ¬p) ∈ Λfaces x x' xs ds
    Λadjoin-corr {x} {x'} {xs} (d , ds) {y} {ys} es P ¬p = there (x∈xs→x∈ys++xs _
      (insertSsubsets x (d , ds)) (ssubsets x' xs ds)
       (insertList-corr (x⊏ssubsets x (d , ds)) (y , ys , es) (Λadjoin (d , ds) es P ¬p) (Λadjoin-where (d , ds) es P ¬p)))













  subsets : neSet → List neSet
  subsets (x , xs , ds) = WithoutΣ.subsets x xs ds

  module _ {X Y : neSet} where
\end{code}
\newcommand{\subsetsCor}{%
\begin{code}
    subsets-corr : Y ∈ subsets X → Y ⊆ X
    subsets-comp : Y ⊆ X → Y ∈ subsets X
\end{code}}
\begin{code}[hide]

    subsets-corr P = WithoutΣ.subsets-corr (snd (snd X)) (snd (snd Y)) P
    subsets-comp P = WithoutΣ.subsets-comp (snd (snd X)) (snd (snd Y)) P

  ssubsets : neSet → List neSet
  ssubsets (x , xs , ds) = WithoutΣ.ssubsets x xs ds

  ssubsets-corr : {X Y : neSet} → Y ∈ ssubsets X → Y ⊂ X
  ssubsets-corr {x , xs , ds} {y , ys , es} P = WithoutΣ.ssubsets-corr ds es P

  ssubsets-comp : {X Y : neSet} → Y ⊂ X → Y ∈ ssubsets X
  ssubsets-comp {x , xs , ds} {y , ys , es} P = WithoutΣ.ssubsets-comp ds es P

  Λfaces = WithoutΣ.Λfaces

  Λclosed : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
    → Λfaces x x' xs ds closedUnder _⊆_
  Λclosed {x} {x'} {xs} (d , ds) (y , ys , es) = WithoutΣ.Λclosed (d , ds) es

  Λadjoin : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
    → ((y , ys , es) : neSet)
    → (y , ys , es) ∈ Λfaces x x' xs (ds)
    → ¬Type (x ∈ (y ∷ ys)) → x ⊏ y
  Λadjoin ds (y , ys , es) = WithoutΣ.Λadjoin ds es

  Λadjoin-corr : {x : carrier} {x' : carrier} {xs : List carrier} (ds : ordered (x ∷ x' ∷ xs))
    → ((y , ys , es) : neSet)
    → (P : (y , ys , es) ∈ Λfaces x x' xs (ds))
    → (¬p : ¬Type (x ∈ (y ∷ ys)))
    → insert x (y , ys , es) (Λadjoin ds (y , ys , es) P ¬p) ∈ Λfaces x x' xs ds
  Λadjoin-corr ds (y , ys , es) = WithoutΣ.Λadjoin-corr ds es




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


module ℕSet where
  _>_ : Rel ℕ ℕ ℓ-zero
  m > n = (n < m)

  ℕlSet = lset ℕ discreteℕ _>_ (λ m n → m≤n-isProp) (λ x → ¬m<m) (λ m n o p q → <-trans q p)

  open neSet ℕlSet public

\end{code}

\newcommand{\simplicialcomplex}{%
\begin{AgdaAlign}\begin{AgdaSuppressSpace}
\begin{code}
record SimplicialComplex : Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁)) where
  constructor simpcomp
  field
    lcarrier : lSet {ℓ₀} {ℓ₁}
\end{code}
\begin{code}[hide]
  open neSet lcarrier
  field
\end{code}
\begin{code}
    faces : List neSet
    faces-closed : (X : neSet) → X ∈ faces → (Y : neSet) → Y ⊆ X → Y ∈ faces
  face : Type (ℓ-max ℓ₀ ℓ₁)
  face = Σ[ X ∈ neSet ] X ∈ faces
\end{code}
\end{AgdaSuppressSpace}\end{AgdaAlign}
}

\begin{code}[hide]

  getList : face → List carrier
  getList X = toList (fst X)

  _isVertex?_ : (x : carrier) → (X : face) → Dec (x ∈ getList X)
  _isVertex?_ x X = _∈?_ {Adec = dec} x (getList X)

  face-isSet : isSet face
  face-isSet = isSetΣ (isSetΣ carrier-isSet (λ x → isSetΣ (isOfHLevelList 0
    carrier-isSet) (λ xs → isOfHLevelSuc 1 ordered-isProp))) (λ x → isProp→isSet trunc)

  decFace : Discrete face
  decFace = discreteΣ discreteneSet (λ a p q → yes (trunc p q))

  dim : face → ℕ
  dim X = length (getList X)

  _≽_ : Rel face face ℓ₀
  X ≽ Y = fst Y ⊆ fst X


  ≽-Poset : Poset _ _
  ≽-Poset = face , (posetstr _≽_ (isposet face-isSet
    (λ X Y → is-prop-valued (fst Y) (fst X))
    (λ X → is-refl (fst X))
    (λ X Y Z p q → is-trans (fst Z) (fst Y) (fst X) q p)
    λ X Y p q → ΣPathP ((is-antisym (fst X) (fst Y) q p) ,
      (toPathP ((trunc (transport (λ i → is-antisym (fst X) (fst Y) q p i ∈ faces) (snd X)) (snd Y)))))))
    where open IsPoset ⊆-IsPoset

  _≻_ : Rel face face _
  X ≻ Y = fst Y ⊂ fst X -- (X ≽ Y) × (dim Y < dim X)

  ≻-LSet : lSet
  ≻-LSet = lset face decFace _≻_
    (λ X Y → ⊂LSet.⊏-prop (fst Y) (fst X))
    (λ X → ⊂LSet.⊏-irreflexive (fst X))
    λ X Y Z p q → ⊂LSet.⊏-trans (fst Z) (fst Y) (fst X) q p
    where
    module ⊂LSet = lSet ⊂LSet

  ≽→≻ : (X Y : face) → X ≽ Y → ¬Type (X ≡  Y) → X ≻ Y
  ≽→≻ X Y P ¬Q = P , (⊆→⊂ (fst Y) (fst X) P (λ x → ¬Q (ΣPathP ((toneSet≡ _ _ x) , (toPathP (trunc _ _))))))

  ≽≻-trans : (X Y Z : face) → X ≽ Y → Y ≻ Z → X ≻ Z
  ≽≻-trans X Y Z P Q = ⊂⊆-trans (fst Z) (fst Y) (fst X) Q P

  ≻≽-trans : (X Y Z : face) → X ≻ Y → Y ≽ Z → X ≻ Z
  ≻≽-trans X Y Z P Q = ⊆⊂-trans (fst Z) (fst Y) (fst X) Q P

  ≽→≡⊎≻ : {X Y : face} → X ≽ Y → (X ≡ Y) ⊎ (X ≻ Y)
  ≽→≡⊎≻ {X} {Y} P with ⊆→≡⊎⊂ (fst Y) (fst X) P
  ... | inl p = inl (ΣPathP (sym p , toPathP (trunc _ _)))
  ... | inr q = inr q



module _ where
  open ℕSet

  ℕSC : (faces : List neSet) → faces closedUnder _⊆_
    → SimplicialComplex
  ℕSC = simpcomp ℕlSet

\end{code}






\newcommand{\pCategory}{%
\begin{code}
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
\end{code}}
\begin{code}[hide]
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


module EntPath (K : SimplicialComplex {ℓ₀} {ℓ₀}) where
  open SimplicialComplex K
  open Seq ≻-LSet

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
  open SimplicialComplex K
  open Seq ≻-LSet

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

\end{code}
\newcommand{\sset}{%
\begin{code}
record ΔSet² {ℓ} : Type (ℓ-suc ℓ) where
  constructor simp
  field
    C⁰ : Type ℓ
    C¹ : C⁰ → C⁰ → Type ℓ
    C² : {x y z : C⁰} → C¹ x y → C¹ y z → C¹ x z → Type ℓ
\end{code}}

\begin{code}[hide]
  [C¹] : Type ℓ
  [C¹] = (Σ[ x ∈ C⁰ ] (Σ[ y ∈ C⁰ ] ( C¹ x y )))

  [C²] : Type ℓ
  [C²] = (Σ[ x ∈ ( C⁰ ) ] Σ[ y ∈ ( C⁰ ) ] Σ[ z ∈ ( C⁰ ) ]
               Σ[ f ∈ ( C¹ x y ) ] Σ[ g ∈ ( C¹ y z ) ] Σ[ h ∈ ( C¹ x z ) ]
                ( (C² f g h) ))

record ΔMap {ℓ} (X Y : ΔSet² {ℓ}) : Type ℓ where
  constructor smap

  module X = ΔSet² X
  module Y = ΔSet² Y

  field
    smap₀ : ( X.C⁰ ) → ( Y.C⁰ )
    smap₁ : {x y : ( X.C⁰ )} → ( X.C¹ x y ) → ( Y.C¹ (smap₀ x) (smap₀ y) )
    smap₂ : {x y z : ( X.C⁰ )} → {f : ( X.C¹ x y )} → {g : ( X.C¹ y z )} → {h : ( X.C¹ x z )}
      → ( X.C² f g h ) → ( Y.C² (smap₁ f) (smap₁ g) (smap₁ h) )

  [smap₁] : {x y : ( X.C⁰ )} → ( X.C¹ x y ) → ( Y.[C¹] )
  [smap₁] {x} {y} k = smap₀ x , smap₀ y , smap₁ k

  [smap₂] : {x y z : ( X.C⁰ )} → {f : ( X.C¹ x y )} → {g : ( X.C¹ y z )}
    → {h : ( X.C¹ x z )} → ( X.C² f g h ) → ( Y.[C²] )
  [smap₂] {x} {y} {z} {f} {g} {h} ϕ = smap₀ x , smap₀ y , smap₀ z ,
    smap₁ f , smap₁ g , smap₁ h , smap₂ ϕ


Nerve : ∀{ℓ} → (pCategory {ℓ}) → ΔSet² {ℓ}
Nerve C = simp ( ob ) (λ x y → ∣ hom x y ∣ₚ)
  λ {x} {y} {z} f g h → h ≤[ hom x z ] (g ∘ f)
  where open pCategory C


Nerve₁ : ∀{ℓ} {C D : pCategory {ℓ}} → pFunctor C D → ΔMap (Nerve C) (Nerve D)
Nerve₁ {ℓ} {C} {D} F = smap fmap₀ fmap₁ map₂
  where
  private
    module C = pCategory C
    module D = pCategory D
    module ΔC = ΔSet² (Nerve C)
    module ΔD = ΔSet² (Nerve D)
  open pFunctor F
  map₂ : {x y z : ΔC.C⁰} {f : ΔC.C¹ x y} {g : ΔC.C¹ y z} {h : ΔC.C¹ x z}
    → ( ΔC.C² f g h ) → ( ΔD.C² (fmap₁ f) (fmap₁ g) (fmap₁ h) )
  map₂ {x} {y} {z} {f} {g} {h} p =
    fmap₁ h ≤⟨ fmap₁-mono h (g C.∘ f) p ⟩
    fmap₁ (g C.∘ f) ≤⟨ comp-law f g ⟩
    fmap₁ g D.∘ fmap₁ f ◾
    where open PosetReasoning (D.hom (fmap₀ x) (fmap₀ z))



module _ where
  open ΔSet²
\end{code}


\newcommand{\sreal}{%
\begin{code}
  data ∣_∣ˢ (X : ΔSet² {ℓ}) : Type ℓ where
    vert : C⁰ X → ∣ X ∣ˢ
    edge : {x y : C⁰ X} → C¹ X x y → vert x ≡ vert y
    triangle : {x y z : C⁰ X} {f : C¹ X x y} {g : C¹ X y z} {h : C¹ X x z} (ϕ : C² X f g h)
      → Square (edge f) refl (edge h) (edge g)
    trunc : isGroupoid ∣ X ∣ˢ
\end{code}}

\begin{code}[hide]
module Δ∣_∣elim {X : ΔSet² {ℓ₀}} {P : ∣ X ∣ˢ → Type ℓ₁} (Pgpd : ∀ a → isGroupoid (P a))
              (vert* : (a : ( ΔSet².C⁰ X )) → P (vert a))
              (edge* : {a b : ( ΔSet².C⁰ X )} (f : ( ΔSet².C¹ X a b )) → PathP (λ i → P (edge f i)) (vert* a) (vert* b))
              (triangle* : {a b c : ( ΔSet².C⁰ X )} {f : ( ΔSet².C¹ X a b )} {g : ( ΔSet².C¹ X b c )}
                         {h : ( ΔSet².C¹ X a c )} (ϕ : ( ΔSet².C² X f g h ))
                         → SquareP (λ i j → P (triangle ϕ i j)) (edge* f) (λ j → vert* c) (edge* h) (edge* g))
                          where
  fun : (a : ∣ X ∣ˢ) → P a
  fun (vert x) = vert* x
  fun (edge f i) = edge* f i
  fun (triangle ϕ i j) = triangle* ϕ i j
  fun (trunc x y p q α β i j k) = isOfHLevel→isOfHLevelDep 3 Pgpd
                                   (fun x) (fun y)
                                   (cong fun p) (cong fun q)
                                   (cong (cong fun) α) (cong (cong fun) β)
                                   (trunc x y p q α β) i j k



Δ∣_∣₁ : {X Y : ΔSet² {ℓ₀}} → ΔMap X Y → ∣ X ∣ˢ → ∣ Y ∣ˢ
Δ∣_∣₁ {X} {Y} F = Δ∣_∣elim.fun
  (λ a → trunc)
  (λ x → vert (smap₀ x))
  (λ f i → edge (smap₁ f) i)
  (λ ϕ i j → triangle (smap₂ ϕ) i j)
  where open ΔMap F


module _ {X : ΔSet² {ℓ₀}} where
  open ΔSet² X
  ◤ : {x y z : C⁰} {f : C¹ x y} {g : C¹ y z}
     {h : C¹ x z} (ϕ : C² f g h)
      → Square refl (edge {ℓ₀} {X} g) (edge f) (edge h)
  ◤ ϕ = slideSquare (flipSquare (triangle ϕ))

  module _ {w x y z : C⁰} {f : C¹ w x} {g : C¹ w y} {f' : C¹ x z}
    {g' : C¹ y z} where
\end{code}


\newcommand{\doubleTriangle}{%
\begin{code}
    doubleTriangle : (h : C¹ w z) → (C² f f' h) → (C² g g' h)
      → Square (edge f) (edge g') (edge g) (edge f')
    doubleTriangle h ϕ ψ i j = hcomp (λ k → λ {
            (i = i0) → edge f j
          ; (i = i1) → edge g' (j ∨ (~ k))
          ; (j = i0) → ◤ ψ i (~ k)
          ; (j = i1) → edge f' i
          }) (triangle ϕ i j)
\end{code}}

\begin{code}[hide]


\end{code}


\newcommand{\classifyingType}{%
\begin{code}
𝓑 : pCategory → Type ℓ
𝓑 C = ∣ Nerve C ∣ˢ
\end{code}}



\newcommand{\classifyingTypeF}{%
\begin{code}
𝓑₁ : {C D : pCategory {ℓ}} → pFunctor C D → 𝓑 C → 𝓑 D
𝓑₁ F = Δ∣ Nerve₁ F ∣₁
\end{code}}



\begin{code}[hide]
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
\end{code}


\newcommand{\catHomotopy}{%
\begin{code}
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
\end{code}}

\begin{code}[hide]
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
\end{code}

\newcommand{\catEquiv}{%
\begin{code}
  CatEquiv→HomEquiv : CatEquiv C D → 𝓑 C ≡ 𝓑 D
  CatEquiv→HomEquiv (cateq F G η ν) = isoToPath (iso (𝓑₁ F) (𝓑₁ G) ι ρ) where
    ι : (x : 𝓑 D) → 𝓑₁ F (𝓑₁ G x) ≡ x
    ι x = 𝓑₁-comp G F x ∙ sym (pNatTrans→Homotopy (pId D) (F ∘₁ G) η x) ∙ 𝓑₁-id {C = D} x
    ρ : (x : 𝓑 C) → 𝓑₁ G (𝓑₁ F x) ≡ x
    ρ x = 𝓑₁-comp F G x ∙ (pNatTrans→Homotopy (G ∘₁ F) (pId C) ν x) ∙ 𝓑₁-id {C = C} x
\end{code}}

\begin{code}[hide]




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


\end{code}






\begin{code}[hide]



module _ where
  open FacePoset
  open EntPath

\end{code}
\newcommand{\entEquivFacePoset}{%
\begin{code}
  Ent≡FacePoset : (K : SimplicialComplex {ℓ₀} {ℓ₀}) → 𝓑 (Ent K) ≡ 𝓑 (FacePoset K)
  Ent≡FacePoset K = CatEquiv→HomEquiv (FacePoset≃Ent K)
\end{code}}
\begin{code}[hide]

module _ where
  open ℕSet

  _-to-0 : (n : ℕ) → neSet
  lemma : (n : ℕ) → fst (n -to-0) ≡ n

  zero -to-0 = singleton 0
  suc n -to-0 = let r = n -to-0 in suc n , toList r , (0 , (cong suc (lemma n))) , snd (snd r)

  lemma zero = refl
  lemma (suc n) = refl

  module ⊆Pos = IsPoset ⊆-IsPoset

\end{code}
\newcommand{\standardComp}{%
\begin{code}
  Δ : ℕ → SimplicialComplex
  Δ n = ℕSC (subsets (n -to-0)) closed where
    closed : subsets (n -to-0) closedUnder _⊆_
    closed X P Y Q = subsets-comp (⊆Pos.is-trans Y X (n -to-0) Q (subsets-corr P))
\end{code}}
\begin{code}[hide]

  module ΔFaces (n : ℕ) where
    open SimplicialComplex (Δ n)
    open FacePoset
    open EntPath

    topcell : Initial (FacePoset (Δ n))
    fst topcell = n -to-0 , subsets-comp (⊆Pos.is-refl (n -to-0))
    snd topcell Y = (subsets-corr (snd Y)) , (λ y → tt*)

    Δn-isContr : isContr (𝓑 (Ent (Δ n)))
    Δn-isContr = subst isContr (sym (Ent≡FacePoset (Δ n))) (Initial-IsContr (FacePoset (Δ n)) topcell)




\end{code}
\newcommand{\boundaryComp}{%
\begin{code}
  ∂ : ℕ → SimplicialComplex
  ∂ n = ℕSC (ssubsets (n -to-0)) closed where
    closed : ssubsets (n -to-0) closedUnder _⊆_
    closed X P Y Q = ssubsets-comp (⊆⊂-trans Y X (n -to-0) Q (ssubsets-corr P))
\end{code}}
\begin{code}[hide]



  sucn-ordered : {(1+ n) : ℕ₊₁} → ordered (suc n ∷ fst (n -to-0) ∷ fst (snd (n -to-0)))
  sucn-ordered {1+ n} = ((0 , cong suc (lemma n)) , snd (snd (n -to-0)))

  Λ : ((1+ n) : ℕ₊₁) → SimplicialComplex
  Λ (1+ n) = ℕSC (Λfaces (suc n) (fst r) (fst (snd r)) sucn-ordered)
    (Λclosed sucn-ordered)
    where
    r = (n)-to-0

  module ΛFaces ((1+ n) : ℕ₊₁) where
    open SimplicialComplex (Λ (1+ n))
    center : face
    center = singleton (suc n) , here refl


\end{code}
\newcommand{\adjoin}{%
\begin{code}
    adjoin : (X : face) → Σ[ X' ∈ face ] (X' ≽ X) × (X' ≽ center)
\end{code}}
\begin{code}[hide]
    fst (adjoin X) = withHelper (suc n isVertex? X)
      where
      withHelper : Dec (suc n ∈ getList X) → face
      withHelper (yes p) = X
      withHelper (no ¬p) = (insert (suc n) (fst X) (Λadjoin sucn-ordered (fst X) (snd X) ¬p)) , Λadjoin-corr sucn-ordered (fst X) (snd X) ¬p
    snd (adjoin X) with (suc n) isVertex? X
    ...| yes p = IsPoset.is-refl (pstr ≽-Poset) X , λ x x₁ → subst (λ a → Any (PathP (λ i → ℕ) a) (fst (fst X) ∷ fst (snd (fst X)))) (sym (x∈[y]→x≡y isSetℕ x₁)) p
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
\end{code}
\newcommand{\adjoinPaths}{%
\begin{code}
      adjoinX≡X : (X : face) → vert (fst (adjoin X)) ≡ vert X
      adjoinX≡center : (X : face) → vert (fst (adjoin X)) ≡ vert center
\end{code}}
\begin{code}[hide]
      adjoinX≡X X = edge (fst (snd (adjoin X)))
      adjoinX≡center X = edge (snd (snd (adjoin X)))
\end{code}
\newcommand{\con}{%
\begin{code}
      con : (X : face) → vert center ≡ vert X
      con X = sym (adjoinX≡center X) ∙ adjoinX≡X X
\end{code}}
\begin{code}[hide]
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

\end{code}
\newcommand{\hornContr}{%
\begin{code}
    EntΛn-isContr : isContr (𝓑 (Ent (Λ (1+ n))))
    EntΛn-isContr = subst isContr (sym (Ent≡FacePoset (Λ (1+ n)))) FacePosetΛn-isContr
\end{code}}
\begin{code}[hide]


-- ∧

\end{code}

