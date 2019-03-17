<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Groups and family 2](#groups-and-family-2)
  - [Magma](#magma)
  - [Semigroupoid](#semigroupoid)
  - [Small category](#small-category)
  - [Semigroup](#semigroup)
  - [Groupoid](#groupoid)
    - [Monoid](#monoid)
  - [Commutative Monoid](#commutative-monoid)
  - [Group](#group)
  - [Abelian Group](#abelian-group)
  - [Lattice](#lattice)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Groups and family 2

Here we define the objects based on the conditions defined in the previous section.

```agda
module Algebra.structures where

open import Types.equality using (Rel)
-- open import Types.functions
-- open import Types.typeBasics

open import Level using (suc; _⊔_)

open import Algebra.groups
```

We recall operations again here:

```agda
★_ : ∀ {a} → Set a → Set a
★ A = A → A → A

♠_ : ∀ {a} → Set a → Set a
♠ A = A → A
```

## Magma

```agda
record Magma a ℓ : Set (suc (a ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data      : Set a
    _==_       : Rel Data ℓ
    _∙_       : ★ Data
    isMagma   : IsMagma _==_ _∙_

  open IsMagma isMagma public
```

## Semigroupoid

```agda
record Semigroupoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data            : Set c
    _==_            : Rel Data ℓ
    _∙_             : ★ Data
    isSemigroupoid  : IsSemigroupoid _==_ _∙_

  open IsSemigroupoid isSemigroupoid public
```

## Small category

```agda
record SmallCategory c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data            : Set c
    _==_            : Rel Data ℓ
    _∙_             : ★ Data
    ε               : Data
    isSmallCategory : IsSmallCategory _==_ _∙_ ε

  open IsSmallCategory isSmallCategory public

  semigroupoid : Semigroupoid c ℓ
  semigroupoid = record { isSemigroupoid = isSemigroupoid }
```

## Semigroup

```agda
record Semigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data        : Set c
    _==_        : Rel Data ℓ
    _∙_         : ★ Data
    isSemigroup : IsSemigroup _==_ _∙_

  open IsSemigroup isSemigroup public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }
```

## Groupoid

```agda
record Groupoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data            : Set c
    _==_            : Rel Data ℓ
    _∙_             : ★ Data
    ε               : Data
    x⁻¹             : ♠ Data
    isGroupoid      : IsGroupoid _==_ _∙_ ε x⁻¹

  open IsGroupoid isGroupoid public

  smallcategory : SmallCategory c ℓ
  smallcategory = record { isSmallCategory = isSmallCategory }

  semigroupoid : Semigroupoid c ℓ
  semigroupoid = record { isSemigroupoid = isSemigroupoid }
```

### Monoid

```agda
record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data     : Set c
    _==_      : Rel Data ℓ
    _∙_      : ★ Data
    ε        : Data
    isMonoid : IsMonoid _==_ _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }
```

## Commutative Monoid

```agda
record CommutativeMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data                : Set c
    _==_                 : Rel Data ℓ
    _∙_                 : ★ Data
    ε                   : Data
    isCommutativeMonoid : IsCommutativeMonoid _==_ _∙_ ε

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid c ℓ
  monoid = record { isMonoid = isMonoid }

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }
```

## Group

```agda
record Group c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 x⁻¹
  infixl 7 _∙_
  infix  4 _==_
  field
    Data    : Set c
    _==_    : Rel Data ℓ
    _∙_     : ★ Data
    ε       : Data
    x⁻¹     : ♠ Data
    isGroup : IsGroup _==_ _∙_ ε x⁻¹

  open IsGroup isGroup public

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }
```

## Abelian Group

```agda
open import Algebra.groups using (IsAbelianGroup)

record AbelianGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 x⁻¹
  infixl 7 _∙_
  infix  4 _==_
  field
    Data           : Set c
    _==_            : Rel Data ℓ
    _∙_            : ★ Data
    ε              : Data
    x⁻¹            : ♠ Data
    isAbelianGroup : IsAbelianGroup _==_ _∙_ ε x⁻¹

  open IsAbelianGroup isAbelianGroup public

  group : Group c ℓ
  group = record { isGroup = isGroup }

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  semigroup : Semigroup c ℓ
  semigroup = record { isSemigroup = isSemigroup }

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }
```

## Lattice

```lauda
open import Types.equality
open import Algebra.operations

record IsLattice {a ℓ} {A : Set a} {_==_ : Rel A ℓ} (∨ ∧ : ★ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _==_
    ∨-comm        : Commutative ∨
    ∨-assoc       : Associative ∨
    ∨-cong        : Congruent₂ ∨
    ∧-comm        : Commutative ∧
    ∧-assoc       : Associative ∧
    ∧-cong        : Congruent₂ ∧
    absorptive    : Absorptive ∨ ∧

  open IsEquivalence isEquivalence public

  ∨-absorbs-∧ : ∨ Absorbs ∧
  ∨-absorbs-∧ = fst absorptive

  ∧-absorbs-∨ : ∧ Absorbs ∨
  ∧-absorbs-∨ = snd absorptive

  ∧-congˡ : LeftCongruent ∧
  ∧-congˡ y==z = ∧-cong y==z refl

  ∧-congʳ : RightCongruent ∧
  ∧-congʳ y==z = ∧-cong refl y==z

  ∨-congˡ  : LeftCongruent ∨
  ∨-congˡ y==z = ∨-cong y==z refl

  ∨-congʳ : RightCongruent ∨
  ∨-congʳ y==z = ∨-cong refl y==z
```

****
[Back to Contents](./contents.html)
