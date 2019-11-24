****
[Contents](contents.html)
[Previous](Algebra.groups.html)
[Next](Algebra.morphisms.html)

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

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Groups and family 2

Here we define the objects based on the conditions defined in the previous section. It might be helpful here to think of `Data` fields as datatypes as used in computer sciences, and the objects as the structure defined on operations of that datatype. For e.g. if a datatype's equivalence (or equality evaluator) happens to be congruent, then the datatype and its equivalence relation form a "magma". Thus the object itself encodes the relationship of a datatype with an operation.

Such structures can often be applied in computer science in curious ways, such as using the monoidal functions (μ: T → T → T) for reduce operations (part of "map-reduce" in big data), progressively "reducing" a large quantity of `T`s into one final value of type `T`, e.g. addition of an enormous list of numbers. Monoids, Groups and Semigroups form the basis for an arguably large number of patterns especially in functional programming.

```agda
module Algebra.groups2 where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.equality using (Rel)
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
record Magma a ℓ : Set (lsuc (a ⊔ ℓ)) where
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
record Semigroupoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
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
record SmallCategory c ℓ : Set (lsuc (c ⊔ ℓ)) where
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

Semigroups can be used in functional programming to abstract over associative operations for non-trivial datatypes, such as "adding" two dictionatries or "multiplying" a character (repeating it n times), etc.

```agda
record Semigroup c ℓ : Set (lsuc (c ⊔ ℓ)) where
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
record Groupoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _==_
  field
    Data            : Set c
    _==_            : Rel Data ℓ
    _∙_             : ★ Data
    ε               : Data
    _⁻¹             : ♠ Data
    isGroupoid      : IsGroupoid _==_ _∙_ ε _⁻¹

  open IsGroupoid isGroupoid public

  smallcategory : SmallCategory c ℓ
  smallcategory = record { isSmallCategory = isSmallCategory }

  semigroupoid : Semigroupoid c ℓ
  semigroupoid = record { isSemigroupoid = isSemigroupoid }
```

## Monoid

```agda
record Monoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
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
record CommutativeMonoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
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
record Group c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _==_
  field
    Data    : Set c
    _==_    : Rel Data ℓ
    _∙_     : ★ Data
    ε       : Data
    _⁻¹     : ♠ Data
    isGroup : IsGroup _==_ _∙_ ε _⁻¹

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

record AbelianGroup c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _==_
  field
    Data           : Set c
    _==_            : Rel Data ℓ
    _∙_            : ★ Data
    ε              : Data
    _⁻¹            : ♠ Data
    isAbelianGroup : IsAbelianGroup _==_ _∙_ ε _⁻¹

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

****
[Group Morphisms](./Algebra.morphisms.html)
