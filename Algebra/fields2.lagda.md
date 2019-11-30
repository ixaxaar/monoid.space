****
[Contents](contents.html)
[Previous](Algebra.fields.html)
[Next](./Algebra.numbers.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Fields Continued...](#fields-continued)
  - [Fields](#fields)
  - [Ordered Fields](#ordered-fields)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Fields Continued...

We now define objects of the field family, as we did for groups and rings before.

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.equality

open import Algebra.order
open import Algebra.groups
open import Algebra.groups2
open import Algebra.rings
open import Algebra.rings2
open import Algebra.fields

module Algebra.fields2 where
```

## Fields

```agda
record Field c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix  9 ÷_
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data     : Set c
    _≈_      : Rel Data ℓ
    _+_      : ★ Data
    _*_      : ★ Data
    -_       : ♠ Data
    ÷_       : ♠ Data
    0#       : Data
    1#       : Data
    isField  : IsField _≈_ _+_ _*_ -_ ÷_ 0# 1#

  open IsField isField public

  ring : Ring _ _
  ring = record { isRing = isRing }

  open Ring ring public
    using
    ( +-magma; +-semigroup; +-abelianGroup
    ; *-magma; *-semigroup
    ; +-monoid ; +-commutativeMonoid
    ; *-monoid
    ; nearSemiring; semiringWithoutOne; semiring
    ; semiringWithoutAnnihilatingZero
    )
```

## Ordered Fields

```agda
record OrderedField c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix  9 ÷_
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data            : Set c
    _≈_             : Rel Data ℓ
    _≤_             : Rel Data ℓ
    _+_             : ★ Data
    _*_             : ★ Data
    -_              : ♠ Data
    ÷_              : ♠ Data
    0#              : Data
    1#              : Data
    isOrderedField  : IsOrderedField _≈_ _+_ _*_ -_ ÷_ _≤_ 0# 1#

  open IsOrderedField isOrderedField public

  ring : Ring _ _
  ring = record { isRing = isRing }

  open Ring ring public
    using
    ( +-magma; +-semigroup; +-abelianGroup
    ; *-magma; *-semigroup
    ; +-monoid ; +-commutativeMonoid
    ; *-monoid
    ; nearSemiring; semiringWithoutOne; semiring
    ; semiringWithoutAnnihilatingZero
    )
```

****
[Numbers](./Algebra.numbers.html)
