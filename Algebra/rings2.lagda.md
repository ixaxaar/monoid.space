****
[Contents](contents.html)
[Previous](Algebra.rings.html)
[Next](Algebra.fields.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Rings Continued...](#rings-continued)
  - [Near-Semiring](#near-semiring)
  - [Semiring](#semiring)
  - [Commutative Semiring](#commutative-semiring)
  - [Ring](#ring)
  - [Commutative Ring](#commutative-ring)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Rings Continued...

We now define objects of the ring family, as we did for groups.

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.equality

open import Algebra.groups
open import Algebra.groups2
open import Algebra.rings

module Algebra.rings2 where
```

## Near-Semiring

```agda
record NearSemiring c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data           : Set c
    _≈_            : Rel Data ℓ
    _+_            : ★ Data
    _*_            : ★ Data
    0#             : Data
    isNearSemiring : IsNearSemiring _≈_ _+_ _*_ 0#

  open IsNearSemiring isNearSemiring public

  +-monoid : Monoid _ _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
    using ()
    renaming
    ( magma     to +-magma
    ; semigroup to +-semigroup
    )

  *-semigroup : Semigroup _ _
  *-semigroup = record { isSemigroup = *-isSemigroup }

  open Semigroup *-semigroup public
    using ()
    renaming ( magma    to *-magma )
```

## Semiring

```agda
record SemiringWithoutOne c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data                 : Set c
    _≈_                  : Rel Data ℓ
    _+_                  : ★ Data
    _*_                  : ★ Data
    0#                   : Data
    isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsSemiringWithoutOne isSemiringWithoutOne public

  nearSemiring : NearSemiring _ _
  nearSemiring = record { isNearSemiring = isNearSemiring }

  open NearSemiring nearSemiring public
    using
    ( +-magma; +-semigroup; +-monoid
    ; *-magma; *-semigroup
    )

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }


record SemiringWithoutAnnihilatingZero c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data       : Set c
    _≈_        : Rel Data ℓ
    _+_        : ★ Data
    _*_        : ★ Data
    0#         : Data
    1#         : Data
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1#

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
    using ()
    renaming
    ( magma     to +-magma
    ; semigroup to +-semigroup
    ; monoid    to +-monoid
    )

  *-monoid : Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
    using ()
    renaming
    ( magma     to *-magma
    ; semigroup to *-semigroup
    )
```

```agda
record Semiring c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data       : Set c
    _≈_        : Rel Data ℓ
    _+_        : ★ Data
    _*_        : ★ Data
    0#         : Data
    1#         : Data
    isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#

  open IsSemiring isSemiring public

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    }

  open SemiringWithoutAnnihilatingZero
         semiringWithoutAnnihilatingZero public
    using
    ( +-magma;  +-semigroup
    ; *-magma;  *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; *-monoid
    )

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
    using (nearSemiring)
```

## Commutative Semiring

```agda
record CommutativeSemiringWithoutOne c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data                            : Set c
    _≈_                             : Rel Data ℓ
    _+_                             : ★ Data
    _*_                             : ★ Data
    0#                              : Data
    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsCommutativeSemiringWithoutOne
         isCommutativeSemiringWithoutOne public

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
    using
    ( +-magma; +-semigroup
    ; *-magma; *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; nearSemiring
    )


record CommutativeSemiring c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data                  : Set c
    _≈_                   : Rel Data ℓ
    _+_                   : ★ Data
    _*_                   : ★ Data
    0#                    : Data
    1#                    : Data
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#

  open IsCommutativeSemiring isCommutativeSemiring public

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( +-magma; +-semigroup
    ; *-magma; *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    )

  *-commutativeMonoid : CommutativeMonoid _ _
  *-commutativeMonoid =
    record { isCommutativeMonoid = *-isCommutativeMonoid }

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
  commutativeSemiringWithoutOne = record
    { isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }
```

## Ring

```agda
record Ring c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data    : Set c
    _≈_     : Rel Data ℓ
    _+_     : ★ Data
    _*_     : ★ Data
    -_      : ♠ Data
    0#      : Data
    1#      : Data
    isRing  : IsRing _≈_ _+_ _*_ -_ 0# 1#

  open IsRing isRing public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
    using
    ( +-magma; +-semigroup
    ; *-magma; *-semigroup
    ; +-monoid ; +-commutativeMonoid
    ; *-monoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero
    )

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group)
```

## Commutative Ring

```agda
record CommutativeRing c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Data              : Set c
    _≈_               : Rel Data ℓ
    _+_               : ★ Data
    _*_               : ★ Data
    -_                : ♠ Data
    0#                : Data
    1#                : Data
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  ring : Ring _ _
  ring = record { isRing = isRing }

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open Ring ring public using (+-group; +-abelianGroup)
  open CommutativeSemiring commutativeSemiring public
    using
    ( +-magma; +-semigroup
    ; *-magma; *-semigroup
    ; +-monoid; +-commutativeMonoid
    ; *-monoid; *-commutativeMonoid
    ; nearSemiring; semiringWithoutOne
    ; semiringWithoutAnnihilatingZero; semiring
    ; commutativeSemiringWithoutOne
    )
```

****
[Fields](./Algebra.fields.html)
