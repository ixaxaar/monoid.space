****
[Contents](contents.html)
[Previous](Algebra.groupProperties.html)
[Next](Algebra.rings2.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Rings](#rings)
  - [Near-Semiring](#near-semiring)
  - [Semiring](#semiring)
  - [Commutative Semiring](#commutative-semiring)
  - [Ring](#ring)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Rings

A ring is a structure containing:

- A set $𝕊$
- Two binary operations: + and −

where the structure defined on the operations are:

1. $𝕊$ is an abelian group under addition, which implies the operation +:
    - is associative
    - is commutative
    - has an inverse (−)
    - has an identity
2. $𝕊$ is a monoid under multiplication, which implies the operation ★:
    - is associative
    - has an identity
3. Multiplication is distributive over addition
4. There must be an annihilating element 𝕖 such that $∀ x : 𝕖 ★ x = 𝕖$

Examples of rings would be natural, real, complex and rational numbers. Any algebra over a ring is also a ring. Hence, any set of n × n matrices of real numbers also forms a ring. A set of real upper or lower triangular matrices would also form a ring. The family of rings starts from semirings and goes on with commutative semirings, rings and commutative rings.

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.equality

module Algebra.rings {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
  open import Types.operations (_==_)
  open import Algebra.groups (_==_)
```

The family of rings consist of a set and two binary operations. Each binary operation behaves in a certain way with the set, taking upon roles from the group family, e.g. one operation can behave like a monoid with respect to the set while the other one can behave like a group.

| Object ↓ Operation → |  `+` behaves as |  `*` behaves as |
| --- | --- | --- |
| Near-Semiring | Monoid | Semigroup |
| Semiring | Commutative Monoid | Monoid |
| Commutative Semiring | Commutative Monoid | Commutative Monoid |
| Ring | Abelian Group | Monoid |

The `*` operation interacts with the `+` operation by folowing the law of distributivity.

## Near-Semiring

We define a Near-Semiring as the most abstract structure in the family of rings. It is a structure containing:

- A set $𝕊$
- Two binary operations: + and *

where the structure defined on the operations are:

1. $𝕊$ is an monoid under addition, which implies the operation +:
    - is associative
    - has an identity
2. $𝕊$ is a semigroup under multiplication, which implies the operation *:
    - is associative
3. Multiplication is distributive over addition
4. There must be an annihilating element 𝕖 such that $∀ x : 𝕖 * x = 𝕖$

```agda
  record IsNearSemiring (+ * : ★ A) (0# : A) : Set (a ⊔ ℓ) where
    field
      +-isMonoid    : IsMonoid + 0#
      *-isSemigroup : IsSemigroup *
      distribʳ      : * DistributesOverʳ +
      zeroˡ         : LeftZero 0# *

    open IsMonoid +-isMonoid public
      renaming
      ( assoc       to +-assoc
      ; ∙-cong      to +-cong
      ; ∙-congˡ     to +-congˡ
      ; ∙-congʳ     to +-congʳ
      ; identity    to +-identity
      ; identityˡ   to +-identityˡ
      ; identityʳ   to +-identityʳ
      ; isMagma     to +-isMagma
      ; isSemigroup to +-isSemigroup
      )

    open IsSemigroup *-isSemigroup public
      using ()
      renaming
      ( assoc    to *-assoc
      ; ∙-cong   to *-cong
      ; ∙-congˡ  to *-congˡ
      ; ∙-congʳ  to *-congʳ
      ; isMagma  to *-isMagma
      )
```

## Semiring

A Semiring is a structure containing:

- A set $𝕊$
- Two binary operations: + and *

where the structure defined on the operations are:

1. $𝕊$ is an commutative monoid under addition, which implies the operation +:
    - is associative
    - is commutative
    - has an identity
2. $𝕊$ is a monoid under multiplication, which implies the operation *:
    - is associative
    - has an identity
3. Multiplication is distributive over addition
4. There must be an annihilating element 𝕖 such that $∀ x : 𝕖 * x = 𝕖$

These laws are the same as that of a ring, except for the requirement of addition to have an inverse operation. It is easier to first describe the semiring with the annihilation element:

```agda
  record IsSemiringWithoutOne (+ * : ★ A) (0# : A) : Set (a ⊔ ℓ) where
    field
      +-isCommutativeMonoid : IsCommutativeMonoid + 0#
      *-isSemigroup         : IsSemigroup *
      distrib               : * DistributesOver +
      zero                  : Zero 0# *

    open IsCommutativeMonoid +-isCommutativeMonoid public
      using ()
      renaming
      ( isMonoid    to +-isMonoid
      ; comm        to +-comm
      )

    zeroˡ : LeftZero 0# *
    zeroˡ = fst zero

    zeroʳ : RightZero 0# *
    zeroʳ = snd zero

    isNearSemiring : IsNearSemiring + * 0#
    isNearSemiring = record
      { +-isMonoid    = +-isMonoid
      ; *-isSemigroup = *-isSemigroup
      ; distribʳ      = snd distrib
      ; zeroˡ         = zeroˡ
      }

    open IsNearSemiring isNearSemiring public
      hiding (+-isMonoid; zeroˡ)


  record IsSemiringWithoutAnnihilatingZero
    (+ * : ★ A) (0# 1# : A) : Set (a ⊔ ℓ) where

    field
      -- 0# is the identity element of *
      -- 1# is the identity element of +
      +-isCommutativeMonoid : IsCommutativeMonoid + 0#
      *-isMonoid            : IsMonoid * 1#
      distrib               : * DistributesOver +

    open IsCommutativeMonoid +-isCommutativeMonoid public
      renaming
      ( assoc       to +-assoc
      ; ∙-cong      to +-cong
      ; ∙-congˡ     to +-congˡ
      ; ∙-congʳ     to +-congʳ
      ; identity    to +-identity
      ; identityˡ   to +-identityˡ
      ; identityʳ   to +-identityʳ
      ; comm        to +-comm
      ; isMagma     to +-isMagma
      ; isSemigroup to +-isSemigroup
      ; isMonoid    to +-isMonoid
      )

    open IsMonoid *-isMonoid public
      using ()
      renaming
      ( assoc       to *-assoc
      ; ∙-cong      to *-cong
      ; ∙-congˡ     to *-congˡ
      ; ∙-congʳ     to *-congʳ
      ; identity    to *-identity
      ; identityˡ   to *-identityˡ
      ; identityʳ   to *-identityʳ
      ; isMagma     to *-isMagma
      ; isSemigroup to *-isSemigroup
      )
```

And now the complete definition:

```agda
  record IsSemiring (+ * : ★ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      isSemiringWithoutAnnihilatingZero :
        IsSemiringWithoutAnnihilatingZero + * 0# 1#
      zero : Zero 0# *

    open IsSemiringWithoutAnnihilatingZero
           isSemiringWithoutAnnihilatingZero public

    isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
    isSemiringWithoutOne = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isSemigroup         = *-isSemigroup
      ; distrib               = distrib
      ; zero                  = zero
      }

    open IsSemiringWithoutOne isSemiringWithoutOne public
      using
      ( isNearSemiring
      ; zeroˡ
      ; zeroʳ
      )
```

We can add commutativity of multiplication to the above structures to obtain their commutative versions.

## Commutative Semiring

A Commutative Semiring is a structure containing:

- A set $𝕊$
- Two binary operations: + and *

where the structure defined on the operations are:

1. $𝕊$ is an commutative monoid under addition, which implies the operation +:
    - is associative
    - is commutative
    - has an identity
2. $𝕊$ is a commutative monoid under multiplication, which implies the operation *:
    - is associative
    - is commutative
    - has an identity
3. Multiplication is distributive over addition
4. There must be an annihilating element 𝕖 such that $∀ x : 𝕖 * x = 𝕖$


```agda
  record IsCommutativeSemiringWithoutOne
           (+ * : ★ A) (0# : A) : Set (a ⊔ ℓ) where
    field
      isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
      *-comm               : Commutative *

    open IsSemiringWithoutOne isSemiringWithoutOne public

  record IsCommutativeSemiring (+ * : ★ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      +-isCommutativeMonoid : IsCommutativeMonoid + 0#
      *-isCommutativeMonoid : IsCommutativeMonoid * 1#
      distrib               : * DistributesOver +
      zero                  : Zero 0# *

    private
      module +-CM = IsCommutativeMonoid +-isCommutativeMonoid
      open module *-CM = IsCommutativeMonoid *-isCommutativeMonoid public
             using () renaming (comm to *-comm)

    distribˡ : * DistributesOverˡ +
    distribˡ = fst distrib

    distribʳ : * DistributesOverʳ +
    distribʳ = snd distrib

    zeroʳ : RightZero 0# *
    zeroʳ = snd zero

    zeroˡ : RightZero 0# *
    zeroˡ = snd zero

    isSemiring : IsSemiring + * 0# 1#
    isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isMonoid            = *-CM.isMonoid
        ; distrib               = distrib
        }
      ; zero                    = zero
      }

    open IsSemiring isSemiring public
      hiding
      ( distrib; zero; zeroˡ; zeroʳ
      ; +-isCommutativeMonoid
      )

    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne + * 0#
    isCommutativeSemiringWithoutOne = record
      { isSemiringWithoutOne = isSemiringWithoutOne
      ; *-comm               = *-CM.comm
      }
```

## Ring

A Ring is a structure containing:

- A set $𝕊$
- Two binary operations: + and *

where the structure defined on the operations are:

1. $𝕊$ is an abelian group under addition, which implies the operation +:
    - is associative
    - is commutative
    - has an identity
    - has an inverse (-)
2. $𝕊$ is a monoid under multiplication, which implies the operation *:
    - is associative
    - has an identity
3. Multiplication is distributive over addition
4. There must be an annihilating element 𝕖 such that $∀ x : 𝕖 * x = 𝕖$

```agda
  record IsRing (+ * : ★ A) (-_ : ♠ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      +-isAbelianGroup : IsAbelianGroup + 0# -_
      *-isMonoid       : IsMonoid * 1#
      distrib          : * DistributesOver +
      zero             : Zero 0# *

    open IsAbelianGroup +-isAbelianGroup public
      renaming
      ( assoc               to +-assoc
      ; ∙-cong              to +-cong
      ; ∙-congˡ             to +-congˡ
      ; ∙-congʳ             to +-congʳ
      ; identity            to +-identity
      ; identityˡ           to +-identityˡ
      ; identityʳ           to +-identityʳ
      ; inverse             to -‿inverse
      ; inverseˡ            to -‿inverseˡ
      ; inverseʳ            to -‿inverseʳ
      ; ⁻¹-cong             to -‿cong
      ; comm                to +-comm
      ; isMagma             to +-isMagma
      ; isSemigroup         to +-isSemigroup
      ; isMonoid            to +-isMonoid
      ; isCommutativeMonoid to +-isCommutativeMonoid
      ; isGroup             to +-isGroup
      )

    open IsMonoid *-isMonoid public
      using ()
      renaming
      ( assoc       to *-assoc
      ; ∙-cong      to *-cong
      ; ∙-congˡ     to *-congˡ
      ; ∙-congʳ     to *-congʳ
      ; identity    to *-identity
      ; identityˡ   to *-identityˡ
      ; identityʳ   to *-identityʳ
      ; isMagma     to *-isMagma
      ; isSemigroup to *-isSemigroup
      )

    distribˡ : * DistributesOverˡ +
    distribˡ = fst distrib

    distribʳ : * DistributesOverʳ +
    distribʳ = snd distrib

    isSemiringWithoutAnnihilatingZero
      : IsSemiringWithoutAnnihilatingZero + * 0# 1#
    isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isMonoid            = *-isMonoid
      ; distrib               = distrib
      }

    isSemiring : IsSemiring + * 0# 1#
    isSemiring = record
      { isSemiringWithoutAnnihilatingZero =
          isSemiringWithoutAnnihilatingZero
      ; zero = zero
      }

    open IsSemiring isSemiring public
      using (distrib; isNearSemiring; isSemiringWithoutOne)
```

and finally, the commutative ring:

```agda
  record IsCommutativeRing
           (+ * : ★ A) (- : ♠ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      isRing : IsRing + * - 0# 1#
      *-comm : Commutative *

    open IsRing isRing public

    *-isCommutativeMonoid : IsCommutativeMonoid * 1#
    *-isCommutativeMonoid =  record
      { isMonoid    = *-isMonoid
      ; comm        = *-comm
      }

    isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
    isCommutativeSemiring = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isCommutativeMonoid = *-isCommutativeMonoid
      ; distrib               = (distribˡ , distribʳ)
      ; zero                  = zero
      }

    open IsCommutativeSemiring isCommutativeSemiring public
      using ( isCommutativeSemiringWithoutOne )
```

****
[Rings and family 2](./Algebra.rings2.html)
