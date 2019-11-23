****
[Contents](contents.html)
[Previous](Algebra.rings.html)
[Next](./Algebra.numbers.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Fields and Family](#fields-and-family)
  - [Fields](#fields)
  - [Ordered Fields](#ordered-fields)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Fields and Family

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.equality

module Algebra.fields {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
  open import Types.operations (_==_)

  open import Algebra.order (_==_)
  open import Algebra.groups (_==_)
  open import Algebra.rings (_==_)
```

## Fields

In abstract algebra, a field has a very specific definition, which is different from the physics conception of a "thing spread across space". A field is, like real numbers, a bunch of objects (a set) for which addition, subtraction, multiplication and division operations are defined. Rational numbers, complex numbers as well as the set of binary values - 0 & 1, like real numbers, fall into this category. Another way to define fields is to define addition, multiplication and their inverses, i.e. subtraction and division, except at "0" - the identity element for multiplication. The formal definition of fields tries to capture all aspects of these operations.

A field is defined as a set with two operations - addition and multiplication. Thus, an operation on a field would be a function type with the signature `F : 𝔽 → 𝔽 → 𝔽` where `𝔽` is the set of objects in the field.

A field is a structure containing:

- A set $ 𝔽 $
- Two binary operations: + and −

where the structure defined on the operations are:

1. $ 𝔽 $ is an abelian group under addition, which implies the operation +:
    - is associative
    - is commutative
    - has an inverse (−)
    - has an identity
2. $ 𝔽 $ is an abelian group under multiplication, which implies the operation ★:
    - is associative
    - is commutative
    - has an inverse (−)
    - has an identity
3. Multiplication is distributive over addition
4. There must be an annihilating element 𝕖 such that $ ∀ x : 𝕖 ★ x = 𝕖 $

A field is thus a more restricted version of a Ring, where there are additional requirements of commutativity and inverse of multiplication.

```agda
  record IsField (+ * : ★ A) (-_ ÷_ : ♠ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      +-isAbelianGroup : IsAbelianGroup + 0# -_
      *-isAbelianGroup : IsAbelianGroup * 1# ÷_
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

    open IsAbelianGroup *-isAbelianGroup public
      using ()
      renaming
      ( assoc               to *-assoc
      ; ∙-cong              to *-cong
      ; ∙-congˡ             to *-congˡ
      ; ∙-congʳ             to *-congʳ
      ; identity            to *-identity
      ; identityˡ           to *-identityˡ
      ; identityʳ           to *-identityʳ
      ; inverse             to ÷‿inverse
      ; inverseˡ            to ÷‿inverseˡ
      ; inverseʳ            to ÷‿inverseʳ
      ; ⁻¹-cong             to ÷‿cong
      ; comm                to *-comm
      ; isMagma             to *-isMagma
      ; isSemigroup         to *-isSemigroup
      ; isMonoid            to *-isMonoid
      ; isCommutativeMonoid to *-isCommutativeMonoid
      ; isGroup             to *-isGroup
      )

    isRing : IsRing + * -_ 0# 1#
    isRing = record
      { +-isAbelianGroup = +-isAbelianGroup
      ; *-isMonoid       = *-isMonoid
      ; distrib          = distrib
      ; zero             = zero
      }
```

## Ordered Fields

Ordered fields impose an additional restriction on fields: there has to be an order `≤` between members of 𝔽. This order is required to be a total order.

```agda
  record IsOrderedField (+ * : ★ A) (-_ ÷_ : ♠ A) (_≤_ : Rel A ℓ) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      +-isAbelianGroup : IsAbelianGroup + 0# -_
      *-isAbelianGroup : IsAbelianGroup * 1# ÷_
      distrib          : * DistributesOver +
      zero             : Zero 0# *
      isTotalOrder     : IsTotalOrder _≤_

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

    open IsAbelianGroup *-isAbelianGroup public
      using ()
      renaming
      ( assoc               to *-assoc
      ; ∙-cong              to *-cong
      ; ∙-congˡ             to *-congˡ
      ; ∙-congʳ             to *-congʳ
      ; identity            to *-identity
      ; identityˡ           to *-identityˡ
      ; identityʳ           to *-identityʳ
      ; inverse             to ÷‿inverse
      ; inverseˡ            to ÷‿inverseˡ
      ; inverseʳ            to ÷‿inverseʳ
      ; ⁻¹-cong             to ÷‿cong
      ; comm                to *-comm
      ; isMagma             to *-isMagma
      ; isSemigroup         to *-isSemigroup
      ; isMonoid            to *-isMonoid
      ; isCommutativeMonoid to *-isCommutativeMonoid
      ; isGroup             to *-isGroup
      )

    isRing : IsRing + * -_ 0# 1#
    isRing = record
      { +-isAbelianGroup = +-isAbelianGroup
      ; *-isMonoid       = *-isMonoid
      ; distrib          = distrib
      ; zero             = zero
      }
```


****
[Numbers](./Algebra.numbers.html)
