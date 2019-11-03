****
[Contents](contents.html)
[Previous](Algebra.groupProperties.html)
[Next](Algebra.ringProperties.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Rings](#rings)
  - [Semiring](#semiring)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Rings

A ring is a structure containing:

- A set $ 𝕊 $
- Two binary operations: + and −

where the structure defined on the operations are:

1. $ 𝕊 $ is an abelian group under addition, which implies the operation +:
    - is associative
    - is commutative
    - has an inverse (−)
    - has an identity

2. $ 𝕊 $ is a monoid under multiplication, which implies the operation ★:
    - is associative
    - has an identity
3. Multiplication is distributive over addition

Examples of rings would be natural, real, complex and rational numbers. Any algebra over a ring is also a ring. Hence, any set of n × n matrices of real numbers also forms a ring. A set of real upper or lower triangular matrices would also form a ring. The family of rings starts from semirings and goes on with commutative semirings, rings and commutative rings.

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.equality

module Algebra.rings {a ℓ} {A : Set a} (_==_ : Rel A ℓ) where
  open import Types.operations (_==_)
  open import Algebra.groups (_==_)
```

In order to derive the family of Rings, we start with the idea of an indempotent function. An Idempotent function is one which, when applied multiple times on an initial input produces the same result. That is, if 𝔽 is a function $ 𝔽 : ϕ → ϕ $ then it's repeated application $ 𝔽(𝔽(𝔽(...𝔽(x)...))) == 𝔽(x) $.

```agda
  _IdempotentOn_ : ★ A → A → Set _
  _∙_ IdempotentOn x = (x ∙ x) == x

  Idempotent : ★ A → Set _
  Idempotent ∙ = ∀ x → ∙ IdempotentOn x

  IdempotentFunction : ♠ A → Set _
  IdempotentFunction f = ∀ x → f (f x) == f x
```

## Semiring




****
[System F](./AppliedTypes.system_f.html)
