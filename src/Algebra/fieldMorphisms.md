****
[Contents](contents.html)
[Previous](Algebra.fields2.html)
[Next](Algebra.numbers.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Field Morphisms](#field-morphisms)
  - [Field Homomorphism](#field-homomorphism)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Field Morphisms

```agda
module Algebra.fieldMorphisms where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Types.relations
open import Types.equality
open import Types.functions2

open import Algebra.groups
open import Algebra.groups2
open import Algebra.groupMorphisms
open import Algebra.ringMorphisms

open import Algebra.fields
open import Algebra.fields2
```

We keep following the same pattern as we have been doing for groups and rings. A morphisms between two fields is a structure-preserving map in a way that preserves the field properties.

## Field Homomorphism

A field homomorphism between two fields 𝔸 and 𝔹 is a function

```math
f : 𝔸 → 𝔹
```

such that ∀ x, y in 𝔸,

1. `f` is congruent over `+`, or
$$f(x + y) = f(x) + f(y)$$
3. `f` is congruent over `⋅`, or
$$f( x ⋅ y) = f(x) ⋅ f(y)$$
4. Identities are preserved, i.e.
$$f(1) = 1$$

The fields are isomorphic if `f` is bijective.



****
[Numbers](./Algebra.numbers.html)
