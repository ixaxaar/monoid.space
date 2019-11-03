****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Real Numbers](#real-numbers)
- [Fields](#fields)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Real Numbers

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.equality
open import Types.operations

module Algebra.real where
```

Real numbers are harder to construct as compared to natural numbers. The constructive definition of a real number is based on the algebraic object called "Field". We first define fields, followed by fields with ordering, also called "Ordered Fields". We then use the definitions of fields to construct real numbers. As a byproduct, we also show how to construct complex and rational numbers.

# Fields

In abstract algebra, a field has a very specific definition, which is different from the physics conception of a "thing spread across space". A field is, like real numbers, a bunch of objects (a set) for which addition, subtraction, multiplication and division operations are defined. Rational numbers, complex numbers as well as the set of binary values - 0 & 1, like real numbers, fall into this category. Another way to define fields is to define addition, multiplication and their inverses, i.e. subtraction and division, except at "0" - the identity element for multiplication. The formal definition of fields tries to capture all aspects of these operations.

A field is defined as a set with two operations - addition and multiplication. Thus, an operation on a field would be a function type with the signature `F : 𝜟 → 𝜟 → 𝜟` where `𝜟` is the set of objects in the field. The operations are required to have the following structure:

- __Associativity__: both operations must be associative, i.e. `a + (b + c) = (a + b) + c` and `a · (b · c) = (a · b) · c`.
- __Commutativity__: both operations must commute -  `a + b = b + a` and `a · b = b · a`.
- __Identities__: both operations must have identities and these identities must be different. `a + ι = a` and `a ⋅ ℑ = ℑ`.
- __Inverses__: both operations must have inverse operations, i.e. subtraction and division must exist.
- __Distributivity__: both operations must be distributive, i.e.  `a · (b + c) = (a · b) + (a · c)`.

where `a, b, c ∈ 𝜟`.

```ladagda
record Field {ℓ} {A : Set ℓ}()
```

****
[System F](./Algrbra.system_f.html)
