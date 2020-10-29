---

[Contents](contents.html)
[Previous](Algebra.introduction.html)
[Next](Algebra.order.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Sets in Type Theory](#sets-in-type-theory)
  - [Setoid](#setoid)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Sets in Type Theory

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.relations
open import Types.equality

module Algebra.sets where
```

The concept of set appears in several different guises in mathematics. In type theory, Sets are defiend in a way to "make sense" in a mathematical way. We will revisit the sense part at a later time.

## Setoid

A setoid is a set of objects equipped with an equivalence relation.

```agda
record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≃_
  field
    Data          : Set c
    _≃_           : Rel Data ℓ
    isEquivalence : IsEquivalence _≃_

  open IsEquivalence isEquivalence public
```

This concept comes from [Bishop](https://ncatlab.org/nlab/show/Errett+Bishop) who defined the notion of set to be specified by stating that a set has to be given by a description of how to build elements of this set and by giving a binary relation of equality, which has to be an equivalence relation.

---

[Identity Types and Paths](./Algebra.order.html)
