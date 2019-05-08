<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Algebraic structures](#algebraic-structures)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Algebraic structures

```agda
module Algebra.introduction where
```

Algebra is essentially any system dealing with

- Abstract symbols as objects
- APIs - rules and laws for manipulating such symbols

The most basic of operations that can be done to an object are to compare them, e.g, using equivalences (≡), to order them using some definition of an order (≥, ≤) and so on. Generally, more complex structures can be created using the laws of associativity, commutativitiy and identity. An example of this would be natural numbers, which support operations such as addition, subtraction, multiplication and division (except with 0) forms linear algebra. Another example is what we have already seen in the case of boolean algebra where ∧ and ∨ follow the [laws of boolean algebra](./Logic.laws.html).

So far we have had a glimpse of type and boolean algebras. Here we start to dive into more complex structures - both structured data and maps (function families). Most of these structures are constructed by picking and choosing certain underlying laws or properties of these objects' APIs. We first start with building such laws. Many of these laws are similar to the ones of logic that we derived in a [previous part](./Logic.laws.html/#operations). We then diverge a bit and look at what equational reasoning is, how it is useful in proving theorems and and how we can do that in Agda. We then get right back into defining group-like objects and their properties.

****
[Back to Contents](./contents.html)
