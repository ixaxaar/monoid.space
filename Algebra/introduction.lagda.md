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
- APIs - rules, laws, or in general, operations for manipulating such symbols

Each algebra behaves more like a DSL, each consisting of a structure and a bunch of operations packaged together.

The most basic operation that can be done to an object or to a collection (set) of objects is to compare them, e.g, using equivalences (≡). Thus equivalanences can be used as a law for creating albegras of `Setoid`s - sets with equivalences. The operation of sorting using some definition of an order (≥, ≤) is another such basic law used to construct higher objects and their algebras such as `Poset`s and `PreOrder`s.

![magma](./magma.png)

Generally, more complex structures can be created using the laws of associativity, commutativitiy and inverse. An example of this would be natural numbers, which support operations such as addition, subtraction, multiplication and division (except with 0), all of which are associative and commutative, forming the peano arithmetic. Another example is what we have already seen in the case of boolean algebra where ∧ and ∨ follow the [laws of boolean algebra](./Logic.laws.html). There are more complex objects that follow essentially the same principles of construction.

General classification of abstract algebras include

| Number of Binary operations | Sets | Examples |
| --- | --- | --- |
| 1 | 1 | Magma, Semigroupoid, Small Category, Semigroup, Groupoid, Monoid, Group |
| 2 | 1 | Ring, Lattics, Semiring |
| 2 | 2 | Vector Spaces, Modules |
| 3 | 2 | Algebra over a field, Algebra over a ring |

We can always mix and match and create objects of higher complexity. There are also a varying mix of objects and their algebras tying other areas of mathematics like topology.

So far we have had a glimpse of type and boolean algebras. Here we start to dive into more complex structures - both structured data and maps (function families). Most of these structures are constructed by picking and choosing certain underlying laws or properties of these objects' APIs. We first start with building such laws. Many of these laws are similar to the ones of logic that we derived in a [previous part](./Logic.laws.html/#operations). We then diverge a bit and look at what equational reasoning is, how it is useful in proving theorems and and how we can do that in Agda. We then get right back into defining group-like objects and their properties.

****
[Operations](./Algebra.operations.html)
