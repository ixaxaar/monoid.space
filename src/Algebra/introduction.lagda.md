****
[Contents](contents.html)
[Previous](Logic.decidability.html)
[Next](Algebra.order.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Abstract Algebra](#abstract-algebra)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Abstract Algebra

```agda
module Algebra.introduction where
```

Algebra is essentially any system dealing with

- Abstract symbols as objects
- APIs - rules, laws, or in general, operations for manipulating such symbols

Each algebra behaves more like a [DSL](https://en.wikipedia.org/wiki/Domain-specific_language), consisting of a set of objects of a type and a bunch of operations packaged together. The algebra that we generally know of are linear, matrix, complex, vector and boolean algebras, all of which deal with real or natural numbers based objects (e.g. matrices or complex numbers) and build on top of their four operations (+,−,★,÷). The field of abstract algebra introduces a variety of more abstract, and arguably more simpler structures than real number systems.

Objects when considered together with some operations give rise to complex structures and allow a bunch of laws and other machinery to be built on top of them.

Consider natural numbers and the operation of addition for example, for any two natural numbers `x` and `y` and the addition operation `+`, $x + y$ is always a natural number. Also, the following laws are always followed:
$$
x + y = y + x \\
(x + y) + z = x + (y + z)
$$
Thus we can refer to all natural numbers and addition together as a algebraic structure called a "group". It turns out such structures have rich APIs and can be used to model and represent wide range of real world phenomenon. Groups can be easily encountered in undergraduate and above level physics which makes extensive use of the concepts of symmetry.

Generally, more complex structures can be created using operations that support the laws of associativity, commutativity and inverse. An example of this would be natural numbers, which support operations such as addition, subtraction, multiplication and division (except with 0), all of which are associative and commutative, forming the peano arithmetic. Another example is what we have already seen in the case of boolean algebra where `∧` and `∨` follow the [laws of boolean algebra](./Logic.laws.html). There are more complex objects that follow essentially the same principles of construction.

General classification of abstract algebras include

| Number of Binary operations | Sets | Examples |
| --- | --- | --- |
| 1 | 1 | Magma, Semigroupoid, Small Category, Semigroup, Groupoid, Monoid, Group |
| 2 | 1 | Ring, Lattics, Semiring |
| 2 | 2 | Fields (Real, complex, rational numbers), Vector Spaces, Modules |
| 3 | 2 | Algebra over a field, Algebra over a ring |

We can always mix and match and create objects of higher complexity. There are also a varying mix of objects and their algebras tying other areas of mathematics like differential geometry, topology, number theory.

So far we have had a glimpse of boolean algebra. Here we start to dive into more complex structures. Most of these structures are constructed by picking and choosing certain underlying laws or properties of these objects' APIs. We first start with building such laws. Many of these laws are similar to the ones of logic that we derived in a [previous part](./Logic.laws.html/#operations).

****
[Order](./Algebra.order.html)
