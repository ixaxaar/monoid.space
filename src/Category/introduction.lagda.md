****
[Contents](contents.html)
[Previous](Algebra.real.html)
[Next](Category.category.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Category Theory: Introduction](#category-theory-introduction)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Category Theory: Introduction

```agda
module Category.introduction where
```

In the previous sections on groups, rings and fields we defined a bunch of structures and a bunch of morphisms on those structures. We observe that there is some pattern we follow while defining these structures:

1. All structures have an underlying set (`setoid`) of objects
2. There are one or more binary operations which act on objects in this set
3. The binary operations preserve at least associativity (except magma)

| Structure | Totality | Associativity | Identity | Invertibility | Commutativity |
| --- | --- | --- | --- | --- | --- |
| Magma | ★ |  |  |  |  |
| Semigroupoid |  | ★ |  |  |  |
| Small Category |  | ★ | ★ |  |  |
| Groupoid |  | ★ | ★ | ★ |  |
| Semigroup | ★ | ★ |  |  |  |
| Inverse Semigroup | ★ | ★ |  | ★ |  |
| Monoid | ★ | ★ | ★ |  |  |
| Commutative monoid | ★ | ★ | ★ |  | ★ |
| Group | ★ | ★ | ★ | ★ |  |
| Abelian group | ★ | ★ | ★ | ★ | ★  |

 It turns out there is a set of basic properties of a large number of mathematical structures, one can build tools on top of these properties such that they're applicable in a wide area of mathematics.

Category Theory is the set of tools to describe and work with generalized aspects of mathematical structures. A systematic study of category theory then allows us to prove general results about any of these types of mathematical structures. The stanford encyclopedia of philosophy describes it as:

> Roughly, it is a general mathematical theory of structures and of systems of structures. At minimum, it is a powerful language, or conceptual framework, allowing us to see the universal components of a family of structures of a given kind, and how structures of different kinds are interrelated.

Different areas of math share common patterns/trends/structures. For mathematicians, this becomes extraordinarily useful when you want to solve a problem in one realm (say, topology) but don't have the right tools at your disposal. By transporting the problem to a different realm (say, algebra), you can see the problem in a different light and perhaps discover new tools, and the solution may become much easier. The bridges between realms are also provided by category theory.

Category Theory has grown tremendously over the last few decades and has a large number of applications including:

1. Huge presence in theoretical computer science in the design of type systems and programming patterns including the structure `monad` that represents side-effects, especially IO. A mixture of structures from abstract algebras and category theory are used to form a class of programming patterns called "functional programming".
2. Widely adopted in physics and mathematical physics with field theories, higher field theories, quantum field and topological quantum field theories, quantum gravitation theories, string theory and so on making heavy use of categorical language.
3. Modeling various structures in life sciences and economics are some of the more novel applications.

---

[Categories](./Category.category.html)
