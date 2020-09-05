****
[Contents](contents.html)
[Previous](Lang.debugging.html)
[Next](Types.universe.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)
- [Set Theory](#set-theory)
  - [Basics of Set Theory](#basics-of-set-theory)
    - [Relations](#relations)
    - [Operations](#operations)
    - [Properties of Operations](#properties-of-operations)
- [Type Theory](#type-theory)
  - [Implications of Type Theory](#implications-of-type-theory)
    - [Foundations of Mathematics](#foundations-of-mathematics)
    - [Programming Language](#programming-language)
    - [Calculus for Category Theory](#calculus-for-category-theory)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Introduction

```agda
module Types.introduction where

open import Lang.dataStructures using (List; []; _::_; ℕ; one; three; seven; nine)
```

Type Theory can be thought of as the programming language used to implement math. Instead of the more familiar method of writing symbols on a piece of paper, we represent those symbols as code, which a compiler can then parse and type-check, thus guaranteeing the code's (and hence the represented math's) correctness. Though to programmers this might seem very natural, it is an extremely powerful method for doing math as the burden of verification becomes automated − thus significantly reducing testing time.

Most of mathematics, as we know it, is based on the foundations of Set Theory. In order to realize our goal of implementing math in Type Theory with some real convenience, the foundations need to be shaken up a bit, and reformulated from the ground-up.

# Set Theory

Set Theory is a mathematical theory which studies collections of objects, called `set`s. These objects, called `member`s or `element`s of the set, can literally be anything. The other main component of Set Theory is first-order logic, which is used to construct and reason around sets. The language of Set Theory can be used to define almost all of mathematical objects.

![Figure 1: Set](/artwork/set.png)

Set Theory has existed for centuries, has underdone several alterations, revisions (rewrites) as well as paradox removal (bug fixes, if you will). In fact, theories in mathematics follow similar lifecycles as seen in the programming world (or vice versa to be exact) leading to various flavors / versions / "forks" of the theory. The best-known amongst them is Zermelo-Fraenkel set theory (ZFC).

## Basics of Set Theory

Zermelo-Fraenkel Set theory (ZFC) consists of:

1. `Set`s which are a collection of objects.
2. a propositional first order logic system to create and manipulate these sets.
3. relations, maps and functions amongst sets.
4. properties of 3.

### Relations

1. Belongs

The basic relation of set theory is that of membership: `∈`, i.e. a statement such as `a ∈ Set A` which implies `a` is an element of the set `A`.

2. Equality

Two sets `A` and `B` are equal if `∀ x, x ∈ A iff x ∈ B`, read as: for all `x`, `x` is an element of `A` if and only if `x` is also an element of `B`.

3. Subsets

`A` is a subset of `B` if every element of `A` is an element of `B`, denoted as `A ⊆ B`.

### Operations

Given sets `A` and `B`, one can perform some basic operations with them yielding the following sets:

- The set `A∪B`, called the union of `A` and `B`, whose elements are the elements of `A` and the elements of `B`.

- The set `A∩B`, called the intersection of `A` and `B`, whose elements are the elements common to `A` and `B`.

- The set `A−B`, called the difference of `A` and `B`, whose elements are those elements of `A` that are not members of `B`.

### Properties of Operations

1. Associativity

```math
A∪(B∪C)=(A∪B)∪C
```

```math
A∩(B∩C)=(A∩B)∩C
```

2. Commutativity

```math
A∪B=B∪A
```

```math
A∩B=B∩A
```

3. Distributivity

```math
A∪(B∩C)=(A∪B)∩(A∪C)
```

```math
A∩(B∪C)=(A∩B)∪(A∩C)
```

4. Idempotency

```math
A∪A=A
```

```math
A∩A=A
```

```math
A∪∅=A
```

```math
A∩∅=∅
```

```math
A−A=∅
```

ZFC comprises of a bunch of axioms, which we are not going to look into here. The interested reader may explore them on [Zermelo–Fraenkel set theory: Wikipedia](https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory) or [nlab](https://ncatlab.org/nlab/show/ZFC#axioms).

# Type Theory

Type theory is a formal system of symbolic logic where every term has a "type". "Term" here refers to mathematical terms such as variable `x`, function `f`, operation `★` and so on. Bertrand Russell was the first to propose this theory in order to fix Russell's Paradox which plagued naive set theory, though Per Martin-Löf was the one to come up with a more practically useful version of it, called "Intuitionistic Type Theory".

![Figure 2: Haskell Type System](/artwork/typehierarchy.png)

A type system in programming languages typically specifies data and appears like a tree of objects, where each successive level tries to represent data more specifically. E.g., A `Float` is a subtype of `Number` and is a more specialized case of a `Number`.

![Figure 3: Scala Type System](/artwork/scala-type-system.png)

In a system of type theory, each term has a type. For example, `4`, `2+2` and `2 * 2` are all separate terms with the type `ℕ` for natural numbers. This is indicated as $2 : ℕ$ or 2 is of type natural number.

Type theories have explicit computation and it is encoded in rules for rewriting terms. These are called "conversion rules" or, if the rule only works in one direction, a "reduction rule". For example, `2+2` and `4` are syntactically different terms, but the former reduces to the latter. This reduction is written `2+2 ↠ 4`.

Functions in type theory have a special reduction rule: the argument to the function is substituted for every instance of the parameter in the function definition. Let's say the function `double` is defined as `double(x) = x + x` or mathematically $double: x ↦ x + x$. Then, the function call `double 2` would be reduced by substituting `2` for every `x` in the function definition. Thus, `double 2 ↠ 2+2`.

## Implications of Type Theory

### Foundations of Mathematics

Logic itself is subsumed in the plain idea of operations on terms of types, by observing that any type X may be thought of as the type of terms satisfying some proposition. In fact, propositions are types and thus finding a proof of the proposition is equivalent to constructing a term of the proposition type. We discuss about this in [Proofs as Data](./Types.proofsAsData.html).

### Programming Language

Since such a proof is constructive, the term witnessing it being a concrete implementation, and since type theory strictly works by rewriting rules, one may identify the construction of a term in type theory as a program whose output is a certain type. Under this "proofs as programs"-paradigm, type theory is a mathematical formalization of a programming language.

### Calculus for Category Theory

(Ignore if the reader is not familiar with category theory)
If we consider any term `t:X` to exist in a context `Γ` of other terms `x:Γ`, then `t` is naturally identified with a "map" `t:Γ→X`, hence: with a morphism. Viewed this way the types and terms of type theory are identified, respectively, with the objects and morphisms of category theory. From this perspective, type theory provides a formal language for speaking about categories.

****
[Universes and families](./Types.universe.html)
