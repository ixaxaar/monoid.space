****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)
  - [The scala type system](#the-scala-type-system)
  - [Judgements and Propositions](#judgements-and-propositions)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Introduction

```agda
module Types.introduction where

open import Lang.dataStructures using (List; []; _::_; ℕ; one; three; seven; nine)
```

Set theory is a formal system of mathematics which serves as a language for constructing and studying collections of objects called "sets". A set, in plain language, is a collection of zero or more objects. These objects can be literally anything.

![Figure 1: Set](./set.png)

Set theory is about sets as objects of study. There happen to be several flavors, or versions if you will, of set theory starting from naive set theory, to axiomatic Zermelo-Fraenkel set theory (ZFC) which is currently the most well known, accepted and popular flavor. Much of mathematics and computer science fundamentals has been built upon the foundations of set theory. In its infancy, naive set theory faced certain technical challenges, called paradoxes or inconsistencies, which were progressively removed, the rules or "axoims" refined and the very meaning of "object" redefined, resulting what is called ZFC. Other variations have also surfaced to accomodate higher abstract math, and which may even include the equality operator to be a part of sets. However, most of foundational mathematics is rather based on Type theory, whose genesis can be credit to Bertrand Russell.

Type theory is an area of mathematics of direct consequence to programming. Type theory is a formal system of symbolic logic where everything is a "type". Bertrand Russell was the first to propose this theory in order to fix Russell's Paradox which plauged naive set theory, though Per Martin-Löf was the one to come up with a more useful version of it, called "intuitionistic type theory". This is what we will go through here.

A type system in programming languages typically specifies data and appears like a tree of objects, where each successive level tries to represent data more specifically. E.g., A `Float` is a subtype of `Number` and is a more specialized case of a numbers. Type systems are designed using type theory and languages tend to have varying levels of tightness of integration with type theory broadly resulting in staticaly and dynaically typed languages. However, in type theory, a "type" can essentially mean anything - from as general as the type of all types, to super specific, like the number `3`. Hence everything, individual objects, sets or collections of objects, types in programming languages, entire programming langauge type systems, every logical statement, theorems, proofs, functions, any other mathematical object, even equality itself, are all "types".

## The scala type system

![Figure 2: Scala Type System](./scala-type-system.png)

## Judgements and Propositions

The basic constructs of type theory as opposed to set theory is based on the concept of "judgement"s versus "proposition"s.

Zermelo-Frenkel Set theory (ZFC) consists of:

- `Set`s which are a collection of objects
- a propositional first order logic system to create and manipulate them
- maps or functions amongst sets

which is in fact pretty much the basic components of any programming language, with data types as collections or sets of objects, first order logic to construct such objects and functions to manipulate them.

However, the problem here is with `propositions` as in there can exist propositions which turn out to be false. However, types as objects serve as judgements. An object with type defined, say, `List[Int]` fully specifies it, and can be type-checked by a first-order logic system for validity. In type theory, propositions are just another kind of types, and hence the judgement of a proposition being true relies on the fact that the proposition can be fully specified. Thus type theory eliminates the possibility of specifying something that can be disproven. Hence, whereas a proposition `prop` in set theory would require a proof to be proven later, and can turn out to be false, a proposition `prop : P` fully specified as type `P` requires the proof as part of its specification otherwise it will not compile!. Though this distinction is very subtle, it is so crucial that it ended up replacing set theory as the foundation on which to build mathematics.

```agda
fullySpecified : List ℕ
fullySpecified = one :: three :: seven :: nine :: []
```

Thus, `fullySpecified` once specified, has already been proven and requires no proving. Hence it is a judgement, whereas something like `x ∈ ℕ` is a proposition, which needs a proof for every given a of "∈ to ℕ".

In type theory, we cannot introduce a variable without specifying its type. Hence, everything becomes a judgement by default if it compiles, and by piling up these judgements we can prove theories, simply by constructing and composing them as objects. This fundamental difference is what makes type theory more consistent and easier to use to construct higher mathematical structures on and moreso do it using better tools such as a programming language. Agda is a faithful implementation of type theory and hence serves as an effective tool to do mathematics constructively.

****
[Universes and families](./Types.universe.html)
