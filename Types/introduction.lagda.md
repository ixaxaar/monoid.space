<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)
  - [The scala type system](#the-scala-type-system)
  - [Judgements and Propositions](#judgements-and-propositions)
- [The Bottom type](#the-bottom-type)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Introduction

```agda
module Types.introduction where

open import Lang.dataStructures using (List; []; _::_; ℕ; one; three; seven; nine)
```

Type theory is an area of mathematics of direct consequence to programming. Type theory is about a class of formal systems, not much unlike type systems in programming languages. Bertrand Russel was the first to propose this theory in order to "fix" Russel's Paradox, though Per Martin-Löf was the one to come up with an actually useful version of it, called "intuitionistic type theory". This is what we will go through here. Though thanks to the Curry-Howard isomorphism, which basically connects two areas of math : type theory can be mapped to logic and studied as such.

Type systems present especially in statically compiled programming languages could also be seen as those sets that type theory is about. The goal of this section could also be to gain further insight into abstractions using type systems and how to really take advantage of certain compilers.


## The scala type system

![scala-type-system](./scala-type-system.png)

## Judgements and Propositions

The basic constructs of type theory is based on the concept of "judgement" versus "propositions".

Zermelo-Frenkel Set theory (ZFC) consists of:

- `Set`s which are a collection of objects
- a propositional first order logic system to create and manipulate such objects and sets
- maps amongst such sets

which is in fact pretty much the basic components of any imperative programming language.

However, the problem here is with `propositions` as in there can exist propositions which turn out to be false. However, types as objects serve as judgements. An object with type defined, say, `List A` fully specifies it, and can be type-checked by a first-order logic system to prove or disprove.

```agda
fullySpecified : List ℕ
fullySpecified = one :: three :: seven :: nine :: []
```

Thus, `fullySpecified` once specified, has already been proven and requires no proving. Hence it is a judgement, whereas something like `a ∈ A` is a proposition, which needs a proof (of ∈).

In type theory, we cannot introduce a variable without specifying its type. Hence, everything becomes a judgement by default if it compiles, and by piling up these judgements we can prove theories, simply by constructing them as objects.


# The Bottom type

The Bottom type in Agda, is akin to `Nothing` type in scala. As far as types are concerned, this indicates a never-ending computation.

The bottom type can be defined using either the `data` API or using `postulate`s:

```agda
data False : Set where
```

```agda
postulate bottom : False
```

```agda
data ⟂ : Set where
```

****
[Back to Contents](./contents.html)
