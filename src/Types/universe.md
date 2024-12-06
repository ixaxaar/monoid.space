****
[Contents](contents.html)
[Previous](Types.introduction.html)
[Next](Types.relations.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Universes](#universes)
  - [Introduction to Universes](#introduction-to-universes)
  - [Universes in Agda](#universes-in-agda)
  - [Universe Levels](#universe-levels)
  - [Universe Polymorphism](#universe-polymorphism)
  - [Cumulativity](#cumulativity)
  - [The Prop Universe](#the-prop-universe)
  - [Families of Types](#families-of-types)
  - [Machinery on Types](#machinery-on-types)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Universes

Set theory has had to deal with paradoxes, such as Russell's Paradox, which shows that the set of all sets that do not contain themselves cannot exist. Set theorists have developed ways to avoid these paradoxes, such as the Zermelo-Fraenkel axioms or ZFC, which avoid the paradoxes by restricting the kinds of sets that can be formed to in a well-defined way.

Just like Set theory, Type theory also has had to deal with paradoxes. In Type theory, we have a similar problem to Russell's Paradox: the type of all types cannot exist, as it would lead to a contradiction. To avoid this, the concept of universes was introduced. Universes are a way to organize types into a hierarchy, where each universe contains the types of the universe below it. This way, we can avoid paradoxes by not allowing types to contain themselves. In Lean, the type of all types is called `Type`, and it is a universe itself. However, to avoid paradoxes, Lean uses a hierarchy of universes, where each universe contains the types of the universe below it.

Formally, the structure of the universe used in type theory are Russell-style and Tarski-style universes. In Russell-style universes, the universe is a type, and in Tarski-style universes, the universe is a type family. In Lean, the universe is a type family, and it is called `Sort`. The `Sort` family is a type family that contains all the types in the hierarchy of universes.

This heirarchy of universes is denoted as:

```lean
Type 0  -- Also written as Type, the universe of "small" types
Type 1  -- The universe containing Type 0
Type 2  -- The universe containing Type 1
-- and so on...
```

Basic types like `Nat`, `Bool`, `String`, etc. are in `Type 0`:

```lean
#check Nat -- : Type
#check Bool -- : Type
#check String -- : Type
```

The type `Type` itslef is in `Type 1`:

```lean
#check Type -- : Type 1
```

Each level of the universe hierarchy contains the types of the universe below it. This way, we can avoid paradoxes by not allowing types to contain themselves.

```lean
#check Type 0 -- : Type 1
#check Type 1 -- : Type 2
#check Type 2 -- : Type 3
#check Type 3 -- : Type 4
```




****
[Relations](./Types.relations.html)
