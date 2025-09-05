---

[Contents](contents.html)
[Previous](Types.introduction.html)
[Next](Types.relations.html)

# Universes

---

- [The `Type` Type](#the-type-type)
- [Lifting Types](#lifting-types)
- [Universe Polymorphism](#universe-polymorphism)
- [The `Prop` Type](#the-prop-type)
- [`Prop` and `Type` and `Sort`](#prop-and-type-and-sort)

Set theory confronts paradoxes like Russell's Paradox, demonstrating that the set of all sets not containing themselves cannot exist. To avoid such paradoxes, set theorists developed axiomatic systems like Zermelo-Fraenkel with Choice (ZFC), which restrict set formation through well-defined rules.

Type theory faces analogous paradoxes: the type of all types cannot exist without contradiction. Type theory resolves this through universes—a hierarchy organizing types such that each universe contains types from lower levels, preventing self-containment. Lean's `Type` represents this universe hierarchy, where higher universes contain lower ones.

In Type Theory, a universe is a type that contains other types. Formally, a universe is a type `U` such that for any type `A`, `A : U` means that `A` is a type. The universe is used to organize the types in a hierarchy, where each universe contains the types of the universe below it.

## The `Type` Type

The structure of the universe used in type theory are Russell-style and Tarski-style universes. In Russell-style universes, the universe is a type, and in Tarski-style universes, the universe is a type family. In Lean, the universe is a type family, and it is called `Type`. The `Type` family is a type family that contains all the types in the hierarchy of universes. Theorem provers have chosen either Russell-style or Tarski-style universes, some examples for Russell-style are Coq and Agda, and for Tarski-style are Lean and Idris, and each has its own advantages and disadvantages.

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

Function types occupy the same universe level that can contain both their argument types and their return types. For example, the type of a function that takes a `Nat` and returns a `Nat` is in `Type 0`:

```lean
#check Nat → Nat -- : Type
```

The type of a function that takes a `Nat` and returns a `Bool` is in `Type 0`:

```lean
#check Nat → Bool -- : Type
```

The type of a function that takes a `Nat` and returns a `Type` `Type 1`:

```lean
#check Nat → Type -- : Type 1
```

## Lifting Types

Elements of a higher universe level can be created from elements of a lower universe level. "Lifting" is a mechanism that allows us to take a type from one universe level and create a corresponding type at a higher universe level. For example, we can create a function that takes a type in `Type 0` and returns a type in `Type 1`:

```lean
def liftType.{u} (α : Type u) : Type (u+1) := PLift α
```

Here, `PLift` is a type constructor that takes a type `α` in `Type u` and returns a type in `Type (u+1)`. The `u` in `Type u` is a universe level parameter, which is used to specify the universe level of the type. The `u+1` in `Type (u+1)` is the universe level of the returned type. The `.{u}` is a universe level parameter that specifies the universe level of the function, which can also be inferred by Lean:

```lean
def liftType1 (α : Type u) : Type (u+1) := PLift α
```

Here, we have omitted the universe level parameter `u` in the function definition (the `.{u}`), and Lean will infer the universe level from the type of the argument `α`.

This function can be used to create a type in `Type 1` from a type in `Type 0`:

```lean
#check @liftType.{0} Nat  -- Nat : Type 1
#check @liftType1 Nat  -- Nat : Type 1
```

## Universe Polymorphism

Universe polymorphism is a feature of type theory that allows us to write functions that can take types in any universe level, and return types in any universe level.

In Lean, universe polymorphism is used to specify the universe level of a type. Universe polymorphism allows us to write functions that can take types in any universe level. For example, the `liftType` function above is universe polymorphic, as it can take types in any universe level. The `u` in `Type u` is a universe level parameter, which is used to specify the universe level of the type.

Universe polymorphism is used to specify the universe level of a type. For example, the `liftType` function above is universe polymorphic, as it can take types in any universe level. The `u` in `Type u` is a universe level parameter, which is used to specify the universe level of the type.

Here are a few examples of universe polymorphism in Lean:

```lean
def idd.{u} (α : Type u) (a : α) : α := a
#check @idd.{0} Nat -- (α : Type) → α → α

def pair.{u, v} (α : Type u) (β : Type v) (a : α) (b : β) : α × β := (a, b)
#check @pair.{0, 0} -- (α β : Type) → α → β → α × β

inductive Listy (α : Type u) : Type u where
  | nil : Listy α
  | cons : α → Listy α → Listy α
def mylist : Listy Nat :=
  .cons 2 (.cons 2 .nil) -- Listy Nat
```

Definitions with multiple arguments can have multiple universe level parameters for maximum flexibility.

```lean
inductive SumInflexible (x : Type u) (y : Type u) : Type u where
  | inl : x → SumInflexible x y
  | inr : y → SumInflexible x y

def stringOrNat : SumInflexible String Nat :=
  SumInflexible.inl "hello" -- SumInflexible String Nat
```

This is an inflexible definition because the universe level of `SumInflexible` is fixed to the universe level of the arguments `x` and `y`. This means that `SumInflexible` can only be used with both types of `x` and `y` in the same universe level.

```lean
inductive SumFlexible (x : Type u) (y : Type v) : Type (max u v) where
  | inl : x → SumFlexible x y
  | inr : y → SumFlexible x y

def stringOrListString : SumFlexible String (List String) :=
  SumFlexible.inl "hello"
```

whereas `SumFlexible` is a flexible definition because the universe level of `SumFlexible` is the maximum of the universe levels of the arguments `x` and `y`. This means that `SumFlexible` can be used with types in different universe levels.

## The `Prop` Type

In Lean, the `Prop` type is used to represent propositions, which are types that represent logical statements. The `Prop` type is a universe that contains the types of propositions. The `Prop` type is used to represent logical statements, such as `true`, `false`, `∀`, `∃`, etc. For propositions, it does not matter which evidence is used to prove them, only that they are true, unlike a program which requires a specific value to be returned, say `3` and not just any `Nat`.

The type of `Prop` is in `Type 0`:

```lean
#check Prop -- : Type
```

A few simple propositions in Lean:

```lean
def isTrue : Prop := true

theorem simple_prop : 1 = 1 := rfl -- 1 = 1
#check simple_prop -- 1 = 1 : Prop

def truthValues : List Prop := [true, false, 1 + 2 = 3, 2 + 2 = 5]
```

## `Prop` and `Type` and `Sort`

In Lean's internal implementation, there's a more fundamental concept called `Sort`. The `Sort` is the "type of types", and both `Prop` and `Type` are examples of `Sort`. To organize the different levels of universes for types, Lean uses the hierarchy `Sort 0`, `Sort 1`, `Sort 2`, and so on. `Type u` is essentially shorthand for `Sort (u + 1)`.

Here's where the special role of `Prop` comes in:

- **`Prop` is synonymous with `Sort 0`.** This is the lowest universe level.
- **`Type 0` is `Sort 1`, `Type 1` is `Sort 2`, and so on.**
- **`Sort u` is in `Sort (u + 1)` for any universe level `u`.** This prevents types from containing themselves.

This means `Prop` is special because it sits at the bottom of the universe hierarchy. This design choice is related to the idea of _impredicativity_, which essentially means that when creating something in `Prop` (proving a proposition), we are allowed to quantify over all propositions, in other words we are allowed to use the proposition we are trying to prove in the proof itself. Impredicativity is very powerful but can cause logical inconsistencies if not handled carefully, as self-reference can lead to paradoxes. By keeping `Prop` separate at the bottom, Lean ensures consistency.

It is important to note that `Prop` and `Type` are distinct because `Prop` is _impredicative_, while `Type` is _predicative_. In a predicative system, a definition cannot refer to the totality of objects to which it belongs. In an impredicative system, a definition can refer to the totality of objects to which it belongs. In Lean, `Prop` is impredicative because it contains definitions that refer to the totality of propositions. For example, the definition of `∀` refers to the totality of propositions:

```lean
∀ (P : Prop), P   -- For all propositions P, P is true
```

This definition refers to the totality of propositions, including the proposition being defined. This is not allowed in a predicative system. In Lean, `Type` is predicative because it contains definitions that do not refer to the totality of types. For example, the definition of equality refers to the totality of natural numbers in a given universe:

```lean
∀ (a b : Nat), a = b  -- For all natural numbers a and b, a is (not) equal to b
```

This definition refers to the totality of natural numbers in a given universe, but not to the totality of all types. This is allowed in a predicative system.

---

[Relations](./Types.relations.html)
