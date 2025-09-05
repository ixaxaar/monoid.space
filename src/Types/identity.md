---

[Contents](contents.html)
[Previous](Types.functions.html)
[Next](Proofs.introduction.html)

# Identity Types

---

- [Introduction](#introduction)
  - [Different Notions of Equality](#different-notions-of-equality)
- [Identity Types](#identity-types)
  - [Properties](#properties)
    - [Reflexivity](#reflexivity)
    - [Symmetry](#symmetry)
    - [Transitivity](#transitivity)
- [Path Induction](#path-induction)
  - [The J Rule](#the-j-rule)
  - [Based Path Induction](#based-path-induction)
  - [Examples](#examples)
- [Transport](#transport)
  - [Definition](#definition)
  - [Examples](#examples-1)
- [Higher Identity Types](#higher-identity-types)
  - [Iterated Identity Types](#iterated-identity-types)
  - [Paths Between Paths](#paths-between-paths)
- [Towards Homotopy Type Theory](#towards-homotopy-type-theory)
  - [The Correspondence](#the-correspondence)

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Basic
```

## Introduction

In programming, we often need to compare values for equality. In most languages, this is done with operators like `==` or `.equals()`. However, in type theory, equality is a much richer concept. Instead of being just a boolean operation that returns true or false, equality is itself a type. This means we can talk about proofs of equality, transformations between equal things, and even equalities between equalities.

Consider these seemingly simple questions:

- When are two functions equal?
- When are two proofs of the same theorem equal?
- If we have two ways to show that `a = b`, are these ways themselves equal?

These questions lead us to identity types, which provide a foundation for answering such questions and form the basis for more advanced concepts like Homotopy Type Theory.

### Different Notions of Equality

Before looking at identity types, let's recall the different kinds of equality we've encountered:

1. **Definitional Equality:** Two terms are definitionally equal if they are equal "by definition" - they compute to the same thing. For example:

```lean
#eval 2 + 2 -- 4
#eval 4     -- 4
```

Here, `2 + 2` and `4` are definitionally equal because they compute to the same value.

2. **Propositional Equality:** This is equality that needs to be **proven**. We write it as `a = b` in Lean:

```lean
-- This needs a proof, even though it's "obvious"
example : 2 + 3 = 5 := rfl
```

3. **Path Equality:** This is the notion of equality we'll focus on in this chapter. It views equality as a "path" or identification between two points.

## Identity Types

Identity types, written as `a = b` or `Id a b` in type theory, represent the type of identifications (or paths) between two terms `a` and `b` of the same type.

In Lean, the identity type is defined inductively (we'll see the actual definition later), but conceptually it looks like this:

```lean
inductive Eq {α : Type u} (a : α) : α → Type u
| refl : Eq a a
```

This seemingly simple definition has profound implications. Let's break it down:

1. For any type `α` and elements `a b : α`, there is a type `a = b`
2. We can construct a term of type `a = a` using `refl` (reflexivity)
3. All other equalities require a proof

For example:

```lean
def proof_2_plus_2 : 2 + 2 = 4 := rfl

#check proof_2_plus_2 -- proof_2_plus_2 : 2 + 2 = 4
```

Note that `proof_2_plus_2` is not just a boolean value - it's a term of an identity type.

### Properties

Identity types have several fundamental properties that make them behave like our intuitive notion of equality.

#### Reflexivity

Every term is equal to itself:

```lean
def refl_example {α : Type} (a : α) : a = a := rfl
```

#### Symmetry

If `a = b`, then `b = a`:

```lean
def symm_example {α : Type} {a b : α} (h : a = b) : b = a := Eq.symm h
```

#### Transitivity

If `a = b` and `b = c`, then `a = c`:

```lean
def trans_example {α : Type} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
  Eq.trans h₁ h₂
```

## Path Induction

The most powerful principle for working with identity types is path induction, also known as the J rule. This principle captures the idea that to prove something about all equalities, it suffices to prove it for reflexivity.

### The J Rule

The J rule states that to prove a property P of all equalities `p : x = y`, it suffices to prove P for all reflexivity proofs `refl : x = x`. In Lean:

```lean
def J {α : Type} {x : α}
      (P : (y : α) → x = y → Sort u)
      (r : P x rfl)
      {y : α} (p : x = y) : P y p :=
  match p with
  | rfl => r
```

This might look intimidating, but it's saying: if you want to prove something about _any_ equality, you only need to prove it for the case where the equality is reflexivity, i.e. the most basic case and all other equalities can be reduced to this.

### Based Path Induction

A simpler version of path induction fixes one endpoint:

```lean
def based_path_induction
      {α : Type} {a : α}
      (P : (x : α) → a = x → Prop)
      (r : P a rfl)
      {b : α} (p : a = b) : P b p :=
  match p with
  | rfl => r
```

### Examples

Here's how we might use path induction to prove symmetry of equality:

```lean
def symm_using_J {α : Type} {a b : α} (p : a = b) : b = a :=
  J (fun x q => x = a) rfl p
```

## Transport

Transport is a fundamental operation that allows us to move terms between types that are connected by an equality.

### Definition

Given a type family `P : α → Type`, an equality `p : a = b`, and a term `x : P a`, we can transport `x` along `p` to get a term of type `P b`:

```lean
def transport {α : Type} {P : α → Type} {a b : α} (p : a = b) (x : P a) : P b :=
  match p with
  | rfl => x
```

### Examples

This operation is incredibly powerful and can be used to define many other operations. For example, we can use it to define vector transport. Given a vector `v : Vector α n` and an equality `eq : n = m`, we can transport `v` to a vector of length `m`:

```lean
def vec_transport {α : Type} {n m : Nat} (eq : n = m) (v : Vector α n) : Vector α m :=
  transport eq v
```

## Higher Identity Types

One of the most interesting aspects of identity types is that they can be iterated - we can have equalities between equalities!

### Iterated Identity Types

Given `p q : a = b`, we can form the type `p = q` of equalities between equalities:

```lean
def double_eq {α : Type} {a b : α} (p q : a = b) : Type :=
  p = q
```

### Paths Between Paths

These higher identity types give rise to a rich structure where we can talk about paths between paths:

```lean
-- A 2-path (path between paths)
def path_between_paths {α : Type} {a b : α} {p q : a = b} (r : p = q) :
  p = q := r
```

## Towards Homotopy Type Theory

Identity types provide the foundation for Homotopy Type Theory (HoTT), where types are viewed as spaces, terms as points, and equalities as paths.

### The Correspondence

| Type Theory     | Homotopy Theory |
| --------------- | --------------- |
| Type            | Space           |
| Term            | Point           |
| Identity        | Path            |
| Higher Identity | Higher Path     |

However, to go there we need to introduce more concepts like algebraic geometry, higher inductive types and univalence. We'll explore these in future chapters.

---

[Proofs - Introduction](Proofs.introduction.html)
