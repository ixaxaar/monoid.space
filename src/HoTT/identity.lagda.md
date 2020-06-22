****
[Contents](contents.html)
[Previous](HoTT.introduction.html)
[Next](HoTT.paths.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Homotopy Theory](#homotopy-theory)
  - [Overview](#overview)
  - [Paths](#paths)
  - [Homotopy](#homotopy)
  - [Fundamental group](#fundamental-group)
  - [∞-groupoid](#-groupoid)
  - [Induction principle](#induction-principle)
- [The Identity Type or Path](#the-identity-type-or-path)
  - [Path Induction](#path-induction)
  - [Dependent Paths](#dependent-paths)
  - [API](#api)
    - [Composition](#composition)
    - [Associativity](#associativity)
    - [Inverse](#inverse)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Homotopy Theory

## Overview

The notion of "space" generally invokes thought of a geometrical structure. The usual spaces one might have encountered are Euclidean spaces which fit this intuition. In Algebraic Geometry (of which Homotopy Theory is a part), however, the notion of a space is abstract, and as a consequence while the well known spaces fit into the definition, so do many other kinds of objects.

1. Formally, a topological space is a set of points endowed with an additional structure called a "topology".
2. A path is a line joining two points in a topological space. These are also called as continuous map.
3. There can be multiple paths between any two points, hence there is a notion of an equivalence between paths, called "homotopy".

Homotopy Theory studies the characteristics of homotopies of paths.

## Paths

Technically, in a topological space 𝕏, a path between two points `x` and `y` ∈ 𝕏 can be represented as a function `f` that takes a continuous value `t` and returns a point on the path `f(t)` such that the first point is `x` $f(0) = x$ and the last point is `y` $f(1) = y$ and $0 ≤ t ≤ 1$. Paths thus represented are continuous functions.

![Figure 1: Path](/artwork/pathType.png)

## Homotopy

We could take any two paths between the same points and stretch / squeeze one path into another. This process can be used to capture relationships between two paths and is called _homotopy_. More formally,

A _homotopy_ between two paths `p(t)` and `q(t)` is defined as a continuous function `H(t, h)` such that:

- $H(t, 0) = p(t)$
- $H(t, 1) = q(t)$
- $H(0, h) = x$
- $H(1, h) = y$

There can exist multiple paths between two objects and hence multiple homotopies between them. Homotopies can be thought of as 2-dimensional paths or path-of-path if paths are 1-dimensional paths.

![Figure 2: Homotopy](/artwork/homotopy.png)

## Fundamental group

Two homotopies `H1` and `H2` can themselves be called equal if $H(0, h) = H(1, h) = x₀$, i.e. if `x` and `y` are the same point. We can use this equivalence relation and the fact that homotopies have inverses, to build a group structure around these homotopies, called as the _fundamental group_.

Formally, for any point `x` in a topological space 𝕏, the fundamental group is the group over
- Homotopy equivalence classes as objects at point `x₀` denoted $π₁(𝕏, x₀)$.
- A product operation defined on these equivalence classes a such:

Given two paths / loops (γ₁ and γ₂), their product is:

```math
γ₁ ♢ γ₂ : [1,0] → 𝕏
γ₁ ♢ γ₂ = λ t → if (0 < t < 1÷2) γ₁ (2 * t) else  γ₂ (2 * t - 1)
```

Thus the loop `γ₁ ♢ γ₂` first follows the loop γ₁ with "twice the speed" and then follows γ₂ with "twice the speed". It is to be noted that we consider all equivalence classes of loops instead of considering all loops as loops belonging to one equivalence class can be treated as the same.

![Figure 3: Fundamental Group](/artwork/fundamental_group.png)




## ∞-groupoid

We can have n-dimensional paths from n-equalities or homotopies of homotopies of homotopies of homotopies and so on. Such a structure of infinite levels of homotopies with points followed by paths as base is called the _∞-groupoid_. Every space can be turned into its ∞-groupoid and then homotopy theory can be applied to it as well as every ∞-groupoid can yield a fundamental group. This fact connects algebraic topology (which uses the fundamental group) and category theory (which builds on the ∞-groupoid).

In HoTT, each type can be represented as an ∞-groupoid. Each pair of objects `x` and `y` of a type can have an typelevel equality type $x ≡_A y$. For example in python:

```python
a = 3
b = 4

type(a) ≡ type(b)
```

These equalities can have further equalities $(x_1 ≡_A y_1) ≡_{(x ≡_A y)} (x_2 ≡_A y_2)$. Note: higher levels cannot be done trivially in python.

## Induction principle

The induction principle is central to deriving all basic constructions for HoTT. Stated simply, if for every pair of objects `x` and `y` of type `A`

- the equality type $≡_A$ between `x` and `y` exists everytime `x` and `y` are equal
- for every `x ∈ A`, the equalities $x ≡_A x$ are reflexive
  then for a proposition `C` which depends upon the equality $x ≡_A y$, it turns out that it is sufficient to prove `C` for all cases where $x ≡_A x$ alone and it becomes automatically applicable for cases for all $x ≡_A y$.


# The Identity Type or Path

```agda
module HoTT.identity where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product using (Σ; _,_; fst; snd)
```

Identity types in type theory are the type of all equality types. An equality type between `x, y ∈ A` can be considered as a path from `x` to `y`. All of such paths share a relation amongst each other.

```agda
data Identity {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  identity : Identity x x
```

Identity types are also known as `Path`s.

```agda
Path = Identity
```

We define equality itself as a path:

![Figure 1: Path](./path.png)

```agda
_==_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_==_ = Path
```

This forms the base of HoTT wherein we rebuild pretty much everything on the above structure.

## Path Induction

![Figure 2: Path Induction](./path-induction.png)

An inductive type is a type with a recursive constructor that can be used to successvely obtain elements of that type. However, though this definition "generally" works, there are more technical ones available [here for example](https://github.com/HoTT/book/issues/460).

The family of identity types is freely generated from elements of the form `identity: x == x`. Such a family's constructor is a dependent type `C : {x y : A} → x == y → Set ℓ₂`, which depends on two objects `x` and `y` of type `A` and an equality type or path between the two objects, can also be written as $Π(x, y, x ==_A y)$. Let `c` be a function that applies an object `x` to the constructor `C` and its `identity` equality type to obtain the path from `x → x`.

```agda
path-induction : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
        (C : {x y : A} → x == y → Set ℓ₂)
        → (c : (x : A) → C {x} {x} identity)
        → ({x y : A} (p : x == y) → C p)
path-induction C c {x} identity = c x

path-induction⁻¹ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
        (C : {x y : A} → y == x → Set ℓ₂)
        → (c : (x : A) → C {x} {x} identity)
        → ({x y : A} (p : y == x) → C p)
path-induction⁻¹ C c {x} identity = c x
```

```agda
path-induction-v2 : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
        (C : {x y : A} → Path x y → Set ℓ₂)
        → (c : (x : A) → C {x} {x} identity)
        → ({x y : A} (p : Path x y) → C p)
path-induction-v2 C c {x} identity = c x

path-induction-v2⁻¹ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
        (C : {x y : A} → Path y x → Set ℓ₂)
        → (c : (x : A) → C {x} {x} identity)
        → ({x y : A} (p : Path y x) → C p)
path-induction-v2⁻¹ C c {x} identity = c x
```

![Figure 3: Induction](./induction.png)
<!-- ![Figure 0: Abstract-path-induction](./abstract-path-induction.png) -->

This induction property could also be interpreted as, for an inductively defined identity type family, the entire family can be completely specified with just the elements `identityₓ`. Thus, since C(x, x) holds on all x ∈ A, if we are given x == y, then C(x, y) must hold. Getting the understanding of the induction principle can be tricky as the ideas around it are still in argument / development. Here are a few resources [1](https://planetmath.org/1121pathinduction) [2](https://math.stackexchange.com/questions/1667582/how-am-i-to-interpret-induction-recursion-in-type-theory) [3](https://cs.stackexchange.com/questions/28701/is-path-induction-constructive?newreg=3d0d333631c24ef0a8737f6072c14278).

## Dependent Paths

A dependent path describes the notion of equality preserving functions. It states that given a dependent type $Π(a, b)$ and the equality type between them, there exists a path $F(a) → F(b)$.

![Figure 4: Dependent Path](./dependent_path.png)

```agda
DependentPath : ∀ {i j} {A : Set i} {x y : A}
  → (F : A → Set j)
  → (p : x == y)
  → (a : F x)
  → (b : F y)
  → Set j
DependentPath F identity a b = (a == b)
```

## API

### Composition

Paths can be composed or concatenated (both from left and right):

```agda
_∘_ : ∀ {ℓ} {A : Set ℓ} {x y z : A}
        → (x == y)
        → (y == z)
        → (x == z)
identity ∘ k = k
```

```agda
_∘ₗ_ : ∀ {ℓ} {A : Set ℓ} {x y z : A}
        → (x == y)
        → (y == z)
        → (x == z)
k ∘ₗ identity = k
```

The above concatenations imply the same thing:

```agda
path-concat-equals-left : ∀ {ℓ} {A : Set ℓ} {x y z : A}
        → (a : x == y)
        → (b : y == z)
        → Identity (a ∘ b) (a ∘ₗ b)
path-concat-equals-left identity identity = identity

path-concat-equals-right : ∀ {ℓ} {A : Set ℓ} {x y z : A}
        → (a : x == y)
        → (b : y == z)
        → Identity (a ∘ₗ b) (a ∘ b)
path-concat-equals-right identity identity = identity
```

### Associativity

Path concatenation is associative:

```agda
path-concat-assoc : ∀ {ℓ} {A : Set ℓ} {w x y z : A}
        → (a : w == x)
        → (b : x == y)
        → (c : y == z)
        → Identity ((a ∘ b) ∘ c) (a ∘ (b ∘ c))
path-concat-assoc identity identity identity = identity
```

and similar for left and mixed `∘` and `∘ₗ` cases.

### Inverse

As paths are identities, they also have inverses. For every type `A` and every `x, y ∈ A`, there exists a function:

$f : (x == y) → (y == x)$

```agda
_⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A}
        → (x == y)
        → (y == x)
identity ⁻¹ = identity
```

****
[Back to Contents](./contents.html)

