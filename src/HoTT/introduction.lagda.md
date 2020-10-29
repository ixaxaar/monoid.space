****

[Contents](contents.html)
[Previous](Algebra.real.html)
[Next](HoTT.identity.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Homotopy Type Theory](#homotopy-type-theory)
- [Intensional and Extensional Type Theories](#intensional-and-extensional-type-theories)
- [Univalence](#univalence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Homotopy Type Theory

```agda
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Types.product
open import Types.relations
open import Types.equality

module HoTT.introduction where
```

Homotopy type theory is a part of a mathematician's quest to have a formal language in which to write mathematics such that the correctness of the mathematics written can be automatically verified by a computer program. This mathematician, Vladimir Voevodsky, played a large part in formalizing homotopy type theory and lead the restructuring of mathematics based on this new foundation, called Univalent foundations, so that it is easier to implement and work consistently in these formal languages.

We are working in one such language, Agda, though Voevodsky had used a different one - [Coq](https://coq.inria.fr/). There are a few more of such languages called __Theorem Provers__, notably [Isabelle](https://isabelle.in.tum.de/), [Idris](https://www.idris-lang.org/), [Arend](https://arend-lang.github.io/) and [Lean](https://leanprover.github.io/).

# Intensional and Extensional Type Theories

Part of the technical problem that was faced, apart from the need for restructuring and refactoring all of mathematics, which needed HoTT as a solution, has to deal with how we define equivalences.

In the current system, if say we were to define two types, both representing natural numbers:

```agda
data ℕ₁ : Set where
  zero₁ : ℕ₁
  succ₁ : ℕ₁ → ℕ₁

data ℕ₂  : Set where
  zero₂ : ℕ₂
  succ₂ : ℕ₂ → ℕ₂
```

Now two objects, both representing `3`, will be considered different:

```agda
three₁ = succ₁ (succ₁ (succ₁ zero₁))
three₂ = succ₂ (succ₂ (succ₂ zero₂))
```

```haskell
eq : three₁ ≡ three₂
eq = refl
```

and the compiler throws the error:

```haskell
ℕ₂ !=< ℕ₁
when checking that the expression three₂ has type ℕ₁
```

In order to make these types equal, we have to define an equality type where we provide a proof that ℕ₁ and ℕ₂ are equal. This is the consequence of the flavor of type theory that we are using called "Intensional" type theory. In intensional type theory, one has to explicitly define all equivalences for all objects and some machinery for them to really work with these structures.

In the above example, we could capture equivalence of integers without much code, however this problem compounds itself as one builds higher structures, say a group of integers or a real number field. These equivalences can be captured by `Setoid`s which are basically objects along with their definition of equivalences "packaged together" so that their implementations can be hidden. However, like many such foundational patches, the final implementations result in a mess where the base definitions need additional machinery and one needs to be aware of these implementations anyway when constructing higher structures. Some areas of mathematics are notably hard, like defining real numbers. However, for all its shortfalls, an intensional system guarantees that the type checking is decidable.

In particular, intensional type theories lack:

1. **Functional extensionality**: Two functions that are pointwise equal are equal.
2. **Propositional extensionality**: Two propositions that are logically equivalent are equal.
3. **Quotients**: We can quotient (subset) a type by an equivalence relation.

The above can be technically handled by modeling Types using `Setoid`s instead of `Set`. However, if we need further extensionality by adding:

4. **Set extensionality**: Two sets are equal if they are in a one-to-one correspondence.

This creates a problem as two sets can be equal in many different ways. To account for this additional structure, we could model Types using `Groupoid`s (also known as a `Magma`) instead of `Setoid`s.

Another flavor of type theory, "extensional" defines equivalences as - things that behave the same way are equal (regardless of their internal implementations). This, in a way, provides a better set of abstractions for working with mathematics as in order to build towers of abstractions, one needs to hide implementation details. Otherwise imagine one needing to know the intel instruction set to build a website. The shortfall in the extensional system is that it is possible to define types that are not decidable. In other words, there is no difference between definitional and propositional equalities allowing cases where type checking will never terminate. Another problem here is that Set extensionality cannot be modeled.

As the extensional version has major drawbacks, there becomes a need for restructuring the modeling of equivalence in intensional type theory to build more extensionality along with cleaner and better abstracted implementations. This is where Homotopy Type Theory comes in.

# Univalence

Roughly speaking, the mathematical theory that models equality and equivalence of types using abstractions from homotopy theory is called Homotopy Type Theory (or HoTT in short). The "Univalence" axiom sits at the core of HoTT and hence, the resulting type theories that build on HoTT are called "univalent type theories" and the math implemented in such type theories "univalent mathematics".

<!-- outline further plan -->

---

[Identity Types and Paths](./HoTT.identity.html)
