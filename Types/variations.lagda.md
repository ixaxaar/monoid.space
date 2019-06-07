****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Flavors of Type Theory](#flavors-of-type-theory)
- [Identity Elimination](#identity-elimination)
- [Axiom K](#axiom-k)
- [Homotopy Type Theory](#homotopy-type-theory)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


```agda
module Types.variations where

open import Types.equality
```

# Flavors of Type Theory

All propositions are essentially identity types. However, one may ask a very fundamental question - are all identities the same?. [In a previous part](./Lang.proofsAsData.html) we looked at how the termination of computation in constructive proofs serves as a marker of falsity of the proposition, in other words, a proof that fails to terminate fails to prove the proposition. Thus, we rely on the decidability of termination of computation for type checking. We could thus assume that all identity proofs are unique or not, depending upon whether we would want to factor in the possibility of non-terminating proofs. This makes type theory itself classifiable into two categories: intensional type theory and extensional type theory.

**Extensional type theory** does not distinguish between definitional and propositional equalities. Since propositional equalities might involve non-terminating proofs, extensionality brings in undecidability. However, computationally equal objects are seen as equal without further proof, such as `a ≡ a = refl` i.e. identities are unique and all of them are the same thing (equal).

**Intentional type theory** is where propositional equality requires proof and type checking and specifically termination checking is possible (and required). The consquence of this is that identity types are not necessarily propositions, or in more practical terms, identities are not unique and equal - one has to prove them to be.

# Identity Elimination

The identity type for any two objects $x, y ∈ A$ if of the form $x =_A y$ represents the type of the proof that x is equal to y. The proof is equivalent to demonstrating that the type is inhabited, i.e. an object of that type can be created. The elimination rule on identity types, called the **J rule** looks like:

```agda
J : {A : Set} →
        (P : (x y : A) → x ≡ y → Set) 
        → ((x : A) → P x x refl) 
        → (x y : A) 
        → (x≡y : x ≡ y) 
        → P x y x≡y
J P p x .x refl = p x
```

where `P` is a predicate that it holds for any two objects `x, y` of type A which are propositionally equal. `p` is the a form that constructs `P` for the case when x and y are both the same object `x` and reflexivity `refl`  of the propositional equality `≡`. The rule states that any identity `x≡y` can be proven using the reflexivity of the propositionlly equal objects `x` and `y`. Thus the J rule can be used with reflexivity `refl` or `x≡x` and `y≡y` to prove the equality of all identity types, including `x≡y`.

![Figure 1: J rule](./path-induction.png)

# Axiom K

Axiom K is an identity eliminator which when defined can be used as an elimination rule to prove all identities as equal. It is also called **principle of uniqueness of identity proofs**.

```haskell
K : {A : Set} {x : A} 
        (P : x ≡ x → Set) 
        → P refl 
        → (x≡x : x ≡ x) 
        → P x≡x
K P p refl = p
```

Note that without the `--with-K` command-line or the `{-# OPTIONS --with-K #-}` inline option, agda will not compile axiom K. This is because we cannot assume every `x ≡ x` to be equal to `refl`, or that all identity propositions can be proven by `refl`.

```math
x≡x : x ≡ x =?= refl
```

The error message explains this rather clearly:

```md
I'm not sure if there should be a case for the constructor refl,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  x ≟ x
Possible reason why unification failed:
  Cannot eliminate reflexive equation x = x of type A because K has
  been disabled.
```

# Homotopy Type Theory

An alternative to axiom K and assuming the uniqueness of all identities is considering identities as paths, which are objects of Homotopy theory from Algebraic Geometry. We could then used homotopy theory to model all types as ∞-groupoids and work with some non-trivial interesting structures rather than the dead-end that is axiom K. We shall develop this theory later in this work.

****
[Introduction to Logic](./Logic.introduction.html)
