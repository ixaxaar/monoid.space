****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Flavors of Type Theory](#flavors-of-type-theory)
- [Axiom K](#axiom-k)
- [Homotopy Type Theory](#homotopy-type-theory)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


```agda
module Types.variations where
```

# Flavors of Type Theory

All propositions are essentially identity types. However, one may ask a very fundamental question - are all identities the same?. [In a previous part](./Lang.proofsAsData.html) we looked at how the termination of computation in constructive proofs serves as a marker of falsity of the proposition, in other words, a proof that fails to terminate fails to prove the proposition. Thus, we rely on the decidability of termination of computation for type checking. We could thus assume that all identity proofs are unique or not, depending upon whether we would want to factor in the possibility of non-terminating proofs. This makes type theory itself classifiable into two categories: intensional type theory and extensional type theory.

Extensional type theory does not distinguish between definitional and propositional equalities. Since propositional equalities might involve non-terminating proofs, extensionality brings in undecidability. However, computationally equal objects are seen as equal without further proof, such as `a ≡ a = refl` i.e. identities are unique and all of them are the same thing (equal).

Intentional type theory is where propositional equality requires proof and type checking and specifically termination checking is possible (and required). The consquence of this is that identity types are not necessarily propositions, or in more practical terms, identities are not unique and equal - one has to prove them to be.

# Axiom K

Axiom K is an identity eliminator which when defined can be used as an elimination rule to prove all identities as equal. It is also called **principle of uniqueness of identity proofs**.


https://github.com/agda/agda/issues/865

# Homotopy Type Theory

An alternative to axiom K and assuming the uniqueness of all identities is considdering identities as paths, which are objects of Homotopy theory from Algebraic Geometry. We could then used homotopy theory to model all types as ∞-groupoids and work with some non-trivial interesting structures rather than the dead-end that is axiom K. We shall develop this theory later in this work.

****
[Introduction to Logic](./Logic.introduction.html)
