****
[Contents](contents.html)
[Previous](Lang.debugging.html)
[Next](Types.universe.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)
  - [1. Foundations of Mathematics](#1-foundations-of-mathematics)
  - [2. Set Theory](#2-set-theory)
    - [2.1 Historical Context](#21-historical-context)
    - [2.2 Basic Concepts](#22-basic-concepts)
    - [2.3 Axioms of Set Theory](#23-axioms-of-set-theory)
    - [2.4 Example in Set Theory](#24-example-in-set-theory)
    - [2.5 Set Theory in Mathematics](#25-set-theory-in-mathematics)
  - [3. Type Theory](#3-type-theory)
    - [3.1 Historical Context](#31-historical-context)
    - [3.2 Basic Concepts](#32-basic-concepts)
    - [3.3 Example in Type Theory](#33-example-in-type-theory)
    - [3.4 Comparison with Set Theory](#34-comparison-with-set-theory)
    - [3.5 Applications in Computer Science](#35-applications-in-computer-science)
    - [3.6 Type Theory in Mathematics](#36-type-theory-in-mathematics)
  - [4. Advanced Concepts and Implications](#4-advanced-concepts-and-implications)
    - [4.1 Categorical Interpretations](#41-categorical-interpretations)
    - [4.2 Homotopy Type Theory](#42-homotopy-type-theory)
    - [4.3 Proof Assistants and Formal Verification](#43-proof-assistants-and-formal-verification)
    - [4.4 Dependent Types in Programming](#44-dependent-types-in-programming)
    - [4.5 Foundations of Mathematics Revisited](#45-foundations-of-mathematics-revisited)
    - [4.6 Future Directions](#46-future-directions)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Introduction

```agda
module Types.introduction where

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1. Foundations of Mathematics

Mathematics, as we know it today, rests upon foundations that have been carefully constructed and refined over centuries. These foundations provide a rigorous basis for mathematical reasoning and proof. Two of the most important foundational systems in modern mathematics are Set Theory and Type Theory.

## 2. Set Theory

### 2.1 Historical Context

Set Theory was developed in the late 19th and early 20th centuries, primarily by Georg Cantor, and later formalized by Ernst Zermelo and Abraham Fraenkel. It emerged as a response to the need for a rigorous foundation for mathematics, particularly in the face of paradoxes that had been discovered in naive approaches to mathematical reasoning.

### 2.2 Basic Concepts

At its core, Set Theory deals with collections of objects, called sets. The fundamental relation in Set Theory is membership, denoted by the symbol ∈. If an object x is a member of a set A, we write x ∈ A.

Key concepts in Set Theory include:

1. **Sets and Elements**: A set is a collection of distinct objects, called its elements or members.

2. **Subsets**: A set A is a subset of B (written A ⊆ B) if every element of A is also an element of B.

3. **Empty Set**: The set with no elements, denoted by ∅ or {}.

4. **Set Operations**:
   - Union `(A ∪ B)`: The set of all elements that are in A or B (or both).
   - Intersection `(A ∩ B)`: The set of all elements that are in both A and B.
   - Difference `(A \ B)`: The set of all elements in A that are not in B.

5. **Power Set**: The set of all subsets of a given set.

### 2.3 Axioms of Set Theory

The most commonly used axiomatic system for Set Theory is Zermelo-Fraenkel Set Theory with the Axiom of Choice (ZFC). Some key axioms include:

1. **Extensionality**: Two sets are equal if and only if they have the same elements.
2. **Pairing**: For any two sets, there exists a set containing exactly those two sets as elements.
3. **Union**: For any collection of sets, there exists a set that contains all elements that belong to at least one set in the collection.
4. **Power Set**: For any set A, there exists a set whose elements are all the subsets of A.
5. **Infinity**: There exists an infinite set.

### 2.4 Example in Set Theory

Let's consider a simple example:

Let $A = {1, 2, 3}$ and $B = {2, 3, 4}$

Then:
- $A ∪ B = {1, 2, 3, 4}$
- $A ∩ B = {2, 3}$
- $A \ B = {1}$
- The power set of A is ${{}, {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}}$

### 2.5 Set Theory in Mathematics

Set Theory provides a language and framework for defining and working with mathematical objects. For example:

- Natural numbers can be defined using sets (e.g., the von Neumann ordinals).
- Functions can be defined as special kinds of sets (specifically, as sets of ordered pairs).
- Mathematical structures like groups, rings, and topological spaces are defined in terms of sets with certain properties.

Set Theory has been incredibly successful as a foundation for mathematics, allowing for rigorous definitions and proofs across various mathematical disciplines.

## 3. Type Theory

### 3.1 Historical Context

Type Theory was initially developed by Bertrand Russell in the early 20th century as a response to paradoxes discovered in Set Theory. It was later refined and expanded by mathematicians and logicians such as Alonzo Church, Per Martin-Löf, and others. Martin-Löf's Intuitionistic Type Theory, developed in the 1970s, has been particularly influential in computer science and constructive mathematics.

### 3.2 Basic Concepts

Type Theory is a formal system in which every term has a "type". This concept of types is similar to, but more general than, the notion of sets. Key concepts in Type Theory include:

1. **Types and Terms**: Every expression in the theory is a term, and every term has a type. We write "t : T" to mean "term t has type T".

2. **Functions**: Functions are first-class citizens in Type Theory. A function f from type A to type B is written as `f : A → B`.

3. **Dependent Types**: Types can depend on terms. For example, we can have a type `Vec(n)` of vectors of length n, where n is a term of type `Nat`.

4. **Propositions as Types**: In many type theories, propositions (logical statements) are represented as types. A proof of a proposition is a term of the corresponding type.

5. **Computation Rules**: Type Theory includes rules for computing with terms, similar to evaluation rules in programming languages.

### 3.3 Example in Type Theory

Let's consider a simple example in Agda, a programming language based on Type Theory:

```agda
data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

_ : not (not true) ≡ true
_ = refl
```

Here, we define a type `Bool` with two constructors, a function `not` that operates on `Bool`, and a proof that `not (not true)` equals `true`.

### 3.4 Comparison with Set Theory

While Set Theory and Type Theory can both serve as foundations for mathematics, they have some key differences:

1. **Objects vs. Terms**: In Set Theory, we work with sets and their elements. In Type Theory, we work with types and terms.

2. **Membership vs. Typing**: Set Theory uses the membership relation (∈), while Type Theory uses typing judgments (:).

3. **Functions**: In Set Theory, functions are special kinds of sets. In Type Theory, functions are primitive notions.

4. **Proof Relevance**: Type Theory is often "proof relevant", meaning that the specific proof of a proposition matters, not just its truth value.

5. **Constructivity**: Many type theories are constructive, rejecting the law of excluded middle and the axiom of choice, which are standard in classical Set Theory.

### 3.5 Applications in Computer Science

Type Theory has found extensive applications in computer science:

1. **Programming Language Design**: Many modern programming languages incorporate ideas from Type Theory in their type systems.

2. **Formal Verification**: Type Theory provides a basis for proving properties of programs and verifying their correctness.

3. **Proof Assistants**: Software like Coq, Agda, and Lean, based on Type Theory, allow for computer-assisted theorem proving.

4. **Foundations of Computer Science**: Type Theory provides a theoretical foundation for understanding computation and programming languages.

### 3.6 Type Theory in Mathematics

While Set Theory remains the most common foundation for mathematics, Type Theory offers some advantages:

1. **Constructive Mathematics**: Type Theory naturally supports constructive approaches to mathematics.

2. **Computational Content**: Proofs in Type Theory often have direct computational interpretations.

3. **Higher-Order Logic**: Type Theory easily accommodates higher-order logic, which can be more expressive than first-order logic used in Set Theory.

4. **Homotopy Type Theory**: Recent developments have connected Type Theory with modern areas of mathematics like homotopy theory.

## 4. Advanced Concepts and Implications

### 4.1 Categorical Interpretations

Both Set Theory and Type Theory have important connections to Category Theory, a branch of mathematics that deals with abstract structures and relationships between them.

1. **Set Theory and Categories**:
   - The category Set, whose objects are sets and morphisms are functions, is a fundamental example in category theory.
   - Many set-theoretic constructions have categorical generalizations (e.g., products, coproducts, exponentials).

2. **Type Theory and Categories**:
   - There's a deep connection between Type Theory and Cartesian closed categories.
   - Each type theory gives rise to a category, where types are objects and terms are morphisms.

### 4.2 Homotopy Type Theory

Homotopy Type Theory (HoTT) is a recent development that connects Type Theory with abstract homotopy theory.

1. **Univalence Axiom**: This axiom in HoTT states that isomorphic types are equal, providing a powerful principle for reasoning about equivalence.

2. **Inductive Types with Recursion**: While Agda doesn't directly support higher inductive types, we can demonstrate similar concepts using regular inductive types and recursive functions.

Example (Modulo 2):

```agda
data Mod2 : Set where
  zero : Mod2
  one  : Mod2

-- Function that cycles through the two points
next : Mod2 → Mod2
next zero = one
next one  = zero

-- Proof that applying 'next' twice gets us back to the start
open import Relation.Binary.PropositionalEquality

next-cycle : ∀ (x : Mod2) → next (next x) ≡ x
next-cycle zero = refl
next-cycle one  = refl

-- This represents a simple cyclic structure with two points
-- and a function that moves between them
```

### 4.3 Proof Assistants and Formal Verification

The development of proof assistants based on Type Theory has significant implications for mathematics and computer science.

1. **Formalized Mathematics**: Large parts of mathematics have been formalized in systems like Coq, Lean, and Agda.

2. **Software Verification**: Type Theory-based systems are used to verify the correctness of critical software systems.

Example (CompCert, a verified C compiler):

```coq
Theorem compiler_correctness:
  forall (p: Clight.program) (b: behavior),
  Clight.semantics p b ->
  Asm.semantics (compile p) b.
```

This theorem states that the compiled assembly code has the same behavior as the original C code.

### 4.4 Dependent Types in Programming

Dependent types, a key feature of many Type Theories, are finding their way into programming languages.

1. **Precision**: Dependent types allow for more precise specifications of program behavior.

2. **Proof-Carrying Code**: Programs can carry proofs of their own properties.

Example in Agda:

```agda
_++_ : ∀ {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- The type system ensures that vector lengths are correctly maintained
```

### 4.5 Foundations of Mathematics Revisited

The development of Type Theory and its variants has led to a reconsideration of the foundations of mathematics.

1. **Constructive Mathematics**: Type Theory naturally supports constructive approaches, which some argue provide a more computationally meaningful foundation.

2. **Univalent Foundations**: The Univalent Foundations program, based on Homotopy Type Theory, proposes a new foundation for mathematics that treats isomorphic structures as genuinely equal.

3. **Set Theory vs. Type Theory**: While Set Theory remains dominant, Type Theory offers advantages in certain areas, particularly those close to computation and constructive reasoning.

### 4.6 Future Directions

1. **Computational Trinitarianism**: The idea that logic, type theory, and category theory are deeply connected and can be seen as different views of the same underlying concepts.

2. **Quantum Computing**: Type theories for quantum computation are an active area of research.

3. **Machine-Assisted Mathematics**: As proof assistants become more powerful, they may play an increasingly important role in mathematical research and education.

****
[Universes and families](./Types.universe.html)
