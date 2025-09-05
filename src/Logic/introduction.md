---

[Contents](contents.html)
[Previous](Types.identity.html)
[Next](Logic.logicBasics.html)

# Introduction to Logic and Boolean Algebra

---

- [Foundations of Logic](#foundations-of-logic)
- [Classical Logic vs. Constructive Logic](#classical-logic-vs-constructive-logic)
- [Propositions as Types](#propositions-as-types)
- [The Curry-Howard Correspondence](#the-curry-howard-correspondence)
- [Logic in Type Theory](#logic-in-type-theory)
- [Computational Logic](#computational-logic)
- [Why Study Logic in Lean?](#why-study-logic-in-lean)

```lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Basic
```

Logic forms the bedrock of mathematics, computer science, and rational reasoning itself. While often introduced through truth tables and symbolic manipulation, logic in type theory—particularly as implemented in Lean—reveals a profound connection between logical reasoning and computation. This chapter explores how logical concepts emerge naturally from type-theoretic foundations, providing both computational tools and rigorous mathematical structures.

## Foundations of Logic

Logic, in its most fundamental sense, concerns itself with the principles of valid reasoning. Classical logic, developed over millennia, deals with statements that are either true or false, and provides rules for combining and manipulating these statements to derive new truths. Boolean algebra, named after George Boole, formalizes this classical logic through algebraic structures.

However, type theory offers a different perspective on logic—one that emphasizes **construction** over **truth values**. Instead of asking "is this statement true or false?", type theory asks "can we construct evidence for this statement?" This shift in perspective leads to what we call **constructive logic** or **intuitionistic logic**.

## Classical Logic vs. Constructive Logic

The distinction between classical and constructive logic is crucial for understanding logic in type theory:

**Classical Logic:**

- Every statement is either true or false (law of excluded middle)
- We can prove something exists by showing its non-existence leads to contradiction
- Double negation elimination: `¬¬P → P`

**Constructive Logic:**

- To prove something exists, we must construct an example
- We cannot freely use the law of excluded middle
- Emphasis on computational content of proofs

In Lean, we work primarily with constructive logic, though classical principles can be imported when needed:

```lean
-- Constructive approach: to prove existence, provide a witness
example : ∃ n : Nat, n > 5 := ⟨6, by simp⟩

-- Classical approach (when imported)
-- example : ∀ P : Prop, P ∨ ¬P := Classical.em
```

## Propositions as Types

One of the most remarkable insights in type theory is the **propositions-as-types** principle. This identifies:

- **Propositions** (logical statements) with **types**
- **Proofs** (justifications) with **terms** (inhabitants of types)
- **Proof construction** with **program construction**

This means that proving a theorem is equivalent to writing a program of a specific type:

```lean
-- The proposition "if P then P" corresponds to the function type P → P
def identity_proof (P : Prop) : P → P := fun p => p

-- The proposition "P and Q implies P" corresponds to P ∧ Q → P
def and_left (P Q : Prop) : P ∧ Q → P := fun ⟨p, q⟩ => p
```

## The Curry-Howard Correspondence

The Curry-Howard correspondence formalizes the connection between logic and computation:

| Logic | Computation |
|-------|-------------|
| Proposition | Type |
| Proof | Program |
| True proposition | Inhabited type |
| False proposition | Empty type |
| Implication P → Q | Function type P → Q |
| Conjunction P ∧ Q | Product type P × Q |
| Disjunction P ∨ Q | Sum type P ⊕ Q |

This correspondence means that logical reasoning becomes type-directed programming, and vice versa.

## Logic in Type Theory

In Lean's type theory, logic is not a separate system but emerges naturally from the type-theoretic foundations:

```lean
-- Conjunction is product types
#check And -- And : Prop → Prop → Prop
#check And.intro -- And.intro : ∀ {a b : Prop}, a → b → a ∧ b

-- Disjunction is sum types
#check Or -- Or : Prop → Prop → Prop
#check Or.inl -- Or.inl : ∀ {a b : Prop}, a → a ∨ b

-- Negation is defined in terms of falsehood
#check Not -- Not : Prop → Prop
-- ¬P is defined as P → False

-- Implication is function types (built-in)
#check (· → ·) -- Prop → Prop → Prop
```

## Computational Logic

Unlike classical logic, logic in type theory has **computational content**. Every proof is actually a program that can be executed:

```lean
-- A constructive proof of P ∨ ¬P → Q ∨ ¬Q
def decidable_transfer (P Q : Prop) : P ∨ ¬P → Q ∨ ¬Q :=
  fun h => by
    cases h with
    | inl hp =>
      -- If we have P, we need to decide about Q
      -- In general, we cannot decide Q from P alone
      sorry  -- This shows we cannot prove this constructively in general
    | inr hnp =>
      -- If we have ¬P, we still cannot decide about Q
      sorry

-- However, for decidable propositions, we can:
def decidable_transfer_bool (b c : Bool) : b = true ∨ b = false → c = true ∨ c = false :=
  fun _ => by
    cases c with
    | true => exact Or.inl rfl
    | false => exact Or.inr rfl
```

## Why Study Logic in Lean?

Studying logic through Lean offers several advantages:

1. **Rigor**: Every logical step must be justified formally
2. **Computability**: Proofs are programs that can be executed
3. **Verification**: The type checker ensures correctness
4. **Expressiveness**: Can handle complex mathematical reasoning
5. **Foundations**: Provides deep understanding of logical principles

This computational view of logic enables us to:

- Write programs that are provably correct
- Verify mathematical theorems mechanically
- Understand the constructive content of classical proofs
- Build reliable software systems

The following sections will explore these ideas in detail, showing how fundamental logical concepts emerge from and are implemented in type theory.

---

[Boolean Algebra](./Logic.logicBasics.html)
