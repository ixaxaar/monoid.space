****
[Contents](contents.html)
[Previous](Types.identity.html)
[Next](Types.tactics.html)  <!-- Assuming the next chapter is on Tactics -->

# Introduction

****

- [Introduction](#introduction)
    - [Propositions as Types](#propositions-as-types)
    - [Proofs as Terms](#proofs-as-terms)
    - [Basic Tactics](#basic-tactics)
        - [`rfl`](#rfl)
        - [`intro`](#intro)
        - [`apply`](#apply)
        - [`exact`](#exact)
        - [`have`](#have)
        - [`let`](#let)
        - [Rewriting with `rw`](#rewriting-with-rw)
    - [Example Proofs](#example-proofs)
        - [Equality](#equality)
        - [Logical Connectives](#logical-connectives)
            - [Implication](#implication)
            - [Conjunction](#conjunction)
            - [Disjunction](#disjunction)
            - [Negation and False](#negation-and-false)
    - [Interacting with Lean](#interacting-with-lean)
        - [Info View](#info-view)
    - [Structuring Proofs](#structuring-proofs)
    - [Automated Tactics (Brief Introduction)](#automated-tactics-brief-introduction)

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Basic
```

In previous chapters, we've seen that types in Lean can represent mathematical objects, data structures, and even propositions (statements that can be true or false). We've hinted at the idea of proofs being terms of these propositional types, specifically in the context of identity types as paths between terms (where each of these terms is a proof).

Theorem proving in Lean is a process of constructing **terms of propositional types** to prove theorems. This is done using a combination of tactics that manipulate the proof state, which consists of goals (propositions to be proved) and hypotheses (assumptions that can be used in the proof). These terms are the formal, machine-checkable proofs of the propositions. Once Lean accepts a proof, it will also type-check the proof.

## Propositions as Types

In type theory, propositions are types. A proposition is a type with only one inhabitant (a term of that type) if it is true, and no inhabitants if it is false. For example, the proposition `2 + 2 = 4` is a type with one term, `rfl`, which is the proof that `2 + 2 = 4`.  If the proposition is false, the type will have no terms, as its simply impossible to construct such a term.

```lean
def proof_of_2_plus_2 : 2 + 2 = 4 := rfl
```

Let's break this down and look at it in more detail:

A **proposition** is a statement that can be either true or false. Examples:
1.   "2 + 2 = 4"
1.   "All cats are mammals."
1.   "x > 5" (where 'x' is a variable)

In type theory (and in Lean), propositions are treated as types. These types are called **propositional types**. The specific type that represents propositions in Lean is called `Prop`. So, instead of just *saying* "2 + 2 = 4" is a proposition, we can say it's a *type* (of type `Prop`).  In Lean:

```lean
#check 2 + 2 = 4  -- Output: 2 + 2 = 4 : Prop
```

This `#check` command confirms that the expression `2 + 2 = 4` has the type `Prop`, meaning it's a propositional type.

In type theory, a **term** is an inhabitant of a type. It's a specific value or expression that belongs to that type.  Think of it like this:

1.   `Nat` is a type (the type of natural numbers).
1.   `5` is a term of type `Nat`.
1.   `"hello"` is a term of type `String`.
1.   `true` is a term of type `Bool`.

**Terms *of* Propositional Types:**

If a proposition is a *type*, what does it mean to have a *term* of that type? -- A term of a propositional type is a *proof* of that proposition. If you can construct a term whose type is a particular proposition, you have *proven* that proposition. If you *cannot* construct such a term, the proposition is considered unproven (or, in some cases, false).

Let's see some examples:

**Example 1: A true proposition**

```lean
def my_proof : 2 + 2 = 4 := rfl
#check my_proof  -- Output: my_proof : 2 + 2 = 4
```

*   `2 + 2 = 4` is the propositional type (a proposition).
*   `my_proof` is a term of that type.
*   `rfl` is the actual proof (it says "2 + 2 = 4 by definition").  `rfl` is a term, and that's the term we're assigning to `my_proof`.
*   Because we were able to construct the term `my_proof`, we have proven the proposition `2 + 2 = 4`.

**Example 2: An implication**

```lean
def add_one_increases (n : Nat) : n < n + 1 := Nat.lt_succ_self n
#check add_one_increases  -- Output: add_one_increases : ∀ (n : ℕ), n < n + 1
```
Here, we have the following:
* The propositional type is `∀ (n: Nat), n < n+1`, this means "for all natural numbers, n will be less than n+1", a true statement.
* Then, using the already defined `Nat.lt_succ_self` we define a function to prove this proposition.

**Example 3: An uninhabited proposition (no term)**

We can state the proposition `1 = 0`, but we can't create a term of that type (unless our logic is inconsistent!).

```lean
#check 1 = 0   -- Output: 1 = 0 : Prop
--  We can't write:  def a_proof : 1 = 0 := ...  (There's nothing we can put here)
```

"Terms of propositional types" means "proofs of propositions, represented as inhabitants of the types that represent those propositions."  The ability to treat propositions as types and proofs as terms is a fundamental aspect of type theory and is what makes Lean a powerful tool for both programming and formal verification. It blurs the line between data and proof, making them aspects of the same underlying concept: terms inhabiting types. This is the essence of the "propositions as types" correspondence.

Propositions can be combined using logical connectives like `∧` (and), `∨` (or), `→` (implies), and `¬` (not). Propositions can also be quantified over types or values using `∀` (for all) and `∃` (there exists). Thus, proving a theorem in Lean is akin to constructing a term of a certain type, which is the proposition to be proved.

## Proofs as Terms

The statement `def proof_of_2_plus_2 : 2 + 2 = 4 := rfl` is simultaneously:

*   A *definition* of a term named `proof_of_2_plus_2`.
*   A *theorem* stating that `2 + 2 = 4`.
*    A *proof*.

The *type* of `proof_of_2_plus_2` is `2 + 2 = 4`, which is a proposition.  The *term* `rfl` is the proof itself.

## Basic Tactics

Tactics are commands that instruct Lean on how to construct a proof term. They manipulate the *proof state*, which consists of:

*   **Goals:**  The propositions we're currently trying to prove.
*   **Hypotheses:** Assumptions we can use in the proof.

A proof starts with an initial goal (the theorem we want to prove) and ends when all goals have been closed (proven). A proof may involve multiple subgoals, each requiring its own proof, just like computer programs can be broken down into smaller functions and combined.

### `rfl`

We've already seen `rfl`. It proves goals that are *definitionally equal* (equal by computation).

```lean
example : 2 + 2 = 4 := rfl
```

### `intro`

The `intro` tactic (short for "introduce") introduces a new hypothesis.  It's used when the goal is an implication (`A → B`) or a universal quantification (`∀ x, ...`).

```lean
example : ∀ x : Nat, x ≤ x + 1 := by
  intro x  -- Introduce 'x' as a new hypothesis (a natural number)
  apply Nat.le_add_right  -- Use a lemma from the library
```

Here, the initial goal is `∀ x : Nat, x ≤ x + 1`.  `intro x` changes the goal to `x ≤ x + 1`, with `x : Nat` as a hypothesis.

Nat.le_add_right is a lemma that states `a ≤ a + b` for any natural numbers `a` and `b` and is proved in the library like this:

```lean
theorem Nat.le_add_right (a b : Nat) : a ≤ a + b := by
  induction b with
  | zero => rfl
  | succ n ih => exact Nat.succ_le_succ ih

theorem Nat.succ_le_succ {a b : Nat} (h : a ≤ b) : a + 1 ≤ b + 1 := by
  induction h with
  | zero => rfl
  | succ h ih => exact Nat.succ_le_succ ih
```

As can be seen from the proof, `Nat.le_add_right` is proved by induction on `b` and `Nat.succ
_le_succ` is proved by induction on `h`.

### `apply`

The `apply` tactic tries to "match" the current goal with the conclusion of a theorem or lemma.

```lean
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans h1 h2  -- Use the transitivity of ≤
```

The goal is `a ≤ c`. `apply Nat.le_trans` changes the goal to proving two subgoals: `a ≤ b` and `b ≤ c`, which are exactly our hypotheses.

### `exact`

Use `exact` when hypotheses are present that directly address the goal:

```lean
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans
  exact h1
  exact h2
```

### `have`

The `have` tactic introduces a new subgoal, proves it, and then adds the proven statement as a hypothesis to the main goal.

```lean
example (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
  have h : 2 * a * b = a * b + a * b := by
    rw [mul_comm, ← two_mul, mul_comm]
  rw [Nat.mul_self_add_mul, h, ← Nat.add_assoc, ← Nat.add_assoc, Nat.add_assoc (a*a) (a*b)]
  rfl
```

### `let`

The `let` tactic introduces a *local definition*. This is useful for giving names to intermediate terms and breaking down complex expressions.

```lean
example (x y : Nat) : (x + y) + (x + y) = 2 * (x + y) := by
  let z := x + y
  rw [← two_mul]
  rfl
```

### Rewriting with `rw`

The `rw` tactic (rewrite) uses an equality to replace one side of the equality with the other in the goal.
```lean
example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]
```
`rw [Nat.add_comm]` replaces `a + b` with `b + a` in the goal, using the commutativity of addition.

## Example Proofs

Let's see how these tactics work together in more complex proofs.

### Equality

```lean
example {α : Type} {a b c : α} (h1 : a = b) (h2 : b = c) : a = c := by
  apply Eq.trans
  exact h1
  exact h2
```

### Logical Connectives

Lets define the foundational logical connectives in Lean:

#### Implication

To prove an implication `P → Q`, assume `P` and prove `Q`.

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h  -- Apply the implication
  exact p
```

#### Conjunction

To prove `P ∧ Q`, prove `P` and `Q` separately.


```lean
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  apply And.intro
  exact p
  exact q
```

#### Disjunction

To prove `P ∨ Q`, prove either `P` or `Q`.


```lean
example (P Q : Prop) (p : P) : P ∨ Q := by
  apply Or.inl
  exact p
```

#### Negation and False

To prove `¬ P`, assume `P` and prove `False`.

```lean
example (P : Prop) (h : P) (hnp : ¬ P) : False :=
  hnp h -- Apply the negation. ¬P is equivalent to P → False
```

## Interacting with Lean

### Info View

The Info View in VS Code (or your editor) is crucial for interactive theorem proving. It shows:

*   The current goal(s).
*   The available hypotheses.
*    The tactic state (the sequence of tactics you have used/are currently using).

## Structuring Proofs

- **Indentation:** Use indentation to make the proof structure clear.
- **Comments:** Explain the *why* of your steps, not just the *what*.
- **Subgoals:** Break down complex proofs into smaller, manageable subgoals using `have`.

```lean
example (a b c : Nat) (h : a ≤ b ∧ b < c) : a < c := by
  -- We have a ≤ b and b < c.  We want to show a < c.
  have hab : a ≤ b := h.left   -- Extract the first part of the conjunction.
  have hbc : b < c := h.right  -- Extract the second part.
  apply Nat.lt_of_le_of_lt hab hbc  -- Use a lemma combining ≤ and <.
```

## Automated Tactics (Brief Introduction)

Lean provides powerful automated tactics that can often find proofs (or parts of proofs) automatically.  These include:

*   `simp`: Simplifies the goal using a set of simplification rules.
*   `tauto`:  Proves tautologies (logically true statements).
*   `linarith`:  Solves linear arithmetic problems.
*   `finish`: Attempt to finish the proof.

We'll cover these in more detail later, but you can start experimenting with them.

```lean
example (a b c : Nat) (h : a ≤ b ∧ b < c) : a < c := by
  cases h
  rename_i h1 h2
  apply Nat.lt_of_le_of_lt <;> assumption
```
