---

[Contents](contents.html)
[Previous](Types.identity.html)
[Next](Proofs.tactics.html) <!-- Assuming the next chapter is on Tactics -->

# Introduction

---

- [Propositions as Types](#propositions-as-types)
- [Curry-Howard Isomorphism](#curry-howard-isomorphism)
- [Tactics](#tactics)
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
- [Structuring Proofs](#structuring-proofs)
- [Automated Tactics](#automated-tactics)

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Basic
```

In previous chapters, we've seen that types in Lean can represent mathematical objects, data structures, and even propositions (statements that can be true or false). We've hinted at the idea of proofs being terms of these propositional types, specifically in the context of identity types as paths between terms (where each of these terms is a proof).

Theorem proving in Lean is a process of constructing **terms of propositional types** to prove theorems. This is done using a combination of tactics that manipulate the proof state, which consists of goals (propositions to be proved) and hypotheses (assumptions that can be used in the proof). These terms are the formal, machine-checkable proofs of the propositions.

The real value proposition of theorem provers is that they can check these proofs for correctness instead of a human having to do it.

## Propositions as Types

In type theory, propositions are types. A proposition is a type with only one inhabitant (a term of that type) if the proposition is true, and no inhabitants if the proposition is false. For example, the proposition `2 + 2 = 4` is a type with one term, `rfl`, which is the proof that `2 + 2 = 4`. If the proposition is false, the type will have no terms, as its simply impossible to construct such a term.

```lean
def proof_of_2_plus_2 : 2 + 2 = 4 := rfl
```

Let's break this down and look at it in more detail:

A proposition is a statement that can be either true or false. Examples:

1.  "2 + 2 = 4"
1.  "All cats are mammals."
1.  "x > 5" (where 'x' is a variable)

In type theory (and in Lean), propositions are treated as types. These types are called **propositional types**. The specific type that represents propositions in Lean is called `Prop`. So, instead of just saying "2 + 2 = 4" is a proposition, we can say its a type (of type `Prop`). In Lean:

```lean
#check 2 + 2 = 4  -- Output: 2 + 2 = 4 : Prop
```

This `#check` command confirms that the expression `2 + 2 = 4` has the type `Prop`, meaning its a propositional type.

In type theory, a "term" is an inhabitant of a type. Its a specific value or expression that belongs to that type. Think of it like this:

1.  `Nat` is a type (the type of natural numbers).
1.  `5` is a term of type `Nat`.
1.  `"hello"` is a term of type `String`.
1.  `true` is a term of type `Bool`.

**Terms of Propositional Types:**

A term of a propositional type is a proof of that proposition. If you can construct a term whose type is a particular proposition, you have proven that proposition. If you cannot construct such a term, the proposition is considered unproven (or, in some cases, false).

Let's see some examples:

**Example 1: A true proposition**

```lean
def my_proof : 2 + 2 = 4 := rfl
#check my_proof  -- Output: my_proof : 2 + 2 = 4
```

- `2 + 2 = 4` is the propositional type (a proposition).
- `my_proof` is a term of that type.
- `rfl` is the actual proof (it says "2 + 2 = 4 by definition"). `rfl` is a term, and that's the term we're assigning to `my_proof`.
- Because we were able to construct the term `my_proof`, we have proven the proposition `2 + 2 = 4`.

**Example 2: An implication**

```lean
def add_one_increases (n : Nat) : n < n + 1 := Nat.lt_succ_self n
#check add_one_increases  -- Output: add_one_increases : ∀ (n : ℕ), n < n + 1
```

Here, we have the following:

- `n < n + 1` is the propositional type (a proposition).
- `add_one_increases` is a term of that type.
- `Nat.lt_succ_self n` is the actual proof (it says "n < n + 1 by definition").
- Because we were able to construct the term `add_one_increases`, we have proven the proposition `n < n + 1`.

**Example 3: An uninhabited proposition (no term)**

We can state the proposition `1 = 0`, but we can't create a term of that type (unless our logic is inconsistent!).

```lean
#check 1 = 0   -- Output: 1 = 0 : Prop
--  We can't write:  def a_proof : 1 = 0 := ...  (There's nothing we can put here)
```

This ability to treat propositions as types and proofs as terms is a fundamental aspect of type theory and is what makes Lean a powerful tool for both programming and formal verification. It blurs the line between data and proof, making them aspects of the same underlying concept: terms inhabiting types. This is the essence of the "propositions as types" correspondence.

## Curry-Howard Isomorphism

The Curry-Howard Isomorphism is a deep and fundamental connection between logic and computation with type theory as the foundational way of expression. It establishes the direct connection between mathematical proofs and computer programs. Its named after logicians Haskell Curry and William Howard. It states that there is a correspondence between:

- **Proofs** in logic.
- **Programs** in computation.
- **Types** in type theory.

The correspondence is as follows:

- **Propositions** are types.
- **Proofs** are terms.
- **Implication** is a function type.
- **Conjunction** is a product type.
- **Disjunction** is a sum type.

Here is a more detailed comparison:

| Logic                                    | Type Theory                                                         | Programming (Lean)                            | Explanation                                                                                                                                                                                                                          |
| ---------------------------------------- | ------------------------------------------------------------------- | --------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Proposition                              | Type (in `Prop`)                                                    | `2 + 2 = 4` : `Prop`                          | A statement that can be true or false. In Lean, propositions are types.                                                                                                                                                              |
| Proof                                    | Term                                                                | `rfl` : `2 + 2 = 4`                           | A witness that a proposition is true. In Lean, proofs are terms of the propositional type.                                                                                                                                           |
| Implication (`P → Q`)                    | Function Type (`P → Q`)                                             | `fun (h : P) => ... : Q`                      | If you have a proof of `P`, you can get a proof of `Q`. Corresponds to a function that takes an argument of type `P` and returns a value of type `Q`.                                                                                |
| Conjunction (`P ∧ Q`)                    | Product Type (`P × Q` or `And P Q`)                                 | `(p, q)` : `P × Q` , `And.intro p q : P ∧ Q ` | You have a proof of _both_ `P` and `Q`. Corresponds to a tuple or pair containing a term of type `P` and a term of type `Q`.                                                                                                         |
| Disjunction (`P ∨ Q`)                    | Sum Type (`P + Q` or `Or P Q`)                                      | `Or.inl p` : `P ∨ Q`, `Or.inr q` : `P ∨ Q`    | You have a proof of _either_ `P` _or_ `Q`. Corresponds to a type that can hold either a value of type `P` or a value of type `Q` (like `Either` in Haskell or tagged unions in other languages).                                     |
| Universal Quantification (`∀ x, P(x)`)   | Dependent Function Type (`(x : A) → P x`)                           | `fun (x : A) => ... : (x : A) → P x`          | For _all_ `x` of type `A`, `P(x)` holds. Corresponds to a dependent function type, where the type of the result (`P x`) depends on the value of the input (`x`). The return _type_ can change depending on the _value_ of the input. |
| Existential Quantification (`∃ x, P(x)`) | Dependent Pair Type (`Σ (x : A), P x` or `Exists (fun x:A => P x)`) | `⟨x, p⟩` : `Σ (x : A), P x`                   | There _exists_ an `x` of type `A` such that `P(x)` holds. Corresponds to a dependent pair (Sigma type) where you have a value `x` of type `A` _and_ a proof that `P(x)` holds.                                                       |
| True (`⊤` or `True`)                     | Unit Type (`Unit` or `PUnit`)                                       | `()` : `Unit`                                 | A proposition that is always true. Corresponds to a type with a single inhabitant (like the unit type). There is only one proof, and it carries no information beyond the fact that the proposition is true.                         |
| False (`⊥` or `False`)                   | Empty Type (`Empty`)                                                | _(No term)_                                   | A proposition that is always false. Corresponds to a type with _no_ inhabitants (the empty type). You cannot construct a term of this type (without introducing inconsistencies).                                                    |
| Negation (`¬P`)                          | Function Type (`P → Empty`)                                         | `fun (h : P) => ... : Empty`                  | If you have a proof of `P`, you can reach a contradiction. This is represented as a function that takes a proof of `P` and returns a term of the empty type (which is impossible). `¬P` is _defined_ as `P → False` in Lean.         |
| Equality (`a = b`)                       | Identity Type (`a = b`)                                             | `refl` (if `a` and `b` are def. equal)        | The type representing the proposition that `a` and `b` are equal. The term `rfl` (reflexivity) is a proof that `a = a`. More complex equalities require proofs using path induction and other techniques.                            |
| Type Variables                           | Type Parameters                                                     | `{α : Type}`                                  | Allows generalizing theorems/functions to work across different types.                                                                                                                                                               |

This correspondence is what enables us to use Lean for theorem proving. We can construct terms (programs) that correspond to proofs of propositions (logical statements), using the type system to ensure correctness. The Curry-Howard Isomorphism thus bridges mathematical logic, type theory and computation.

There are extensions of the Curry-Howard Isomorphism, such as the Curry-Howard-Lambek Correspondence, which extends the correspondence to include category theory, the Curry-Howard-De Bruijn Correspondence, which extends it to include lambda calculus.

## Tactics

Tactics are commands that instruct Lean on how to construct a proof term. They manipulate the proof state, which consists of:

- **Goals:** The propositions we're currently trying to prove.
- **Hypotheses:** Assumptions we can use in the proof.

A proof starts with an initial goal (the theorem we want to prove) and ends when all goals have been closed (proven). A proof may involve multiple subgoals, each requiring its own proof, just like computer programs can be broken down into smaller functions and combined.

Propositions can be combined using logical connectives like `∧` (and), `∨` (or), `→` (implies), and `¬` (not). Propositions can also be quantified over types or values using `∀` (for all) and `∃` (there exists).

When using tactics in Lean, you typically start with the `by` keyword, which enters "tactic mode." The proof state is then displayed in the editor, showing the current goal and available hypotheses. As you apply tactics, the proof state changes, and Lean guides you toward completing the proof.

For example, here's how a proof state might look when proving a simple theorem:

```lean
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  -- Proof state:
  -- a b c : Nat
  -- h1 : a ≤ b
  -- h2 : b ≤ c
  -- ⊢ a ≤ c
  exact Nat.le_trans h1 h2 -- using the fact that ≤ is transitive (proof from mathlib)
```

The line with `⊢` shows the current goal, and the lines above show the available hypotheses. The goal is to prove `a ≤ c` using the hypotheses `a ≤ b` and `b ≤ c`.

### `rfl`

We've already seen `rfl`. It proves goals that are definitionally equal (equal by computation).

```lean
example : 2 + 2 = 4 := rfl
```

### `intro`

The `intro` tactic (short for "introduce") introduces a new hypothesis. Its used when the goal is an implication (`A → B`) or a universal quantification (`∀ x, ...`).

```lean
example : ∀ x : Nat, x ≤ x + 1 := by
  intro x  -- Introduce 'x' as a new hypothesis (a natural number)
  apply Nat.le_add_right  -- Use a lemma from the library
```

Here, the initial goal is `∀ x : Nat, x ≤ x + 1`. `intro x` changes the goal to `x ≤ x + 1`, with `x : Nat` as a hypothesis.

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

The `let` tactic introduces a _local definition_. This is useful for giving names to intermediate terms and breaking down complex expressions.

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

## Structuring Proofs

- **Indentation:** Use indentation to make the proof structure clear.
- **Comments:** Explain the _why_ of your steps, not just the _what_.
- **Subgoals:** Break down complex proofs into smaller, manageable subgoals using `have`.

```lean
example (a b c : Nat) (h : a ≤ b ∧ b < c) : a < c := by
  -- We have a ≤ b and b < c.  We want to show a < c.
  have hab : a ≤ b := h.left   -- Extract the first part of the conjunction.
  have hbc : b < c := h.right  -- Extract the second part.
  apply Nat.lt_of_le_of_lt hab hbc  -- Use a lemma combining ≤ and <.
```

## Automated Tactics

Lean provides powerful automated tactics that can often find proofs (or parts of proofs) automatically. These include:

- `simp`: Simplifies the goal using a set of simplification rules.
- `tauto`: Proves tautologies (logically true statements).
- `linarith`: Solves linear arithmetic problems.
- `finish`: Attempt to finish the proof.

We'll cover these in more detail later.

---

[Strategies & Tactics](Proofs.tactics.html)
