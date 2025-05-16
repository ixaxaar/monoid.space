---

[Contents](contents.html)
[Previous](Proofs.introduction.html)
[Next](Proofs.automation.html) <!-- WIP section -->

# Strategies & Tactics

---

- [Introduction](#introduction)
- [Structured Proofs](#structured-proofs)
- [Tactic Combinators](#tactic-combinators)
  - [Sequencing with `;`](#sequencing-with-)
  - [Branching with `|`](#branching-with-)
  - [Repetition with `*` and `+`](#repetition-with--and-)
- [Basic Tactics](#basic-tactics)
  - [`rfl` and `refl`](#rfl-and-refl)
  - [`intro` and `intros`](#intro-and-intros)
  - [`apply`](#apply)
  - [`exact`](#exact)
  - [`assumption`](#assumption)
  - [`have`](#have)
  - [`let`](#let)
  - [`rewrite` and `rw`](#rewrite-and-rw)
  - [`cases`](#cases)
  - [`induction`](#induction)
  - [`contradiction`](#contradiction)
  - [`by_cases`](#by_cases)
- [Intermediate Tactics](#intermediate-tactics)
  - [`simp`](#simp)
  - [`ring`](#ring)
  - [`field`](#field)
  - [`linarith`](#linarith)
- [Advanced Tactics](#advanced-tactics)
  - [`tauto`](#tauto)
  - [`finish`](#finish)
  - [`omega`](#omega)
  - [`aesop`](#aesop)
- [Proof Patterns and Strategies](#proof-patterns-and-strategies)
  - [Forward Reasoning vs. Backward Reasoning](#forward-reasoning-vs-backward-reasoning)
  - [Case Analysis](#case-analysis)
  - [Induction Principles](#induction-principles)
  - [Proof by Contradiction](#proof-by-contradiction)
- [Debugging Proofs](#debugging-proofs)
  - [`trace`](#trace)
  - [`#print`](#print)
  - [`#check`](#check)
- [Examples of Complex Proofs](#examples-of-complex-proofs)

```lean
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
```

## Introduction

In the previous chapter, we introduced the concept of proofs in Lean and briefly touched on some basic tactics. In this chapter, we'll dive deeper into tactics and explore strategies for constructing proofs effectively.

Tactics are commands that manipulate the proof state to help us construct proof terms. They automate parts of the proof construction process, allowing us to focus on the high-level structure of a proof rather than every detail of the underlying term.

When working with Lean, there are multiple ways to approach proofs:

1. **Term mode:** Directly writing proof terms without tactics
2. **Tactic mode:** Using tactics with the `by` keyword
3. **Structured proofs:** Combining term and tactic mode with `have`, `let`, etc.

This chapter focuses primarily on tactic mode, which offers a good balance between control and automation. Whether you're new to proof assistants or transitioning from another system like Agda, mastering tactics in Lean will significantly enhance your ability to formalize mathematics and logic.

## Structured Proofs

Before diving into individual tactics, let's discuss how to structure proofs effectively. A well-structured proof is:

- **Clear:** Each step should have a clear purpose
- **Modular:** Break complex proofs into smaller, manageable parts
- **Maintainable:** Easy to modify or extend if needed

Here's an example of a structured proof in Lean, which combines multiple steps in a readable way:

```lean
example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  -- First establish that a ≤ b and b < c implies a < c
  apply Nat.lt_of_le_of_lt
  -- Now we need to prove the two premises
  · exact h₁  -- First premise: a ≤ b
  · exact h₂  -- Second premise: b < c
```

`apply` here is used to apply a theorem `Nat.lt_of_le_of_lt` from the library, which states that if `a ≤ b` and `b < c`, then `a < c` on natural numbers.

`exact` is used to provide the exact hypotheses needed for the theorem.

So, if we are given `h₁` and `h₂`, we can apply the theorem already proven theorem from the library and we supply the hypotheses `h₁` and `h₂` to the theorem to prove the goal.

In this context, it might be helpful for thinking of a theorem as a function that takes arguments (hypotheses) and returns a result (the conclusion). The `apply` tactic is like calling that function, and `exact` is like providing the arguments.

## Tactic Combinators

Lean provides several ways to combine tactics, allowing you to chain, branch, or repeat them for easier proof construction:

### Sequencing with `;`

The semicolon allows you to chain tactics, applying one after another to the current goal:

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h; exact p
```

This applies `h` to transform the goal into needing `P`, and then immediately uses `exact p` to close the goal with the provided hypothesis.

### Branching with `|`

The vertical bar allows you to try different tactics for the same goal, useful when multiple approaches might work:

```lean
example (P Q : Prop) : P → (P → Q) → Q := by
  intros p h
  first
  | exact h p
  | apply h; exact p
```

Here, `first` tries each tactic in order until one succeeds. This can be handy for experimentation or when a goal can be solved in multiple ways.

### Repetition with `*` and `+`

You can repeat tactics with `*` (zero or more times) and `+` (one or more times), which is particularly useful for handling multiple hypotheses or goals:

```lean
example (P Q R : Prop) : (P → Q → R) → P → Q → R := by
  intros* -- Introduce all hypotheses at once
  assumption -- Use an assumption that matches the goal
```

The `intros*` tactic introduces all possible hypotheses in one go, streamlining the proof process.

## Basic Tactics

Let's explore the foundational tactics in Lean. These are the building blocks you'll use in almost every proof, so getting comfortable with them is essential.

### `rfl` and `refl`

Both prove goals of the form `a = a` by reflexivity, often used for equalities that hold by definition:

```lean
example : 2 + 2 = 4 := by
  rfl -- Proves by computation (definitional equality)
```

While `rfl` focuses on computational equality, `refl` is a more general tactic for reflexive relations. You'll most often use `rfl` for straightforward equalities.

### `intro` and `intros`

These tactics introduce hypotheses for implications and universal quantifiers, moving them from the goal to the context:

```lean
example : ∀ (n m : ℕ), n = m → m = n := by
  intros n m h
  symm
  exact h
```

`intro` introduces one hypothesis at a time, while `intros` can handle multiple at once, as shown above. This mirrors how you might assume premises in a mathematical argument.

### `apply`

Applies a theorem or hypothesis whose conclusion matches the goal, potentially generating new subgoals for its premises:

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h
  exact p
```

Think of `apply` as working backward: it reduces the goal to proving the premises of the applied theorem or hypothesis.

### `exact`

Provides an exact proof term for the current goal, closing it if the term matches the goal precisely:

```lean
example (P : Prop) (h : P) : P := by
  exact h
```

This is often used after other tactics have shaped the goal to match an existing hypothesis or theorem.

### `assumption`

Looks for a hypothesis in the context that exactly matches the goal, closing it automatically:

```lean
example (P Q : Prop) (h₁ : P) (h₂ : Q) : P := by
  assumption
```

This is a quick way to resolve goals when the required proof is already in the context, saving you from explicitly naming the hypothesis.

### `have`

Introduces a new subgoal and adds it as a hypothesis once proved, useful for breaking down complex proofs into smaller steps:

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := h₁ p
  exact h₂ q
```

This tactic helps in making proofs more modular, allowing you to name intermediate results for clarity and reuse.

### `let`

Introduces a local definition within a proof, which can simplify expressions or clarify intent:

```lean
example (n : ℕ) : n + n = 2 * n := by
  let double := n + n
  have : double = 2 * n := by
    rw [mul_two]
  exact this
```

`let` is particularly useful when you need to refer to a computed value multiple times in a proof.

### `rewrite` and `rw`

Rewrites the goal using an equality, transforming expressions based on proven equalities or definitions:

```lean
example (a b : ℕ) (h : a = b) : a + a = b + b := by
  rw [h]
  -- Goal is now b + b = b + b
  rfl
```

You can rewrite multiple equalities and specify direction with `←` for reverse rewriting:

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : c = b) : a = c := by
  rw [h₁, ←h₂]
  -- First rewrites a to b, then c to b (in reverse)
  -- Goal is now b = b
  rfl
```

`rw` is one of the most frequently used tactics, as it allows direct manipulation of terms in the goal.

### `cases`

Breaks down a hypothesis or goal by cases, useful for handling inductive types or logical disjunctions:

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with | intro hp hq =>
    constructor
    · exact hq
    · exact hp
```

This tactic splits the proof into manageable parts based on the structure of the data or proposition, much like a case analysis in mathematics.

### `induction`

Proves a goal by induction, essential for reasoning about recursive structures like natural numbers or lists:

```lean
example (n : ℕ) : 2 * n = n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, ih]
    rfl
```

Here, `ih` is the induction hypothesis, used to build the proof for the successor case. Induction is a cornerstone of formal proofs in Lean.

### `contradiction`

Proves a goal when the hypotheses are contradictory, resolving the proof by showing an inconsistency:

```lean
example (P : Prop) (h₁ : P) (h₂ : ¬P) : Q := by
  contradiction
```

This tactic is useful in proofs by contradiction, where assuming the negation leads to an impossible state.

### `by_cases`

Splits the proof into two cases based on a decidable proposition, allowing you to handle both possibilities:

```lean
example (P Q : Prop) (h : P → Q) : ¬P ∨ Q := by
  by_cases p : P
  · exact Or.inr (h p)  -- Case 1: P is true, so Q must be true
  · exact Or.inl p      -- Case 2: P is false, so ¬P holds
```

`by_cases` is particularly useful for propositions where you can reason about both truth and falsity, mirroring classical logic's law of excluded middle (though Lean often works constructively).

## Intermediate Tactics

Once you're comfortable with the basics, these intermediate tactics can speed up proof development by automating common patterns.

### `simp`

Simplifies the goal or hypotheses using a set of simplification rules, often reducing expressions to their canonical form:

```lean
example (a b : ℕ) : a + 0 + b = a + b := by
  simp
```

`simp` is a powerful tool for cleaning up goals, especially in algebraic contexts, though it can sometimes be opaque about what rules it applies.

### `ring`

Automates proofs of equalities in commutative rings, solving polynomial equations over integers or rationals:

```lean
example (a b : ℤ) : (a + b) * (a - b) = a^2 - b^2 := by
  ring
```

This tactic is invaluable for algebraic manipulations, handling tedious calculations automatically.

### `field`

Similar to `ring`, but for fields, handling fractions and division in expressions:

```lean
example (a b : ℚ) (h : b ≠ 0) : (a / b) * b = a := by
  field
  exact h
```

`field` simplifies rational expressions, making it easier to work with fractions in proofs.

### `linarith`

Automates linear arithmetic, proving inequalities and equalities involving addition and scalar multiplication:

```lean
example (a b c : ℤ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  linarith
```

This tactic is a go-to for numerical inequalities, combining hypotheses to resolve the goal.

## Advanced Tactics

For more complex proofs, these advanced tactics can handle entire subgoals or apply sophisticated automation.

### `tauto`

Automates proofs in propositional logic, resolving tautologies using logical rules:

```lean
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  tauto
```

`tauto` is great for logical implications and contradictions, often closing goals in one step.

### `finish`

A powerful automation tactic that attempts to close the goal using a combination of logical and arithmetic reasoning:

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  finish
```

While convenient, `finish` can be slow for large goals, so use it judiciously.

### `omega`

Handles Presburger arithmetic, proving statements about integers using addition and inequalities:

```lean
example (a b : ℤ) (h : a < b) : a + 1 ≤ b := by
  omega
```

`omega` is particularly useful for integer arithmetic beyond simple linear combinations.

### `aesop`

A modern automation tactic in Lean, designed as a successor to `finish`, offering customizable search strategies:

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  aesop
```

`aesop` is highly configurable and often more efficient than older automation tactics, making it a strong choice for complex proofs.

## Proof Patterns and Strategies

Beyond individual tactics, successful theorem proving in Lean involves understanding broader strategies. These patterns help you approach proofs systematically, especially for complex goals.

### Forward Reasoning vs. Backward Reasoning

- **Forward Reasoning**: Start with what you know (hypotheses) and build towards the goal. Tactics like `have` and direct computation support this approach.
- **Backward Reasoning**: Start with the goal and work backward to what you need to prove. Tactics like `apply` and `rw` are key here, reducing the goal to simpler subgoals.

Most proofs in Lean combine both approaches. For example, you might use `apply` to break down the goal (backward), then use `have` to establish an intermediate result (forward).

### Case Analysis

Case analysis, facilitated by `cases` and `by_cases`, involves breaking a problem into distinct scenarios. This is particularly useful for propositions with multiple possible states or inductive types with different constructors.

```lean
example (n : ℕ) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (Nat.zero_lt_succ k)
```

This pattern mirrors how mathematicians often split arguments into cases based on structure or properties.

### Induction Principles

Induction, as seen with the `induction` tactic, is fundamental for proving properties over recursive structures. Always consider induction for goals involving natural numbers, lists, or other inductive types.

```lean
example (l : List ℕ) : l.length ≥ 0 := by
  induction l with
  | nil => exact Nat.zero_le 0
  | cons _ ih => exact Nat.succ_le_succ ih
```

The induction hypothesis (`ih`) is your bridge from the base case to the general case, a concept we'll revisit in more advanced contexts.

### Proof by Contradiction

Proof by contradiction, supported by the `contradiction` tactic, assumes the negation of the goal and derives a contradiction from the hypotheses:

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases p : P
  · exact p
  · contradiction  -- h is ¬¬P, p is ¬P, so contradiction
```

This classical approach is powerful but should be used carefully in Lean, as constructive proofs are often preferred for clarity and computational content.

## Debugging Proofs

Proofs don't always go as planned, especially when learning Lean or tackling complex goals. These tools and tactics help diagnose issues in your proofs.

### `trace`

Outputs intermediate states or messages during proof execution, helping you see where a tactic fails or what the goal looks like:

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  trace "Current goal before apply"
  apply h
  trace "Goal after apply: need to prove P"
  exact p
```

Use `trace` to log custom messages or inspect the proof state at specific points.

### `#print`

Prints definitions or information about a term, useful for understanding what theorems or types are available:

```lean
#print Nat.add  -- Shows the definition of addition on natural numbers
```

This command helps when you're unsure about the exact statement or structure of a theorem you want to use.

### `#check`

Checks the type of an expression, confirming what a term or theorem represents:

```lean
#check Nat.lt_of_le_of_lt  -- Displays the type of this theorem
```

Use `#check` to ensure you're applying the right theorem or to explore the library for useful results.

## Examples of Complex Proofs

To solidify your understanding, let's look at a few more involved proofs that combine multiple tactics and strategies. These examples build on concepts from earlier chapters and demonstrate real-world applications of Lean tactics.

**Example 1: Proving a Property of Natural Numbers**

Let's prove that the sum of the first `n` natural numbers is `n * (n + 1) / 2`. This classic result requires induction and algebraic manipulation:

```lean
example (n : ℕ) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero =>
    simp [List.range, List.sum_nil]  -- Base case: sum of empty list is 0
  | succ n ih =>
    simp [List.range, List.sum_cons, ih]  -- Unfold definitions
    ring  -- Use ring tactic to simplify the algebra
```

This proof uses `induction` for the structure, `simp` to handle list operations, and `ring` for algebraic simplification, showcasing how tactics build on each other.

**Example 2: Logical Implication with Multiple Cases**

Consider a logical statement involving multiple conditions, where case analysis is necessary:

```lean
example (P Q R : Prop) : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  intro h
  cases h with
  | inl hpq =>
    constructor
    · exact hpq.1  -- P from P ∧ Q
    · exact Or.inl hpq.2  -- Q as left disjunct
  | inr hpr =>
    constructor
    · exact hpr.1  -- P from P ∧ R
    · exact Or.inr hpr.2  -- R as right disjunct
```

Here, `cases` handles the disjunction in the hypothesis, and `constructor` builds the conjunction in the goal, demonstrating structured reasoning over logical propositions.

These examples are just the beginning. As you progress through later chapters, you'll encounter more sophisticated proofs in areas like algebra and category theory, where these tactics will be applied in increasingly complex ways.

---

[Previous](Proofs.introduction.html) | [Next](Proofs.automation.html) <!-- WIP section -->
