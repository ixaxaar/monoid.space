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

This chapter focuses primarily on tactic mode, which offers a good balance between control and automation.

## Structured Proofs

Before diving into individual tactics, let's discuss how to structure proofs effectively. A well-structured proof is:

- **Clear:** Each step should have a clear purpose
- **Modular:** Break complex proofs into smaller, manageable parts
- **Maintainable:** Easy to modify or extend if needed

Here's an example of a structured proof:

```lean
example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  -- First establish that a ≤ b and b < c implies a < c
  apply Nat.lt_of_le_of_lt
  -- Now we need to prove the two premises
  · exact h₁  -- First premise: a ≤ b
  · exact h₂  -- Second premise: b < c
```

## Tactic Combinators

Lean provides several ways to combine tactics:

### Sequencing with `;`

The semicolon allows you to chain tactics:

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h; exact p
```

This applies `h` and then immediately applies `exact p` to the resulting goal.

### Branching with `|`

The vertical bar allows you to try different tactics for the same goal:

```lean
example (P Q : Prop) : P → (P → Q) → Q := by
  intros p h
  first
  | exact h p
  | apply h; exact p
```

### Repetition with `*` and `+`

You can repeat tactics with `*` (zero or more times) and `+` (one or more times):

```lean
example (P Q R : Prop) : (P → Q → R) → P → Q → R := by
  intros* -- Introduce all hypotheses at once
  assumption -- Use an assumption that matches the goal
```

## Basic Tactics

### `rfl` and `refl`

Both prove goals of the form `a = a` by reflexivity:

```lean
example : 2 + 2 = 4 := by
  rfl -- Proves by computation (definitional equality)
```

### `intro` and `intros`

Introduces hypotheses for implications and universal quantifiers:

```lean
example : ∀ (n m : ℕ), n = m → m = n := by
  intros n m h
  symm
  exact h
```

### `apply`

Applies a theorem or hypothesis whose conclusion matches the goal:

```lean
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h
  exact p
```

### `exact`

Provides an exact proof term for the current goal:

```lean
example (P : Prop) (h : P) : P := by
  exact h
```

### `assumption`

Looks for a hypothesis that exactly matches the goal:

```lean
example (P Q : Prop) (h₁ : P) (h₂ : Q) : P := by
  assumption
```

### `have`

Introduces a new subgoal and adds it as a hypothesis once proved:

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := h₁ p
  exact h₂ q
```

### `let`

Introduces a local definition:

```lean
example (n : ℕ) : n + n = 2 * n := by
  let double := n + n
  have : double = 2 * n := by
    rw [mul_two]
  exact this
```

### `rewrite` and `rw`

Rewrites the goal using an equality:

```lean
example (a b : ℕ) (h : a = b) : a + a = b + b := by
  rw [h]
  -- Goal is now b + b = b + b
  rfl
```

You can rewrite multiple equalities and specify directions:

```lean
example (a b c : ℕ) (h₁ : a = b) (h₂ : c = b) : a = c := by
  rw [h₁, ←h₂]
  -- First rewrites a to b, then c to b (in reverse)
  -- Goal is now b = b
  rfl
```

### `cases`

Breaks down a hypothesis by cases:

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with | intro hp hq =>
    constructor
    · exact hq
    · exact hp
```

### `induction`

Proves a goal by induction:

```lean
example (n : ℕ) : 2 * n = n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, ih]
    rfl
```

### `contradiction`

Proves a goal when the hypotheses are contradictory:

```lean
example (P : Prop) (h₁ : P) (h₂ : ¬P) : Q := by
  contradiction
```

### `by_cases`

Splits a proof into cases based on whether a proposition is true or false:

```lean
example (P Q : Prop) : (P → Q) → (¬P ∨ Q) := by
  intro h
  by_cases hp : P
  · right
    exact h hp
  · left
    exact hp
```

## Intermediate Tactics

### `simp`

Simplifies the goal using a library of simplification lemmas:

```lean
example (a b c : ℕ) (h : a = b) : a + c = b + c := by
  simp [h]
```

### `ring`

Solves equalities in commutative rings:

```lean
example (a b : ℕ) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
  ring
```

### `field`

Solves equalities in fields, handling divisions:

```lean
example (a b c : ℚ) (h : c ≠ 0) : (a + b) / c = a / c + b / c := by
  field_simp
  ring
```

### `linarith`

Solves linear arithmetic problems:

```lean
example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  linarith
```

## Advanced Tactics

### `tauto`

Proves tautologies in propositional logic:

```lean
example (P Q : Prop) : P ∧ Q → P := by
  tauto
```

### `finish`

Attempts to finish the proof using a combination of tactics:

```lean
example (P Q : Prop) (h₁ : P → Q) (h₂ : P) : Q := by
  finish
```

### `omega`

Handles linear arithmetic over integers:

```lean
example (a b : Int) (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  omega
```

### `aesop`

The Automated Extensible Search for Obvious Proofs (aesop) is a powerful search tactic:

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R := by
  aesop
```

## Proof Patterns and Strategies

### Forward Reasoning vs. Backward Reasoning

In **forward reasoning**, you start with what you know and derive new facts until you reach the goal:

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := h₁ p
  have r : R := h₂ q
  exact r
```

In **backward reasoning**, you start with the goal and break it down until you reach known facts:

```lean
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  apply h₂
  apply h₁
  exact p
```

### Case Analysis

When dealing with complex goals, breaking them into cases can simplify the proof:

```lean
example (n : ℕ) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; apply Nat.succ_pos
```

### Induction Principles

Induction is essential for proving properties of recursive definitions:

```lean
example (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.add_succ, ih]
    rfl
```

### Proof by Contradiction

Sometimes, it's easier to prove something by assuming its negation and deriving a contradiction:

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases p : P
  · exact p
  · contradiction
```

## Debugging Proofs

### `trace`

Prints information during proof execution:

```lean
example (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => 
    trace "Base case: proving 0 + 0 = 0"
    rfl
  | succ n ih => 
    trace "Inductive case: proving succ n + 0 = succ n using " ++ toString ih
    rw [Nat.add_succ]
    rw [ih]
    rfl
```

### `#print`

Outside of proofs, `#print` shows the definition of terms:

```lean
#print Nat.add
```

### `#check`

Checks the type of an expression:

```lean
#check Nat.add_comm
```

## Examples of Complex Proofs

Let's conclude with a more sophisticated example that combines multiple tactics:

```lean
theorem sqrt2_irrational : ¬ ∃ (p q : ℕ), q > 0 ∧ p*p = 2*q*q := by
  intro ⟨p, q, hq, h⟩
  wlog hp : p > 0
  · have : p*p = 2*q*q := h
    have : p*p > 0 := by
      apply mul_pos <;> assumption
    have : p > 0 := Nat.pos_of_mul_pos_left this (by decide)
    contradiction
  
  have : p*p = 2*q*q := h
  have : Even (p*p) := by
    use q*q
    rw [two_mul]
    exact this.symm
  
  have : Even p := by
    apply even_of_even_sqr
    assumption
  
  rcases this with ⟨k, hk⟩
  rw [hk, mul_pow] at h
  have : 4*k*k = 2*q*q := by rw [← h, pow_two, mul_assoc]
  have : 2*k*k = q*q := by
    apply mul_left_cancel₀ two_ne_zero
    exact this
  
  have : Even (q*q) := by
    use k*k
    rw [two_mul]
    exact this.symm
  
  have : Even q := by
    apply even_of_even_sqr
    assumption
  
  rcases this with ⟨j, hj⟩
  rw [hj, ← mul_assoc, mul_pow] at h
  
  -- Now we have a smaller pair (k, j) with the same property
  have : k*k = 2*j*j := by
    apply mul_left_cancel₀ (by decide : 4 ≠ 0)
    rw [← h, mul_pow, mul_assoc, mul_assoc]
    ring
  
  have : k > 0 := by
    apply Nat.pos_of_mul_pos_left (by rw [← hk]; exact hp) (by decide)
  have : j > 0 := by
    apply Nat.pos_of_mul_pos_left (by rw [← hj]; exact hq) (by decide)
  
  -- This contradicts the well-foundedness of ℕ
  have : k < p := by
    rw [hk]
    apply Nat.mul_lt_of_lt_div
    · exact two_pos
    · exact hp
  
  -- Infinite descent is impossible
  have : ∃ (p' q' : ℕ), q' > 0 ∧ p'*p' = 2*q'*q' ∧ p' < p := by
    use k, j
    constructor
    · exact ⟨this.1, this.2, by assumption⟩
  
  -- Apply infinite descent to get a contradiction
  have := sqrt2_irrational
  contradiction
```

This extended example demonstrates the power of combining tactics for constructing complex proofs. Understanding when and how to use each tactic is an essential skill for theorem proving in Lean.

---

[Next: Automation & Reflection](Proofs.automation.html)