---

[Contents](contents.html)
[Previous](Proofs.introduction.html)
[Next](Proofs.debugging.html)

# Essential Tactics for Theorem Proving

---

- [Understanding Tactics](#understanding-tactics)
- [Core Structural Tactics](#core-structural-tactics)
  - [`intro` and `intros`](#intro-and-intros)
  - [`exact` and `apply`](#exact-and-apply)
  - [`rw` and `simp`](#rw-and-simp)
  - [`constructor` and Destructuring](#constructor-and-destructuring)
- [Working with Hypotheses](#working-with-hypotheses)
  - [`have` and `let`](#have-and-let)
  - [`use` for Existentials](#use-for-existentials)
  - [`assumption` and `trivial`](#assumption-and-trivial)
- [Case Analysis and Induction](#case-analysis-and-induction)
  - [`cases` and Pattern Matching](#cases-and-pattern-matching)
  - [`induction` and Recursive Proofs](#induction-and-recursive-proofs)
  - [`by_cases` for Decidable Props](#by_cases-for-decidable-props)
- [Computational Tactics](#computational-tactics)
  - [`rfl` and Definitional Equality](#rfl-and-definitional-equality)
  - [`decide` for Decidable Goals](#decide-for-decidable-goals)
  - [`norm_num` for Numerical Goals](#norm_num-for-numerical-goals)
- [Automation Tactics](#automation-tactics)
  - [`simp` Advanced Usage](#simp-advanced-usage)
  - [`ring` for Algebra](#ring-for-algebra)
  - [`linarith` for Linear Arithmetic](#linarith-for-linear-arithmetic)
- [Tactic Combinators](#tactic-combinators)
  - [Sequencing with `;` and `<;>`](#sequencing-with--and-)
  - [Goal Management](#goal-management)
  - [Error Handling](#error-handling)
- [Debugging and Exploration](#debugging-and-exploration)
- [Advanced Patterns](#advanced-patterns)
  - [Term-Mode Integration](#term-mode-integration)
  - [Meta-Programming Basics](#meta-programming-basics)

```lean
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Decide
import Mathlib.Tactic.NormNum
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
```

Tactics are the building blocks of interactive theorem proving in Lean. They transform proof goals systematically, allowing you to construct complex proofs step by step. This chapter covers all the essential tactics you need to prove the theorems in subsequent chapters, especially the logical foundations covered in Chapter 4.

## Understanding Tactics

A **tactic** is a command that modifies the **proof state**. The proof state consists of:

```lean
-- Example proof state visualization
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  -- Current proof state:
  -- P Q R : Prop          ← Types in context
  -- h1 : P → Q            ← Hypotheses
  -- h2 : Q → R            ← Hypotheses
  -- hp : P                ← Hypotheses
  -- ⊢ R                   ← Current goal
  sorry
```

**Key concepts:**

- **Goals**: Propositions you need to prove (after `⊢`)
- **Hypotheses**: Assumptions you can use (above the line)
- **Context**: Types and definitions available
- **Multiple goals**: Some tactics create subgoals

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  -- Goal: Q ∧ P
  constructor
  -- Now we have two goals: ⊢ Q and ⊢ P
  · exact h.right  -- First goal: prove Q
  · exact h.left   -- Second goal: prove P
```

## Core Structural Tactics

These tactics handle the basic logical structure of proofs.

### `intro` and `intros`

**Purpose**: Introduce hypotheses for implications (`→`) and universal quantifiers (`∀`).

```lean
-- Single introduction
example (P Q : Prop) : P → Q → P := by
  intro hp    -- Introduce hypothesis hp : P
  intro hq    -- Introduce hypothesis hq : Q
  exact hp    -- Goal is P, we have hp : P

-- Multiple introductions
example (P Q R : Prop) : P → Q → R → P ∧ Q := by
  intros hp hq hr  -- Introduce all three at once
  constructor
  · exact hp
  · exact hq

-- With destructuring
example (P Q R : Prop) : P ∧ Q → R → P := by
  intro ⟨hp, hq⟩  -- Destructure the conjunction immediately
  intro hr
  exact hp

-- Universal quantifiers
example (α : Type) (P : α → Prop) : (∀ x, P x) → (∀ y, P y) := by
  intro h      -- h : ∀ x, P x
  intro y      -- Goal becomes: P y
  exact h y    -- Apply h to y
```

**Key patterns:**

- `intro h` - introduce one hypothesis
- `intros h1 h2 h3` - introduce multiple hypotheses
- `intro ⟨hp, hq⟩` - introduce and destructure

### `exact` and `apply`

**Purpose**: Provide exact proofs or apply theorems.

```lean
-- exact: when you have exactly what you need
example (P Q : Prop) (hp : P) : P := by
  exact hp  -- hp is exactly a proof of P

-- apply: when you need to work backwards from a conclusion
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  apply h2     -- Goal becomes: prove Q
  apply h1     -- Goal becomes: prove P
  exact hp     -- We have P

-- apply with automatic inference
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply Nat.le_trans h1 h2  -- Lean infers the arguments

-- Partial application
example (P Q R : Prop) (h : P → Q → R) (hp : P) (hq : Q) : R := by
  apply h
  · exact hp  -- First subgoal
  · exact hq  -- Second subgoal
```

**Key differences:**

- `exact` requires the term to exactly match the goal
- `apply` can create subgoals if the applied term needs arguments

### `rw` and `simp`

**Purpose**: Rewrite using equalities and simplify expressions.

```lean
-- Basic rewriting
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]  -- Replace a with b using hypothesis h

-- Multiple rewrites
example (a b c d : Nat) (h1 : a = b) (h2 : c = d) : a + c = b + d := by
  rw [h1, h2]  -- Apply both rewrites

-- Backward rewriting
example (a b : Nat) (h : a = b) : b = a := by
  rw [← h]  -- Use h in reverse direction

-- Rewriting with library theorems
example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]  -- Use commutativity from the library

-- Conditional rewriting
example (a b c : Nat) (h : a = b) (hpos : c > 0) : a * c = b * c := by
  rw [h]

-- simp for automatic simplification
example (a b : Nat) : a + 0 + b * 1 = a + b := by
  simp  -- Simplifies a + 0 to a and b * 1 to b

-- simp with additional lemmas
example (a b : Nat) (h : a = 0) : a + b = b := by
  simp [h]  -- Use h as an additional simplification rule
```

**Key patterns:**

- `rw [h]` - rewrite using hypothesis h
- `rw [← h]` - rewrite using h in reverse
- `rw [h1, h2, h3]` - multiple rewrites
- `simp` - automatic simplification
- `simp [h]` - simplify using additional lemmas

### `constructor` and Destructuring

**Purpose**: Build and break down structured data.

```lean
-- Building conjunctions
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor  -- Creates two goals: ⊢ P and ⊢ Q
  · exact hp
  · exact hq

-- Building disjunctions (manual choice)
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left        -- Choose left side of disjunction
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right       -- Choose right side of disjunction
  exact hq

-- Building existentials
example : ∃ n : Nat, n > 5 := by
  use 6       -- Provide witness
  norm_num    -- Prove 6 > 5

-- Destructuring in intro
example (P Q R : Prop) : P ∧ Q → P ∨ R := by
  intro ⟨hp, hq⟩  -- Destructure the conjunction
  left
  exact hp

-- Destructuring in cases
example (P Q R : Prop) (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  cases h with
  | inl hp => exact hpr hp  -- Case: P is true
  | inr hq => exact hqr hq  -- Case: Q is true
```

## Working with Hypotheses

These tactics help manage and create new hypotheses.

### `have` and `let`

**Purpose**: Create intermediate results and local definitions.

```lean
-- have: prove an intermediate lemma
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  have hq : Q := h1 hp     -- Prove Q as intermediate result
  exact h2 hq              -- Use Q to prove R

-- Anonymous have
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  have : a = b := h1       -- Anonymous intermediate result
  rw [this, h2]

-- let: local definition
example (n : Nat) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  let m := n + 1           -- Local definition
  show m * m = n * n + 2 * n + 1
  ring                     -- Algebraic manipulation

-- have with tactics
example (a b : Nat) (h : a = b) : a + a = 2 * b := by
  have h' : a = b := by
    exact h                -- Prove the have statement
  rw [h', ← Nat.two_mul]
```

### `use` for Existentials

**Purpose**: Provide witnesses for existential statements.

```lean
-- Basic existential proof
example : ∃ n : Nat, n * n = 9 := by
  use 3      -- Provide witness n = 3
  norm_num   -- Prove 3 * 3 = 9

-- Multiple witnesses
example : ∃ (m n : Nat), m + n = 7 ∧ m * n = 12 := by
  use 3, 4   -- Provide both witnesses
  constructor
  · norm_num  -- Prove 3 + 4 = 7
  · norm_num  -- Prove 3 * 4 = 12

-- Computed witness
example (n : Nat) : ∃ m : Nat, m = 2 * n := by
  use 2 * n  -- Witness is computed from n
  rfl        -- 2 * n = 2 * n by reflexivity

-- Existential with dependent type
example : ∃ f : Nat → Nat, f 0 = 5 ∧ f 1 = 10 := by
  use fun n => 5 * (n + 1)  -- Provide function as witness
  constructor
  · simp  -- f 0 = 5 * 1 = 5
  · simp  -- f 1 = 5 * 2 = 10
```

### `assumption` and `trivial`

**Purpose**: Use existing hypotheses or solve trivial goals.

```lean
-- assumption: find matching hypothesis automatically
example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : Q := by
  assumption  -- Finds hq : Q automatically

-- When multiple hypotheses could work
example (P : Prop) (h1 h2 : P) : P := by
  assumption  -- Uses first available proof

-- trivial: solve obviously true goals
example : True := by
  trivial

example : 2 + 2 = 4 := by
  trivial  -- Sometimes works for definitional equalities

-- assumption is useful after case analysis
example (P Q : Prop) (h : P ∨ Q) : P ∨ Q := by
  assumption  -- h is exactly what we need
```

## Case Analysis and Induction

These tactics handle structured reasoning.

### `cases` and Pattern Matching

**Purpose**: Analyze data by cases and handle disjunctions.

```lean
-- Basic case analysis on disjunction
example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hpr hqr
  cases h with
  | inl hp => exact hpr hp  -- Case: P is true
  | inr hq => exact hqr hq  -- Case: Q is true

-- Case analysis on natural numbers
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero =>
    left
    rfl                     -- n = 0
  | succ k =>
    right
    exact Nat.zero_lt_succ k  -- succ k > 0

-- Case analysis on lists
example (α : Type) (l : List α) : l = [] ∨ ∃ (h : α) (t : List α), l = h :: t := by
  cases l with
  | nil =>
    left
    rfl
  | cons h t =>
    right
    use h, t
    rfl

-- Case analysis on propositions with decidable instances
example (P : Prop) [Decidable P] (hpos : P → True) (hneg : ¬P → True) : True := by
  cases ‹Decidable P› with
  | isTrue hp => exact hpos hp
  | isFalse hnp => exact hneg hnp

-- Nested case analysis
example (P Q : Prop) : (P ∨ Q) ∨ (P ∧ Q) → P ∨ Q := by
  intro h
  cases h with
  | inl hpq => exact hpq      -- Already have P ∨ Q
  | inr hpq =>
    cases hpq with
    | intro hp hq =>          -- Have both P and Q
      left
      exact hp
```

### `induction` and Recursive Proofs

**Purpose**: Prove statements about inductive types.

```lean
-- Basic induction on natural numbers
example (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
    rfl                       -- Base case: 0 + 0 = 0
  | succ k ih =>
    rw [Nat.succ_add, ih]     -- Inductive case: use ih : k + 0 = k
    rfl

-- Induction with more complex goal
example (n : Nat) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero =>
    simp [List.range, List.sum]
  | succ k ih =>
    rw [List.range_succ, List.sum_cons, ih]
    ring  -- Algebra to finish the proof

-- Induction on lists
example (α : Type) (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil =>
    simp [List.reverse]
  | cons h t ih =>
    simp [List.reverse, ih]

-- Strong induction (well-founded recursion)
example (n : Nat) : n < n + 1 := by
  induction n using Nat.strong_induction_on with
  | ind k ih =>
    exact Nat.lt_succ_self k

-- Mutual induction (for mutually defined types)
mutual
  example (n : Nat) : even n ∨ odd n := by
    induction n with
    | zero =>
      left
      exact even_zero
    | succ k ih =>
      cases ih with
      | inl heven =>
        right
        exact odd_succ_of_even heven
      | inr hodd =>
        left
        exact even_succ_of_odd hodd

  def even : Nat → Prop
  | 0 => True
  | n + 1 => odd n

  def odd : Nat → Prop
  | 0 => False
  | n + 1 => even n
end
```

### `by_cases` for Decidable Props

**Purpose**: Split on decidable propositions using law of excluded middle.

```lean
-- Basic case split
example (P Q : Prop) [Decidable P] : P ∨ ¬P := by
  by_cases h : P
  · left; exact h       -- Case: P is true
  · right; exact h      -- Case: P is false

-- Using case split in larger proof
example (n : Nat) : n = 0 ∨ n > 0 := by
  by_cases h : n = 0
  · left; exact h       -- Case: n = 0
  · right               -- Case: n ≠ 0
    cases n with
    | zero => contradiction  -- But we assumed n ≠ 0
    | succ k => exact Nat.zero_lt_succ k

-- Multiple case splits
example (P Q : Prop) [Decidable P] [Decidable Q] : P ∨ Q ∨ (¬P ∧ ¬Q) := by
  by_cases hp : P
  · left; exact hp
  · by_cases hq : Q
    · right; left; exact hq
    · right; right; exact ⟨hp, hq⟩
```

## Computational Tactics

These tactics leverage Lean's computational capabilities.

### `rfl` and Definitional Equality

**Purpose**: Prove goals that hold by definition or computation.

```lean
-- Basic reflexivity
example (a : Nat) : a = a := rfl

-- Computational equality
example : 2 + 2 = 4 := rfl
example : List.length [1, 2, 3] = 3 := rfl

-- Definitional unfolding
def double (n : Nat) : Nat := n + n

example : double 3 = 6 := rfl  -- Unfolds double 3 = 3 + 3 = 6

-- With more complex computation
def factorial : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * factorial n

example : factorial 4 = 24 := rfl  -- Computes 4! = 24

-- Beta reduction
example : (fun x : Nat => x + 1) 5 = 6 := rfl

-- Eta conversion
example (f : Nat → Nat) : (fun x => f x) = f := rfl
```

### `decide` for Decidable Goals

**Purpose**: Prove decidable propositions by computation.

```lean
-- Decidable equality
example : (5 : Nat) = 5 := by decide
example : ¬((3 : Nat) = 7) := by decide

-- Decidable ordering
example : (10 : Nat) < 20 := by decide
example : ¬((15 : Nat) ≤ 10) := by decide

-- Boolean propositions
example : true ∧ ¬false := by decide
example : true ∨ false ↔ true := by decide

-- Complex decidable statements
example : List.length [1, 2, 3, 4, 5] > 3 := by decide
example : 17 ∈ List.range 20 := by decide

-- Arithmetic
example : (2 + 2) * (3 + 1) = 16 := by decide
example : 23 % 7 = 2 := by decide

-- In combination with other tactics
example (n : Nat) (h : n = 5) : n < 10 := by
  rw [h]
  decide  -- Prove 5 < 10
```

### `norm_num` for Numerical Goals

**Purpose**: Normalize and simplify numerical expressions.

```lean
-- Basic numerical computation
example : (2 : ℚ) + 3 = 5 := by norm_num
example : (1.5 : ℝ) * 4 = 6 := by norm_num

-- Comparisons
example : (17 : ℤ) < 25 := by norm_num
example : (3.14 : ℝ) > 3 := by norm_num

-- Fractions
example : (1 : ℚ) / 2 + 1 / 3 = 5 / 6 := by norm_num
example : (0.25 : ℝ) = 1 / 4 := by norm_num

-- Powers and roots
example : (2 : ℝ) ^ 10 = 1024 := by norm_num
example : Real.sqrt 9 = 3 := by norm_num

-- Mixed with variables
example (x : ℝ) (h : x = 2.5) : x + 1.5 = 4 := by
  rw [h]
  norm_num

-- Complex expressions
example : (12 : ℚ) / 8 * 16 / 3 = 8 := by norm_num
```

## Automation Tactics

These tactics provide powerful automation for common proof patterns.

### `simp` Advanced Usage

**Purpose**: Simplify expressions using rewrite rules.

```lean
-- Basic simplification
example (a b : Nat) : a + 0 + (b * 1) = a + b := by simp

-- With hypotheses
example (a b c : Nat) (h : a = b) : a + c = b + c := by simp [h]

-- Custom simp lemmas
@[simp] def my_double (n : Nat) : Nat := 2 * n

example : my_double 5 + my_double 3 = 16 := by simp [my_double]; norm_num

-- Contextual simp
example (P : Prop) (h : P) : P ∧ True ↔ P := by simp [h]

-- simp only with specific lemmas
example (a b : Nat) : a + b + 0 = b + a := by
  simp only [Nat.add_zero, Nat.add_comm]

-- simp with arithmetical simplification
example (a b c : Nat) : (a + b) + c = a + (b + c) := by simp [Nat.add_assoc]

-- Conditional simp
example (n : Nat) (h : n > 0) : n + 0 = n := by simp
```

### `ring` for Algebra

**Purpose**: Solve ring equations automatically.

```lean
-- Basic ring operations
example (a b c : ℤ) : (a + b) * c = a * c + b * c := by ring

-- Polynomial identities
example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring

-- Complex algebraic manipulation
example (a b c : ℚ) : (a + b + c)^2 = a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*a*c := by ring

-- With assumptions
example (a b : ℝ) (h : a = 2*b) : a^2 = 4*b^2 := by
  rw [h]
  ring

-- Mixed with other tactics
example (n : Nat) : (n + 1)^2 = n^2 + 2*n + 1 := by
  ring_nf  -- Ring normal form
  rfl
```

### `linarith` for Linear Arithmetic

**Purpose**: Solve linear arithmetic problems.

```lean
-- Basic linear inequalities
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b < c) : a < c := by linarith

-- Multiple constraints
example (x y z : ℚ) (h1 : x + y = 10) (h2 : y + z = 15) (h3 : x + z = 20) :
  x = 7.5 ∧ y = 2.5 ∧ z = 12.5 := by
  linarith  -- Solves the system of equations

-- With multiplication by constants
example (a b : ℝ) (h1 : 2*a + 3*b ≤ 10) (h2 : a ≥ 1) (h3 : b ≥ 2) : a + b ≤ 5 := by
  linarith

-- Contradiction detection
example (x : ℝ) (h1 : x < 5) (h2 : x > 10) : False := by linarith

-- With case analysis
example (a b : ℝ) : max a b ≥ a := by
  by_cases h : a ≤ b
  · simp [max_def, h]; linarith
  · simp [max_def, h]; linarith
```

## Tactic Combinators

These help combine and control tactics.

### Sequencing with `;` and `<;>`

**Purpose**: Apply tactics in sequence or to all goals.

```lean
-- Basic sequencing
example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h; exact p  -- Apply h, then exact p to the resulting goal

-- Apply to all goals
example (P Q R S : Prop) (hp : P) (hq : Q) (hr : R) (hs : S) : (P ∧ Q) ∧ (R ∧ S) := by
  constructor <;> constructor <;> assumption
  -- constructor creates 2 goals
  -- <;> constructor applies constructor to both goals (creates 4 goals total)
  -- <;> assumption applies assumption to all 4 goals

-- Conditional application
example (a b c : Nat) : a + b = b + a ∧ b + c = c + b ∧ a + c = c + a := by
  constructor <;> [rw [Nat.add_comm]; constructor <;> rw [Nat.add_comm]]

-- Error handling
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left; exact hp
  <|> (right; assumption)  -- Try left; if it fails, try right
```

### Goal Management

**Purpose**: Handle multiple goals systematically.

```lean
-- Focus on specific goals
example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R := by
  constructor
  · exact hp      -- Focus on first goal
  constructor
  · exact hq      -- Focus on second goal
  · exact hr      -- Focus on third goal

-- All goals simultaneously
example (P Q R S : Prop) (h : P ∧ Q ∧ R ∧ S) : S ∧ R ∧ Q ∧ P := by
  constructor <;> [exact h.2.2.2; constructor <;> [exact h.2.2.1; constructor <;> [exact h.2.1; exact h.1]]]

-- Swap goals
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  swap  -- Changes order of goals
  · exact hq
  · exact hp

-- Rotate goals
example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R := by
  constructor
  · exact hp
  rotate_left  -- Rotate remaining goals
  · exact hr
  · exact hq
```

### Error Handling

**Purpose**: Handle failing tactics gracefully.

```lean
-- Try alternative tactics
example (P : Prop) [Decidable P] : P ∨ ¬P := by
  first
  | left; assumption
  | right; assumption
  | by_cases h : P <;> [left; exact h | right; exact h]

-- Optional tactics
example (n : Nat) : n + 0 = n := by
  try rw [Nat.add_zero]  -- Try this, continue even if it fails
  rfl

-- Repeat until failure
example (a b c : Nat) : a + (b + (c + 0)) = a + b + c := by
  repeat rw [Nat.add_zero]
  simp [Nat.add_assoc]

-- Success continuation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro hp hq =>
    success_if_progress exact ⟨hq, hp⟩  -- Only succeed if progress made
```

## Debugging and Exploration

**Purpose**: Understand proof states and debug failures.

```lean
-- Trace proof state
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  trace_state  -- Print current proof state
  apply h2
  trace_state  -- Print proof state after apply
  apply h1
  trace_state  -- Print proof state after second apply
  exact hp

-- Check goal type
example (n : Nat) : n + 0 = n := by
  guard_target =ₛ n + 0 = n  -- Verify goal is as expected
  simp

-- Check hypothesis
example (P Q : Prop) (h : P ∧ Q) : P := by
  guard_hyp h : P ∧ Q  -- Verify h has expected type
  exact h.1

-- Admit impossible goals (for exploration)
example (P : Prop) : P := by
  admit  -- Give up on this goal (for debugging)

-- Show intermediate terms
example (a b : Nat) : a + b = b + a := by
  show a + b = b + a  -- Make goal explicit
  rw [Nat.add_comm]
```

## Advanced Patterns

### Term-Mode Integration

**Purpose**: Mix tactic and term modes.

```lean
-- Embed terms in tactics
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  exact h2 (h1 hp)  -- Term-mode proof within tactic

-- Embed tactics in terms
def my_proof (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

-- Mixed approach
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [show a = b from h1, h2]  -- Mix rw with term-mode proof

-- Convert between modes
example (P Q : Prop) : P → Q → P ∧ Q :=
  fun hp hq => by exact ⟨hp, hq⟩  -- Term mode calling tactic mode
```

### Meta-Programming Basics

**Purpose**: Write custom tactics.

```lean
-- Simple custom tactic
macro "my_assumption" : tactic => `(tactic| first | assumption | rfl)

example (P : Prop) (h : P) : P := by my_assumption
example : True := by my_assumption

-- Parameterized tactic
macro "apply_twice " t:term : tactic => `(tactic| (apply $t; apply $t))

example (P Q R : Prop) (h : P → Q) (h' : Q → R) (hp : P) : R := by
  sorry  -- apply_twice would need more sophisticated implementation

-- Tactic notation
notation:max "solve_goal" => assumption <|> rfl <|> simp

example (n : Nat) : n + 0 = n := by solve_goal
```

These tactics form the foundation for all theorem proving in Lean. Mastery of these essential tools enables you to tackle the logical and mathematical proofs in subsequent chapters. Practice with simple examples first, then gradually work up to more complex mathematical statements.

---

[Debugging](./Proofs.debugging.html)
