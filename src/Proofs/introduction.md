---

[Contents](contents.html)
[Previous](Types.identity.html)
[Next](Proofs.tactics.html)

# Introduction to Theorem Proving in Lean

---

- [Proofs as Programs](#proofs-as-programs)
- [The Proof Assistant Paradigm](#the-proof-assistant-paradigm)
- [Term Mode vs Tactic Mode](#term-mode-vs-tactic-mode)
  - [Term Mode: Direct Construction](#term-mode-direct-construction)
  - [Tactic Mode: Interactive Construction](#tactic-mode-interactive-construction)
- [Propositions as Types Revisited](#propositions-as-types-revisited)
- [The Curry-Howard Correspondence](#the-curry-howard-correspondence)
- [Interactive Theorem Proving](#interactive-theorem-proving)
- [Proof States and Goals](#proof-states-and-goals)
- [Types of Mathematical Reasoning](#types-of-mathematical-reasoning)
  - [Direct Proof](#direct-proof)
  - [Proof by Cases](#proof-by-cases)
  - [Proof by Induction](#proof-by-induction)
  - [Proof by Contradiction](#proof-by-contradiction)
- [Constructive vs Classical Proofs](#constructive-vs-classical-proofs)
- [The Lean Proof Assistant](#the-lean-proof-assistant)
  - [Syntax and Notation](#syntax-and-notation)
  - [Library Integration](#library-integration)
  - [Error Messages and Suggestions](#error-messages-and-suggestions)
- [Your First Proofs](#your-first-proofs)
- [The Journey Ahead](#the-journey-ahead)

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Decide
import Mathlib.Tactic.Ring
```

Mathematics has always been concerned with **proof**—rigorous arguments that establish the truth of mathematical statements. However, traditional mathematical proofs, while logically sound, are often informal and rely on human intuition to fill in gaps. **Theorem proving** in type theory represents a revolutionary approach: proofs become **programs**, mathematical statements become **types**, and the process of proving becomes **programming**.

In Lean, we don't just write proofs—we **construct** them as computational objects that can be executed, verified, and reasoned about mechanically. This chapter introduces you to this paradigm, showing how the abstract concepts from previous chapters translate into concrete proof techniques.

## Proofs as Programs

The most profound insight in modern logic is that **proofs are programs** and **programs are proofs**. This isn't just a philosophical observation—it's a practical reality that fundamentally changes how we approach mathematics.

```lean
-- A mathematical statement
def statement : Prop := ∀ n : Nat, n + 0 = n

-- A proof of that statement (which is a program!)
def proof_of_statement : statement := fun n => rfl

-- We can "run" this proof
#check proof_of_statement 5  -- 5 + 0 = 5
#eval proof_of_statement 5   -- This is actually a proof term!
```

When you prove a theorem in Lean, you're writing a program that:

- **Inputs**: The hypotheses of the theorem
- **Outputs**: A proof of the conclusion
- **Correctness**: Guaranteed by the type system

This means every proof is:

- **Executable**: It can be run like any program
- **Verifiable**: The type checker ensures correctness
- **Compositional**: Proofs can be combined like functions
- **Reusable**: Once proven, theorems become tools for other proofs

## The Proof Assistant Paradigm

Traditional mathematics:

```bash
Mathematician states theorem → Writes informal proof → Peer review → Acceptance
```

Formal mathematics with Lean:

```bash
Mathematician states theorem → Constructs formal proof → Type checker verification → Absolute certainty
```

Lean acts as your **mathematical partner**, not just a tool:

```lean
-- Lean helps you explore what you need to prove
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  -- At this point, Lean shows you:
  -- a b c : Nat
  -- h1 : a = b
  -- h2 : b = c
  -- ⊢ a = c
  sorry  -- We'll fill this in soon!

-- Lean provides feedback as you construct the proof
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]  -- Goal becomes: b = c
  exact h2 -- Goal solved!
```

## Term Mode vs Tactic Mode

Lean offers two primary ways to construct proofs:

### Term Mode: Direct Construction

In term mode, you directly write the proof term:

```lean
-- Direct proof construction
def transitivity_term (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  h1 ▸ h2  -- Using transport (substitution)

-- More explicitly
def transitivity_term' (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  Eq.trans h1 h2
```

### Tactic Mode: Interactive Construction

In tactic mode, you build proofs step-by-step with guidance:

```lean
-- Interactive proof construction
def transitivity_tactic (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]    -- Rewrite using h1
  exact h2   -- Use h2 directly
```

**When to use each:**

- **Term mode**: When you know exactly what proof term you want
- **Tactic mode**: When you want to explore and build proofs interactively
- **Mixed**: You can combine both approaches freely

## Propositions as Types Revisited

We've seen this principle before, but let's see how it manifests in theorem proving:

```lean
-- A proposition is a type
#check (2 + 2 = 4 : Prop)

-- A proof is a term of that type
def my_proof : 2 + 2 = 4 := rfl

-- Multiple proofs can exist for the same proposition
def another_proof : 2 + 2 = 4 := Eq.refl (2 + 2)

-- But in Prop, all proofs are "equal" (proof irrelevance)
example : my_proof = another_proof := rfl

-- False propositions have no proofs (uninhabited types)
-- def impossible : 1 = 0 := -- No way to complete this!

-- Some propositions require more complex proofs
def commutativity : ∀ a b : Nat, a + b = b + a := by
  intro a b
  induction a with
  | zero => simp [Nat.zero_add]
  | succ n ih =>
    rw [Nat.succ_add, ih, Nat.add_succ]
```

## The Curry-Howard Correspondence

This correspondence is your roadmap for translating logical concepts into computational ones:

```lean
-- Implication ≡ Function Type
def modus_ponens (P Q : Prop) : P → (P → Q) → Q :=
  fun hp hpq => hpq hp

-- Conjunction ≡ Product Type
def and_intro (P Q : Prop) : P → Q → (P ∧ Q) :=
  fun hp hq => ⟨hp, hq⟩

def and_elim_left (P Q : Prop) : (P ∧ Q) → P :=
  fun ⟨hp, _⟩ => hp

-- Disjunction ≡ Sum Type
def or_intro_left (P Q : Prop) : P → (P ∨ Q) :=
  fun hp => Or.inl hp

def or_elimination (P Q R : Prop) : (P ∨ Q) → (P → R) → (Q → R) → R :=
  fun hpq hpr hqr => match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq

-- Universal quantification ≡ Dependent function type
def forall_intro (α : Type) (P : α → Prop) : (∀ x, P x) → ((x : α) → P x) :=
  fun h => h

-- Existential quantification ≡ Dependent pair type
def exists_intro (α : Type) (P : α → Prop) (a : α) (ha : P a) : ∃ x, P x :=
  ⟨a, ha⟩

def exists_elim (α : Type) (P : α → Prop) (R : Prop) :
  (∃ x, P x) → (∀ x, P x → R) → R :=
  fun ⟨a, ha⟩ h => h a ha
```

## Interactive Theorem Proving

One of Lean's greatest strengths is its **interactive** nature. The system provides continuous feedback as you build proofs:

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : c = d) : a + c = b + d := by
  -- 1. Initial goal: a + c = b + d
  -- 2. Available hypotheses: h1 : a = b, h2 : c = d
  rw [h1]  -- Goal becomes: b + c = b + d
  rw [h2]  -- Goal becomes: b + d = b + d
  rfl      -- Goal solved by reflexivity!
```

The proof state shows:

- **Current goals**: What you need to prove
- **Hypotheses**: What you can use
- **Context**: Available types and definitions
- **Error messages**: Guidance when things go wrong

## Proof States and Goals

Understanding proof states is crucial for effective theorem proving:

```lean
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  -- Proof state:
  -- P Q R : Prop
  -- h1 : P → Q
  -- h2 : Q → R
  -- hp : P
  -- ⊢ R

  have hq : Q := h1 hp  -- Introduce intermediate result
  -- Proof state now includes: hq : Q

  exact h2 hq  -- Apply h2 to hq
```

Key concepts:

- **⊢ symbol**: "Proves" or "goal"
- **Hypotheses**: Above the line, available for use
- **Goal**: Below the line, what needs to be proven
- **Multiple goals**: Some tactics create several subgoals

## Types of Mathematical Reasoning

Lean supports all major forms of mathematical reasoning:

### Direct Proof

```lean
example (n : Nat) : n ≤ n + 1 := by
  -- Directly show n ≤ n + 1
  exact Nat.le_add_right n 1
```

### Proof by Cases

```lean
example (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (Nat.zero_lt_succ k)
```

### Proof by Induction

```lean
example (n : Nat) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [List.range_succ_eq, List.sum_cons, ih]
    ring
```

### Proof by Contradiction

```lean
example (n : Nat) : ¬(n < n) := by
  intro h  -- Assume n < n
  -- This leads to contradiction by irreflexivity of <
  exact Nat.lt_irrefl n h
```

## Constructive vs Classical Proofs

Lean primarily uses **constructive** logic, but classical principles are available:

```lean
-- Constructive: to prove existence, provide a witness
example : ∃ n : Nat, n > 10 := ⟨11, by norm_num⟩

-- Classical: can prove existence without explicit witness
open Classical

example : ∃ n : Nat, n = 0 ∨ n ≠ 0 := by
  by_cases h : ∃ n, n = 0
  · exact h.elim (fun w hw => ⟨w, Or.inl hw⟩)
  · use 1; right; norm_num

-- Law of excluded middle (classical)
#check em  -- ∀ (p : Prop), p ∨ ¬p

-- Double negation elimination (classical)
example (P : Prop) : ¬¬P → P := not_not
```

## The Lean Proof Assistant

Lean provides an integrated development environment for mathematics:

### Syntax and Notation

```lean
-- Mathematical notation is supported
example (x y : ℝ) : x ≤ y ∧ y ≤ x → x = y := by
  intro ⟨h1, h2⟩
  exact le_antisymm h1 h2

-- Unicode and ASCII alternatives
example (P Q : Prop) : P ∧ Q ↔ Q ∧ P := And.comm
example (P Q : Prop) : P /\ Q <-> Q /\ P := And.comm  -- ASCII version
```

### Library Integration

```lean
-- Vast mathematical library (Mathlib)
#check Nat.gcd_comm           -- ∀ (m n : ℕ), gcd m n = gcd n m
#check Real.pi_pos            -- 0 < π
#check List.length_append     -- ∀ {α : Type*} (s t : List α), (s ++ t).length = s.length + t.length
```

### Error Messages and Suggestions

```lean
example (n : Nat) : n + 1 = 1 + n := by
  -- rw [add_comm]  -- Error: ambiguous, multiple add_comm theorems
  rw [Nat.add_comm]  -- Specific theorem
```

## Your First Proofs

Let's build some simple proofs to get hands-on experience:

```lean
-- Reflexivity of equality
example (a : Nat) : a = a := rfl

-- Symmetry of equality
example (a b : Nat) : a = b → b = a := by
  intro h
  exact h.symm

-- Transitivity of equality
example (a b c : Nat) : a = b → b = c → a = c := by
  intro h1 h2
  rw [h1, h2]

-- Simple logical reasoning
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩  -- Destructure the conjunction
  exact ⟨hq, hp⟩  -- Construct the swapped conjunction

-- Working with natural numbers
example (n : Nat) : n + 0 = n := by
  simp  -- Simplification handles this automatically

-- A slightly more complex example
example (a b : Nat) (h : a = b) : a + a = b + b := by
  rw [h]  -- Replace a with b everywhere
```

## The Journey Ahead

This introduction has shown you the **conceptual foundations** of theorem proving in Lean. In the following sections, you'll learn:

1. **Basic Tactics**: The essential tools for proof construction
2. **Advanced Techniques**: Powerful automation and specialized tactics
3. **Proof Strategies**: Systematic approaches to complex proofs
4. **Computational Proofs**: Using decidability and reflection

Remember: theorem proving in Lean is both an **art** and a **craft**. The art lies in seeing the logical structure of mathematical arguments. The craft lies in effectively using Lean's tools to construct formal proofs. Both develop with practice and experience.

Every proof you write makes you both a better mathematician and a better programmer. In Lean, these are the same thing.

---

[Basic Tactics](./Proofs.tactics.html)
