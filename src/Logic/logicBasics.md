---

[Contents](contents.html)
[Previous](Logic.introduction.html)
[Next](Logic.equality.html)

# Boolean Algebra and Logical Connectives

---

- [Two Faces of Logic](#two-faces-of-logic)
- [Propositional Logic](#propositional-logic)
  - [False and True](#false-and-true)
  - [Conjunction (AND)](#conjunction-and)
  - [Disjunction (OR)](#disjunction-or)
  - [Negation (NOT)](#negation-not)
  - [Implication](#implication)
- [Boolean Algebra](#boolean-algebra)
  - [The Bool Type](#the-bool-type)
  - [Boolean Operations](#boolean-operations)
  - [Boolean vs Propositional](#boolean-vs-propositional)
- [Advanced Logical Connectives](#advanced-logical-connectives)
  - [Bi-implication (If and Only If)](#bi-implication-if-and-only-if)
  - [Exclusive Or (XOR)](#exclusive-or-xor)
  - [Sheffer Stroke (NAND)](#sheffer-stroke-nand)
- [Quantifiers](#quantifiers)
  - [Universal Quantification](#universal-quantification)
  - [Existential Quantification](#existential-quantification)
  - [Unique Existence](#unique-existence)
- [Classical Extensions](#classical-extensions)

```lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Logic.Function.Basic
```

In type theory, logic manifests in two complementary forms: as **propositions** (types in `Prop`) that we prove by constructing inhabitants, and as **boolean values** (terms of type `Bool`) that we compute. This duality mirrors the distinction between **proof** and **computation**, offering both rigorous logical reasoning and practical algorithmic tools.

## Two Faces of Logic

Lean provides two distinct but related approaches to logic:

1. **Propositional Logic**: Using the `Prop` universe for statements we prove
2. **Boolean Algebra**: Using the `Bool` type for values we compute

```lean
-- Propositional approach: proving relationships
example : True ∧ True := ⟨trivial, trivial⟩

-- Boolean approach: computing results
example : true && true = true := rfl

-- Connection between them
example : (true = true) ↔ True := ⟨fun _ => trivial, fun _ => rfl⟩
```

## Propositional Logic

### False and True

The foundation of propositional logic rests on two primitive concepts:

**False** (`False`) represents an impossible proposition—one for which no proof can exist:

```lean
-- False has no constructors, so no proof can be built
#print False
-- inductive False : Prop

-- From False, anything follows (ex falso quodlibet)
def false_implies_anything (P : Prop) : False → P :=
  fun false_proof => False.elim false_proof

-- This is the same as:
#check False.elim -- False.elim : {C : Sort u} → False → C
```

**True** (`True`) represents a trivially provable proposition:

```lean
-- True has one constructor: True.intro
#print True
-- inductive True : Prop
-- | intro : True

-- We can always construct a proof of True
def true_is_provable : True := True.intro

-- Often abbreviated as:
def true_is_provable' : True := trivial
```

### Conjunction (AND)

Conjunction (`And`, written `∧`) combines two propositions—both must be proven:

```lean
-- And has one constructor requiring proofs of both components
#print And
-- structure And (a b : Prop) : Prop where
-- | intro :: (left : a) (right : b)

-- Constructing a conjunction
def and_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq

-- Anonymous constructor syntax
def and_example' (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- Destructuring a conjunction
def and_left (P Q : Prop) : P ∧ Q → P :=
  fun ⟨hp, hq⟩ => hp

def and_right (P Q : Prop) : P ∧ Q → Q :=
  fun ⟨hp, hq⟩ => hq

-- Built-in destructors
#check And.left  -- {a b : Prop} → a ∧ b → a
#check And.right -- {a b : Prop} → a ∧ b → b
```

### Disjunction (OR)

Disjunction (`Or`, written `∨`) represents a choice between two propositions—at least one must be proven:

```lean
-- Or has two constructors, one for each alternative
#print Or
-- inductive Or (a b : Prop) : Prop where
-- | inl : a → a ∨ b
-- | inr : b → a ∨ b

-- Constructing disjunctions
def or_left_example (P Q : Prop) (hp : P) : P ∨ Q := Or.inl hp
def or_right_example (P Q : Prop) (hq : Q) : P ∨ Q := Or.inr hq

-- Destructuring with case analysis
def or_elimination (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R :=
  fun h hpr hqr => match h with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq

-- This is built-in as Or.elim
#check Or.elim -- {a b c : Prop} → a ∨ b → (a → c) → (b → c) → c
```

### Negation (NOT)

Negation (`Not`, written `¬`) represents the impossibility of a proposition:

```lean
-- Negation is defined in terms of False
#print Not
-- def Not : Prop → Prop :=
-- fun a => a → False

-- So ¬P means P → False
def not_example (P : Prop) : ¬P ↔ (P → False) := Iff.rfl

-- Double negation introduction (always valid constructively)
def double_negation_intro (P : Prop) : P → ¬¬P :=
  fun hp hnp => hnp hp

-- Double negation elimination (requires classical logic)
-- def double_negation_elim (P : Prop) : ¬¬P → P := Classical.not_not

-- Contradiction gives us anything
def contradiction (P Q : Prop) : P → ¬P → Q :=
  fun hp hnp => False.elim (hnp hp)
```

### Implication

Implication is built into type theory as the function type `→`:

```lean
-- P → Q is a function type: given P, produce Q
def modus_ponens (P Q : Prop) : P → (P → Q) → Q :=
  fun hp hpq => hpq hp

-- Implication is transitive
def implication_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
  fun hpq hqr hp => hqr (hpq hp)

-- Contraposition
def contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  fun hpq hnq hp => hnq (hpq hp)
```

## Boolean Algebra

### The Bool Type

The `Bool` type provides computational logic with two constructors:

```lean
#print Bool
-- inductive Bool : Type where
-- | false : Bool
-- | true : Bool

-- Pattern matching on booleans
def bool_to_prop : Bool → Prop
  | true  => True
  | false => False

-- Decidable propositions can be computed as booleans
def is_even_bool (n : Nat) : Bool := n % 2 = 0
```

### Boolean Operations

Boolean operations mirror propositional logic but compute values:

```lean
-- Boolean AND
#check Bool.and  -- Bool → Bool → Bool
#check (· && ·)  -- Bool → Bool → Bool  (infix notation)

-- Truth table for &&
example : true && true = true := rfl
example : true && false = false := rfl
example : false && true = false := rfl
example : false && false = false := rfl

-- Boolean OR
#check Bool.or   -- Bool → Bool → Bool
#check (· || ·)  -- Bool → Bool → Bool  (infix notation)

-- Truth table for ||
example : true || true = true := rfl
example : true || false = true := rfl
example : false || true = true := rfl
example : false || false = false := rfl

-- Boolean NOT
#check Bool.not  -- Bool → Bool
#check not       -- Bool → Bool (alternative notation)

-- Truth table for not
example : not true = false := rfl
example : not false = true := rfl

-- Boolean implication (not built-in, but can be defined)
def bool_implies : Bool → Bool → Bool
  | true, b => b
  | false, _ => true

-- Boolean XOR
def bool_xor : Bool → Bool → Bool
  | true, b => not b
  | false, b => b

-- This is available as ⊕ in mathlib
#check Bool.xor -- Bool → Bool → Bool
```

### Boolean vs Propositional

The connection between boolean and propositional logic:

```lean
-- Convert Bool to Prop
def bool_to_prop_fn : Bool → Prop := (· = true)

-- Every boolean computation corresponds to a decidable proposition
def bool_and_prop (b c : Bool) :
  (b && c = true) ↔ (b = true ∧ c = true) := by
  cases b <;> cases c <;> simp

def bool_or_prop (b c : Bool) :
  (b || c = true) ↔ (b = true ∨ c = true) := by
  cases b <;> cases c <;> simp [or_comm]

-- For decidable propositions, we can go both ways
variable [Decidable P] [Decidable Q]

#check decide P  -- Bool (computes whether P holds)
```

## Advanced Logical Connectives

### Bi-implication (If and Only If)

Bi-implication (`Iff`, written `↔`) means both directions of implication:

```lean
-- Iff is conjunction of both implications
#print Iff
-- structure Iff (a b : Prop) : Prop where
-- | intro :: (mp : a → b) (mpr : b → a)

def iff_example (P Q : Prop) : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
  ⟨fun ⟨hpq, hqp⟩ => ⟨hpq, hqp⟩, fun ⟨hpq, hqp⟩ => ⟨hpq, hqp⟩⟩

-- Iff is an equivalence relation
def iff_refl (P : Prop) : P ↔ P := ⟨id, id⟩
def iff_symm (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := fun ⟨hpq, hqp⟩ => ⟨hqp, hpq⟩
def iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  fun ⟨hpq, hqp⟩ ⟨hqr, hrq⟩ => ⟨hqr ∘ hpq, hqp ∘ hrq⟩
```

### Exclusive Or (XOR)

Exclusive or means exactly one of two propositions holds:

```lean
-- Define XOR propositionally
def Xor (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

-- Alternative definition
def Xor' (P Q : Prop) : Prop := (P ∧ ¬Q) ∨ (¬P ∧ Q)

-- Show equivalence
theorem xor_equiv (P Q : Prop) : Xor P Q ↔ Xor' P Q := by
  constructor
  · intro ⟨h_or, h_not_and⟩
    cases h_or with
    | inl hp =>
      right; exact ⟨fun hq => h_not_and ⟨hp, hq⟩, hp⟩
    | inr hq =>
      left; exact ⟨hq, fun hp => h_not_and ⟨hp, hq⟩⟩
  · intro h
    cases h with
    | inl ⟨hp, hnq⟩ => exact ⟨Or.inl hp, fun ⟨_, hq⟩ => hnq hq⟩
    | inr ⟨hnp, hq⟩ => exact ⟨Or.inr hq, fun ⟨hp, _⟩ => hnp hp⟩
```

### Sheffer Stroke (NAND)

The Sheffer stroke shows that all logical operations can be expressed using just one:

```lean
-- NAND (NOT AND)
def nand (P Q : Prop) : Prop := ¬(P ∧ Q)

-- All operations in terms of NAND
def not_via_nand (P : Prop) : ¬P ↔ nand P P := by simp [nand]

def and_via_nand (P Q : Prop) : P ∧ Q ↔ ¬(nand P Q) := by
  simp [nand]; rfl

def or_via_nand (P Q : Prop) : P ∨ Q ↔ nand (nand P P) (nand Q Q) := by
  simp [nand]
  constructor
  · intro h
    cases h <;> simp [*]
  · intro h
    by_contra h_not
    push_neg at h_not
    exact h ⟨h_not.1, h_not.2⟩
```

## Quantifiers

### Universal Quantification

Universal quantification (`∀`) is built into type theory as dependent function types:

```lean
-- ∀ x : α, P x  is the same as  (x : α) → P x
def universal_example (α : Type) (P : α → Prop) :
  (∀ x : α, P x) ↔ ((x : α) → P x) := Iff.rfl

-- Instantiation: from ∀ to specific instance
def universal_instantiation (α : Type) (P : α → Prop) (a : α) :
  (∀ x : α, P x) → P a := fun h => h a

-- Generalization: from instances to universal (when x is arbitrary)
def universal_generalization (α : Type) (P : α → Prop) :
  ((x : α) → P x) → (∀ x : α, P x) := fun h => h
```

### Existential Quantification

Existential quantification (`∃`) provides a witness along with a proof:

```lean
-- Existential as Sigma type
#print Exists
-- inductive Exists {α : Sort u} (p : α → Prop) : Prop where
-- | intro : ∀ (w : α), p w → Exists p

-- Constructing existentials
def exists_example (α : Type) (P : α → Prop) (a : α) (ha : P a) :
  ∃ x : α, P x := Exists.intro a ha

-- Anonymous constructor
def exists_example' (α : Type) (P : α → Prop) (a : α) (ha : P a) :
  ∃ x : α, P x := ⟨a, ha⟩

-- Eliminating existentials
def exists_elimination (α : Type) (P : α → Prop) (Q : Prop) :
  (∃ x : α, P x) → (∀ x : α, P x → Q) → Q :=
  fun ⟨a, ha⟩ h => h a ha

-- Concrete example
example : ∃ n : Nat, n > 5 ∧ n < 10 := ⟨7, by simp, by simp⟩
```

### Unique Existence

Sometimes we want to assert that exactly one object satisfies a property:

```lean
-- Unique existence: there exists exactly one
def ExistsUnique (α : Type) (P : α → Prop) : Prop :=
  ∃ x : α, P x ∧ ∀ y : α, P y → y = x

-- Notation for unique existence
notation "∃! " binder ", " r:(scoped P => ExistsUnique _ P) => r

-- Example: there is a unique additive identity for natural numbers
example : ∃! n : Nat, ∀ m : Nat, n + m = m ∧ m + n = m := by
  use 0
  constructor
  · intro m; simp
  · intro n h
    have := h 1
    simp at this
    exact this.2.symm
```

## Classical Extensions

In constructive logic, some classical principles don't hold. When needed, we can import them:

```lean
-- These require Classical logic
open Classical

-- Law of Excluded Middle
#check em  -- ∀ (p : Prop), p ∨ ¬p

-- Double Negation Elimination
#check not_not  -- ∀ {p : Prop}, ¬¬p → p

-- These give us classical reasoning power
theorem pierce_law (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_cases hp : P
  · exact hp
  · exact h (fun _ => False.elim (hp (h (fun _ => False.elim (hp _)))))

-- But they break computational content
-- We can prove things exist without constructing them
theorem classical_existence : ∃ x : Nat, x = 0 ∨ x ≠ 0 := by
  cases em (∃ x : Nat, x = 0) with
  | inl h => exact h.elim (fun w hw => ⟨w, Or.inl hw⟩)
  | inr h => use 1; right; simp
```

This foundation of logical connectives and quantifiers provides the building blocks for all mathematical reasoning in Lean. The interplay between propositional and boolean logic offers both rigorous proof capabilities and efficient computation.

---

[Equality](./Logic.equality.html)
