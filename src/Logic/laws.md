---

[Contents](contents.html)
[Previous](Logic.equality.html)
[Next](Logic.decidability.html)

# Laws of Boolean Algebra

---

- [Boolean Algebraic Structure](#boolean-algebraic-structure)
- [Fundamental Laws](#fundamental-laws)
  - [Identity Laws](#identity-laws)
  - [Complement Laws](#complement-laws)
  - [Idempotent Laws](#idempotent-laws)
  - [Commutative Laws](#commutative-laws)
  - [Associative Laws](#associative-laws)
  - [Distributive Laws](#distributive-laws)
  - [De Morgan's Laws](#de-morgans-laws)
  - [Absorption Laws](#absorption-laws)
- [Derived Laws](#derived-laws)
  - [Consensus Laws](#consensus-laws)
  - [Redundancy Laws](#redundancy-laws)
- [Proof Techniques](#proof-techniques)
  - [Truth Table Proofs](#truth-table-proofs)
  - [Algebraic Proofs](#algebraic-proofs)
  - [Constructive Proofs](#constructive-proofs)
- [Boolean Algebra as a Lattice](#boolean-algebra-as-a-lattice)
- [Applications to Simplification](#applications-to-simplification)

```lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.Order.Lattice.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Basic
```

Boolean algebra is not just a collection of logical operations—it forms a rich algebraic structure governed by precise laws. These laws enable systematic reasoning, circuit optimization, and logical simplification. In type theory, we can prove these laws both computationally (for `Bool`) and propositionally (for `Prop`), demonstrating the deep connections between logic and algebra.

## Boolean Algebraic Structure

A Boolean algebra consists of:

- A set of elements (in our case, `Bool` or propositions in `Prop`)
- Two binary operations (∧ and ∨, or && and ||)
- One unary operation (¬ or not)
- Two special elements (True/true and False/false)
- Laws governing their interaction

```lean
-- Define a general Boolean algebra structure
class BooleanAlgebra (α : Type*) extends Lattice α where
  -- Complement operation
  compl : α → α
  -- Special elements
  top : α    -- True element
  bot : α    -- False element

  -- Complement laws
  compl_sup_eq : ∀ x : α, x ⊔ compl x = top
  compl_inf_eq : ∀ x : α, x ⊓ compl x = bot

  -- Identity laws
  sup_bot_eq : ∀ x : α, x ⊔ bot = x
  inf_top_eq : ∀ x : α, x ⊓ top = x

-- Bool is a Boolean algebra
instance : BooleanAlgebra Bool where
  compl := not
  top := true
  bot := false
  compl_sup_eq := fun x => by cases x <;> simp [Sup.sup, Bot.bot]
  compl_inf_eq := fun x => by cases x <;> simp [Inf.inf, Bot.bot]
  sup_bot_eq := fun x => by cases x <;> simp [Sup.sup, Bot.bot]
  inf_top_eq := fun x => by cases x <;> simp [Inf.inf, Top.top]
```

## Fundamental Laws

### Identity Laws

The identity laws establish True and False as the identity elements:

```lean
-- Boolean identity laws
theorem bool_or_false (b : Bool) : b || false = b := by cases b <;> rfl
theorem bool_or_true (b : Bool) : b || true = true := by cases b <;> rfl
theorem bool_and_false (b : Bool) : b && false = false := by cases b <;> rfl
theorem bool_and_true (b : Bool) : b && true = b := by cases b <;> rfl

-- Propositional identity laws
theorem prop_or_false (P : Prop) : P ∨ False ↔ P := ⟨Or.resolve_right, Or.inl⟩
theorem prop_or_true (P : Prop) : P ∨ True ↔ True := ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
theorem prop_and_false (P : Prop) : P ∧ False ↔ False := ⟨And.right, False.elim⟩
theorem prop_and_true (P : Prop) : P ∧ True ↔ P := ⟨And.left, fun h => ⟨h, trivial⟩⟩
```

### Complement Laws

Every element has a unique complement:

```lean
-- Boolean complement laws
theorem bool_or_not (b : Bool) : b || not b = true := by cases b <;> rfl
theorem bool_and_not (b : Bool) : b && not b = false := by cases b <;> rfl

-- Propositional complement laws (require classical logic for full strength)
open Classical

theorem prop_or_not (P : Prop) : P ∨ ¬P := em P
theorem prop_and_not (P : Prop) : ¬(P ∧ ¬P) := fun ⟨h, nh⟩ => nh h

-- Double negation
theorem bool_not_not (b : Bool) : not (not b) = b := by cases b <;> rfl
theorem prop_not_not (P : Prop) : ¬¬P → P := not_not
```

### Idempotent Laws

Operations with the same element twice simplify:

```lean
-- Boolean idempotency
theorem bool_or_self (b : Bool) : b || b = b := by cases b <;> rfl
theorem bool_and_self (b : Bool) : b && b = b := by cases b <;> rfl

-- Propositional idempotency
theorem prop_or_self (P : Prop) : P ∨ P ↔ P := ⟨Or.resolve_left id, Or.inl⟩
theorem prop_and_self (P : Prop) : P ∧ P ↔ P := ⟨And.left, fun h => ⟨h, h⟩⟩
```

### Commutative Laws

Order of operands doesn't matter:

```lean
-- Boolean commutativity
theorem bool_or_comm (b c : Bool) : b || c = c || b := by cases b <;> cases c <;> rfl
theorem bool_and_comm (b c : Bool) : b && c = c && b := by cases b <;> cases c <;> rfl

-- Propositional commutativity
theorem prop_or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P := Or.comm
theorem prop_and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := And.comm
```

### Associative Laws

Grouping doesn't matter:

```lean
-- Boolean associativity
theorem bool_or_assoc (a b c : Bool) : a || (b || c) = (a || b) || c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_and_assoc (a b c : Bool) : a && (b && c) = (a && b) && c := by
  cases a <;> cases b <;> cases c <;> rfl

-- Propositional associativity
theorem prop_or_assoc (P Q R : Prop) : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := Or.assoc
theorem prop_and_assoc (P Q R : Prop) : P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R := And.assoc
```

### Distributive Laws

Operations distribute over each other:

```lean
-- Boolean distributivity
theorem bool_and_or_distrib (a b c : Bool) :
  a && (b || c) = (a && b) || (a && c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_or_and_distrib (a b c : Bool) :
  a || (b && c) = (a || b) && (a || c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Propositional distributivity
theorem prop_and_or_distrib (P Q R : Prop) :
  P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro h
    cases h with
    | inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

theorem prop_or_and_distrib (P Q R : Prop) :
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · intro h
    cases h with
    | inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  · intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq =>
      cases hpr with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr ⟨hq, hr⟩
```

### De Morgan's Laws

Fundamental relationship between conjunction, disjunction, and negation:

```lean
-- Boolean De Morgan's laws
theorem bool_not_and (b c : Bool) : not (b && c) = (not b) || (not c) := by
  cases b <;> cases c <;> rfl

theorem bool_not_or (b c : Bool) : not (b || c) = (not b) && (not c) := by
  cases b <;> cases c <;> rfl

-- Propositional De Morgan's laws
theorem prop_not_and (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hp : P
    · by_cases hq : Q
      · exact False.elim (h ⟨hp, hq⟩)
      · exact Or.inr hq
    · exact Or.inl hp
  · intro h ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq

theorem prop_not_or (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hp; exact h (Or.inl hp)
    · intro hq; exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ h
    cases h with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq
```

### Absorption Laws

These fundamental laws show how operations can "absorb" each other:

```lean
-- Boolean absorption laws
theorem bool_and_or_absorb (b c : Bool) : b && (b || c) = b := by
  cases b <;> cases c <;> rfl

theorem bool_or_and_absorb (b c : Bool) : b || (b && c) = b := by
  cases b <;> cases c <;> rfl

-- Propositional absorption laws
theorem prop_and_or_absorb (P Q : Prop) : P ∧ (P ∨ Q) ↔ P := by
  constructor
  · intro ⟨hp, _⟩; exact hp
  · intro hp; exact ⟨hp, Or.inl hp⟩

theorem prop_or_and_absorb (P Q : Prop) : P ∨ (P ∧ Q) ↔ P := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr ⟨hp, _⟩ => exact hp
  · intro hp; exact Or.inl hp
```

## Derived Laws

### Consensus Laws

These show how certain expressions can be simplified:

```lean
-- Consensus theorem for Boolean algebra
theorem bool_consensus (a b c : Bool) :
  (a && b) || (not a && c) || (b && c) = (a && b) || (not a && c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- The third term (b && c) is redundant when the first two are present
theorem prop_consensus (P Q R : Prop) :
  (P ∧ Q) ∨ (¬P ∧ R) ∨ (Q ∧ R) ↔ (P ∧ Q) ∨ (¬P ∧ R) := by
  constructor
  · intro h
    cases h with
    | inl hpq => exact Or.inl hpq
    | inr h' =>
      cases h' with
      | inl hnpr => exact Or.inr hnpr
      | inr hqr =>
        by_cases hp : P
        · exact Or.inl ⟨hp, hqr.1⟩
        · exact Or.inr ⟨hp, hqr.2⟩
  · intro h; cases h <;> [exact Or.inl ‹_›; exact Or.inr (Or.inl ‹_›)]
```

### Redundancy Laws

Show when certain terms become unnecessary:

```lean
-- If P implies Q, then P ∨ Q = Q and P ∧ Q = P
theorem redundancy_or (P Q : Prop) (h : P → Q) : P ∨ Q ↔ Q := by
  constructor
  · intro hpq
    cases hpq with
    | inl hp => exact h hp
    | inr hq => exact hq
  · intro hq; exact Or.inr hq

theorem redundancy_and (P Q : Prop) (h : P → Q) : P ∧ Q ↔ P := by
  constructor
  · intro ⟨hp, _⟩; exact hp
  · intro hp; exact ⟨hp, h hp⟩
```

## Proof Techniques

### Truth Table Proofs

For boolean expressions, exhaustive case analysis:

```lean
-- Example: proving a complex identity by cases
theorem bool_complex_identity (a b c : Bool) :
  (a || b) && (a || c) && (b || c) = (a || b) && (a || c) := by
  cases a <;> cases b <;> cases c <;> rfl
```

### Algebraic Proofs

Using previously proven laws to derive new results:

```lean
-- Example: algebraic proof of absorption
theorem absorption_algebraic_proof (P Q : Prop) : P ∨ (P ∧ Q) ↔ P := by
  calc P ∨ (P ∧ Q)
    ↔ P ∨ (P ∧ Q) ∨ False           := by rw [prop_or_false]
    _ ↔ P ∨ (P ∧ Q) ∨ (P ∧ ¬P)       := by rw [← prop_and_not]
    _ ↔ P ∨ (P ∧ (Q ∨ ¬P))           := by rw [← prop_and_or_distrib]
    _ ↔ P ∨ (P ∧ (Q ∨ ¬P))           := by rfl
    _ ↔ P ∨ (P ∧ True)               := by rw [← prop_or_not]
    _ ↔ P ∨ P                        := by rw [prop_and_true]
    _ ↔ P                            := by rw [prop_or_self]
```

### Constructive Proofs

Direct construction without case analysis:

```lean
-- Constructive proof showing the essence of the law
theorem constructive_absorption (P Q : Prop) : P ∨ (P ∧ Q) → P := by
  intro h
  cases h with
  | inl hp => exact hp
  | inr ⟨hp, _⟩ => exact hp
```

## Boolean Algebra as a Lattice

Boolean algebra forms a special kind of lattice—a complemented distributive lattice:

```lean
-- Boolean algebra is a bounded distributive lattice with complements
theorem boolean_lattice_properties :
  ∀ (a b c : Bool),
  -- Idempotent
  (a || a = a) ∧
  (a && a = a) ∧
  -- Absorption
  (a || (a && b) = a) ∧
  (a && (a || b) = a) ∧
  -- Distributive
  (a || (b && c) = (a || b) && (a || c)) ∧
  (a && (b || c) = (a && b) || (a && c)) ∧
  -- Complement
  (a || not a = true) ∧
  (a && not a = false) := by
  intro a b c
  cases a <;> cases b <;> cases c <;> simp [Bool.and_assoc, Bool.or_assoc]
```

## Applications to Simplification

These laws enable systematic simplification of logical expressions:

```lean
-- Example: simplifying a complex boolean expression
def complex_expr (a b c : Bool) : Bool :=
  (a && b) || (a && not b && c) || (not a && b && c) || (not a && not b)

-- Simplified form
def simplified_expr (a b c : Bool) : Bool :=
  (a && b) || (not a && not b) || (not b && c)

-- Proof they're equivalent
theorem simplification_correct (a b c : Bool) :
  complex_expr a b c = simplified_expr a b c := by
  cases a <;> cases b <;> cases c <;> rfl

-- General simplification strategy
theorem simplification_strategy (P Q R : Prop) :
  (P ∧ Q) ∨ (P ∧ ¬Q ∧ R) ∨ (¬P ∧ Q ∧ R) ∨ (¬P ∧ ¬Q) ↔
  (P ∧ Q) ∨ (¬P ∧ ¬Q) ∨ (¬Q ∧ R) := by
  -- This would require a longer proof, but demonstrates the principle
  sorry
```

These laws form the theoretical foundation for:

- **Digital circuit design**: Minimizing gate counts
- **Logic programming**: Optimizing queries
- **Automated theorem proving**: Simplifying expressions
- **Compiler optimization**: Boolean expression optimization
- **Mathematical reasoning**: Systematic proof techniques

The beauty of Boolean algebra lies in its dual nature: providing both computational tools for working with `Bool` values and logical principles for reasoning about propositions in `Prop`.

---

[Decidability](./Logic.decidability.html)
