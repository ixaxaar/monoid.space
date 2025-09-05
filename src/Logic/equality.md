---

[Contents](contents.html)
[Previous](Logic.logicBasics.html)
[Next](Logic.laws.html)

# Equality in Logic

---

- [Logical vs Propositional Equality](#logical-vs-propositional-equality)
- [Boolean Equality](#boolean-equality)
- [Equivalence Relations](#equivalence-relations)
  - [Properties of Relations](#properties-of-relations)
  - [Equivalence Relation Structure](#equivalence-relation-structure)
- [Logical Equivalence](#logical-equivalence)
- [Decidable Equality](#decidable-equality)
- [Equality in Different Contexts](#equality-in-different-contexts)
  - [Equality of Propositions](#equality-of-propositions)
  - [Equality of Truth Values](#equality-of-truth-values)
  - [Functional Extensionality](#functional-extensionality)

```lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Relation.Basic
import Mathlib.Tactic.Basic
```

While we explored equality comprehensively in the Types chapter, equality takes on special significance in logic. Here we examine equality from the logical perspective: how equality relates to logical operations, how we can compute with equality, and how equality structures arise in different logical contexts.

## Logical vs Propositional Equality

In logic, we encounter different notions of equality depending on whether we're working with truth values, propositions, or logical operations:

```lean
-- Propositional equality: two propositions are the same proposition
example : (True ∧ False) = False := rfl

-- Logical equivalence: two propositions have the same truth value
example : (True ∧ False) ↔ False := ⟨And.right, False.elim⟩

-- Boolean equality: two boolean values are the same
example : (true && false) = false := rfl

-- These are related but distinct concepts
example (P Q : Prop) : (P = Q) → (P ↔ Q) := fun h => by rw [h]
-- But the converse is not always true without additional axioms
```

## Boolean Equality

In computational logic, equality can be defined in terms of other logical operations:

```lean
-- Boolean equality using XOR
def bool_eq (a b : Bool) : Bool := !(a ^^ b)

-- Verify this matches built-in equality
example (a b : Bool) : bool_eq a b = (a == b) := by
  cases a <;> cases b <;> rfl

-- Boolean equality truth table
example : bool_eq true true = true := rfl
example : bool_eq true false = false := rfl
example : bool_eq false true = false := rfl
example : bool_eq false false = true := rfl

-- Relationship to XOR: equality is negation of XOR
theorem bool_eq_not_xor (a b : Bool) : bool_eq a b = !(a ^^ b) := rfl

-- Alternative definition using other operations
def bool_eq_alt (a b : Bool) : Bool := (a && b) || ((!a) && (!b))

theorem bool_eq_equiv (a b : Bool) : bool_eq a b = bool_eq_alt a b := by
  cases a <;> cases b <;> rfl
```

## Equivalence Relations

Equality is the prototypical equivalence relation. Let's formalize the general structure:

### Properties of Relations

```lean
-- General relation type
def Relation (α : Type*) := α → α → Prop

-- Reflexivity: every element is related to itself
def Reflexive {α : Type*} (r : Relation α) : Prop := ∀ a, r a a

-- Symmetry: if a relates to b, then b relates to a
def Symmetric {α : Type*} (r : Relation α) : Prop := ∀ a b, r a b → r b a

-- Transitivity: if a relates to b and b relates to c, then a relates to c
def Transitive {α : Type*} (r : Relation α) : Prop := ∀ a b c, r a b → r b c → r a c

-- Examples with equality
example : Reflexive (@Eq Nat) := fun a => rfl
example : Symmetric (@Eq Nat) := fun a b h => h.symm
example : Transitive (@Eq Nat) := fun a b c h₁ h₂ => h₁.trans h₂
```

### Equivalence Relation Structure

```lean
-- An equivalence relation combines all three properties
structure EquivalenceRel (α : Type*) where
  rel : Relation α
  refl : Reflexive rel
  symm : Symmetric rel
  trans : Transitive rel

-- Equality is the canonical equivalence relation
def equality_equiv_rel (α : Type*) : EquivalenceRel α := {
  rel := Eq,
  refl := fun a => rfl,
  symm := fun a b h => h.symm,
  trans := fun a b c h₁ h₂ => h₁.trans h₂
}

-- Boolean equality is also an equivalence relation
def bool_equality_equiv : EquivalenceRel Bool := {
  rel := fun a b => a = b,
  refl := fun a => rfl,
  symm := fun a b h => h.symm,
  trans := fun a b c h₁ h₂ => h₁.trans h₂
}

-- Logical equivalence for propositions
def prop_equiv_rel : EquivalenceRel Prop := {
  rel := fun P Q => P ↔ Q,
  refl := fun P => Iff.rfl,
  symm := fun P Q h => h.symm,
  trans := fun P Q R h₁ h₂ => h₁.trans h₂
}
```

## Logical Equivalence

Logical equivalence (`↔`) is a fundamental concept distinct from equality:

```lean
-- Two propositions are logically equivalent if they have the same truth value
def LogicallyEquivalent (P Q : Prop) : Prop := P ↔ Q

-- Examples of logical equivalence
theorem double_negation_equiv (P : Prop) : LogicallyEquivalent (¬¬P) P := by
  constructor
  · exact Classical.not_not
  · intro h hnp; exact hnp h

theorem demorgan_equiv (P Q : Prop) :
  LogicallyEquivalent (¬(P ∧ Q)) (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hp : P
    · by_cases hq : Q
      · exfalso; exact h ⟨hp, hq⟩
      · exact Or.inr hq
    · exact Or.inl hp
  · intro h ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq

-- Logical equivalence respects logical operations
theorem and_equiv_compat (P₁ P₂ Q₁ Q₂ : Prop) :
  LogicallyEquivalent P₁ P₂ → LogicallyEquivalent Q₁ Q₂ →
  LogicallyEquivalent (P₁ ∧ Q₁) (P₂ ∧ Q₂) := by
  intro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  constructor
  · intro ⟨hp₁, hq₁⟩; exact ⟨h₁ hp₁, h₃ hq₁⟩
  · intro ⟨hp₂, hq₂⟩; exact ⟨h₂ hp₂, h₄ hq₂⟩
```

## Decidable Equality

Some types have decidable equality—we can compute whether two elements are equal:

```lean
-- Natural numbers have decidable equality
example (n m : Nat) : Decidable (n = m) := Nat.decidableEq n m

#eval decide (5 = 5)  -- true
#eval decide (5 = 7)  -- false

-- Booleans have decidable equality
example (b c : Bool) : Decidable (b = c) := Bool.decidableEq b c

#eval decide (true = true)   -- true
#eval decide (true = false)  -- false

-- We can implement decidable equality for custom types
inductive Color where | red | green | blue

instance : DecidableEq Color := fun
  | Color.red, Color.red => Decidable.isTrue rfl
  | Color.green, Color.green => Decidable.isTrue rfl
  | Color.blue, Color.blue => Decidable.isTrue rfl
  | Color.red, Color.green => Decidable.isFalse (by simp)
  | Color.red, Color.blue => Decidable.isFalse (by simp)
  | Color.green, Color.red => Decidable.isFalse (by simp)
  | Color.green, Color.blue => Decidable.isFalse (by simp)
  | Color.blue, Color.red => Decidable.isFalse (by simp)
  | Color.blue, Color.green => Decidable.isFalse (by simp)

#eval decide (Color.red = Color.red)    -- true
#eval decide (Color.red = Color.blue)   -- false
```

## Equality in Different Contexts

### Equality of Propositions

```lean
-- Propositional equality is very strict
example : (True ∧ True) = True := rfl
example : (True ∨ False) = True := rfl

-- But many logically equivalent propositions are not equal
example : (True ∧ True) ≠ True := by
  -- This is actually false! They are propositionally equal
  sorry

-- Let's check what actually happens
example : (True ∧ True) = True := rfl  -- This works!

-- More interesting examples
example (P : Prop) : (P ∧ True) = P := by
  -- This requires propositional extensionality in general
  sorry
```

### Equality of Truth Values

```lean
-- For decidable propositions, we can compare their truth values
def same_truth_value (P Q : Prop) [Decidable P] [Decidable Q] : Bool :=
  decide P == decide Q

example : same_truth_value (3 = 3) (5 < 10) = true := rfl
example : same_truth_value (3 = 4) (5 < 10) = false := rfl

-- This gives us a computational way to check logical equivalence
-- for decidable propositions
theorem same_truth_iff_equiv (P Q : Prop) [Decidable P] [Decidable Q] :
  same_truth_value P Q = true ↔ (P ↔ Q) := by
  sorry  -- Requires more machinery
```

### Functional Extensionality

For functions, equality means they return equal results on all inputs:

```lean
-- Two boolean functions are equal if they agree on all inputs
theorem bool_fun_ext (f g : Bool → Bool) :
  (∀ b, f b = g b) → f = g := by
  intro h
  funext b
  exact h b

-- Example: these boolean functions are equal
def f₁ (b : Bool) : Bool := b && true
def f₂ (b : Bool) : Bool := b

theorem f₁_eq_f₂ : f₁ = f₂ := by
  funext b
  cases b <;> rfl

-- For logical functions (predicates)
theorem pred_ext (P Q : Bool → Prop) :
  (∀ b, P b ↔ Q b) → P = Q := by
  intro h
  funext b
  exact propext (h b)
```

This exploration of equality in logic shows how the abstract concept of equality manifests in different ways:

- **Computational equality**: Decidable and computable
- **Logical equivalence**: Same truth conditions
- **Propositional equality**: Definitional sameness
- **Functional equality**: Extensional equivalence

These different notions of equality are all useful in different contexts, and understanding their relationships is crucial for effective logical reasoning in type theory.

---

[Laws of Boolean Algebra](./Logic.laws.html)
