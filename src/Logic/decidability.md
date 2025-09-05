---

[Contents](contents.html)
[Previous](Logic.laws.html)
[Next](Logic.system_f.html)

# Decidability

---

- [The Decision Problem](#the-decision-problem)
- [Decidable Propositions](#decidable-propositions)
  - [The Decidable Type Class](#the-decidable-type-class)
  - [Examples of Decidable Propositions](#examples-of-decidable-propositions)
- [Evidence vs Computation](#evidence-vs-computation)
  - [Proof-Relevant Decision](#proof-relevant-decision)
  - [Computational Decision](#computational-decision)
  - [Bridging the Gap](#bridging-the-gap)
- [Decidability Instances](#decidability-instances)
  - [Natural Number Equality](#natural-number-equality)
  - [Natural Number Ordering](#natural-number-ordering)
  - [Boolean Decidability](#boolean-decidability)
- [Decidable Relations](#decidable-relations)
- [Classical vs Constructive Decidability](#classical-vs-constructive-decidability)
- [Undecidable Propositions](#undecidable-propositions)
  - [The Halting Problem](#the-halting-problem)
  - [Gödel's Incompleteness](#gödels-incompleteness)
- [Practical Applications](#practical-applications)
  - [Automation in Lean](#automation-in-lean)
  - [Proof by Computation](#proof-by-computation)
- [Reflective Programming](#reflective-programming)

```lean
import Mathlib.Logic.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Decidable.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Decide
```

One of the most fundamental questions in logic and computer science is: "Given a proposition, can we effectively determine whether it is true or false?" This is the **decision problem**. In constructive type theory, this question takes on special significance because it connects logical reasoning with computation. Decidability bridges the gap between **proof** and **algorithm**, between **evidence** and **computation**.

## The Decision Problem

A proposition is **decidable** if there exists an effective procedure (algorithm) that, given the proposition, can determine whether it is true or false in finite time. This concept is central to:

- **Automated theorem proving**: Can the computer decide this theorem?
- **Program verification**: Can we automatically check this property?
- **Computational logic**: Can we compute with logical statements?

In classical logic, every proposition is either true or false (law of excluded middle), but this doesn't tell us whether we can **compute** which one it is. In constructive type theory, decidability is about the **existence of algorithms**.

```lean
-- Classical view: every proposition has a truth value (non-constructive)
open Classical
example (P : Prop) : P ∨ ¬P := em P

-- Constructive view: we need an algorithm to decide
example (b : Bool) : b = true ∨ b = false := by cases b <;> simp
```

## Decidable Propositions

### The Decidable Type Class

In Lean, decidability is captured by the `Decidable` type class:

```lean
-- The core definition (simplified)
#print Decidable
-- inductive Decidable (p : Prop) : Type where
-- | isFalse : (¬p) → Decidable p
-- | isTrue  : p → Decidable p

-- This provides either a proof or a refutation
def decide_example (P : Prop) [Decidable P] : Bool :=
  match ‹Decidable P› with
  | Decidable.isTrue _  => true
  | Decidable.isFalse _ => false

-- More commonly used built-in function
#check decide -- {p : Prop} → [Decidable p] → Bool
```

The `Decidable` type provides either:

- A **proof** that the proposition is true (`isTrue`)
- A **proof** that the proposition is false (`isFalse`)

This is constructive: we don't just know that P ∨ ¬P, we have an algorithm that produces a proof of whichever is the case.

### Examples of Decidable Propositions

```lean
-- Natural number equality is decidable
#check Nat.decidableEq -- DecidableEq Nat
example : Decidable (3 = 3) := Decidable.isTrue rfl
example : Decidable (3 = 4) := Decidable.isFalse (by simp)

-- We can decide by computation
#eval decide (3 = 3) -- true
#eval decide (3 = 4) -- false

-- Natural number ordering is decidable
example : Decidable (5 ≤ 10) := Decidable.isTrue (by simp)
example : Decidable (10 ≤ 5) := Decidable.isFalse (by simp)

#eval decide (5 ≤ 10) -- true
#eval decide (10 ≤ 5) -- false

-- Complex decidable propositions can be built from simpler ones
example : Decidable ((3 = 3) ∧ (5 ≤ 10)) := by infer_instance
#eval decide ((3 = 3) ∧ (5 ≤ 10)) -- true
```

## Evidence vs Computation

Decidability beautifully demonstrates the connection between two views of the same logical statement:

### Proof-Relevant Decision

We can provide explicit evidence for our decisions:

```lean
-- Proof-relevant: we get the actual proof or refutation
def nat_eq_decision (n m : Nat) : Decidable (n = m) :=
  if h : n = m then
    Decidable.isTrue h
  else
    Decidable.isFalse h

-- Extract the proof from a positive decision
def extract_proof (n m : Nat) (h : decide (n = m) = true) : n = m := by
  -- The `decide` function can provide constructive evidence
  exact of_decide_eq_true h

-- Example usage
example : 7 = 7 := extract_proof 7 7 rfl
```

### Computational Decision

We can also work purely computationally:

```lean
-- Convert decidable proposition to boolean
def prop_to_bool (P : Prop) [Decidable P] : Bool := decide P

-- Boolean function for natural number equality
def nat_eq_bool (n m : Nat) : Bool := decide (n = m)

-- Boolean function for natural number less-than-or-equal
def nat_le_bool (n m : Nat) : Bool := decide (n ≤ m)

#eval nat_eq_bool 5 5  -- true
#eval nat_le_bool 3 7  -- true
#eval nat_le_bool 7 3  -- false
```

### Bridging the Gap

The beauty of Lean's approach is that these views are connected:

```lean
-- From boolean to proposition
theorem decide_true_iff (P : Prop) [Decidable P] : decide P = true ↔ P :=
  ⟨of_decide_eq_true, of_decide_eq_false⟩

-- From proposition to boolean
theorem bool_of_decidable (P : Prop) [Decidable P] :
  (P → decide P = true) ∧ (¬P → decide P = false) :=
  ⟨of_decide_eq_false, of_decide_eq_false⟩

-- Example: prove arithmetical statements by computation
example : 15 * 23 = 345 := by decide
example : 100 < 200 := by decide
example : ¬(17 = 18) := by decide
```

## Decidability Instances

### Natural Number Equality

```lean
-- Lean provides decidability for natural number equality
instance : DecidableEq Nat := Nat.decidableEq

-- We can implement our own version
def nat_eq_decidable (n m : Nat) : Decidable (n = m) :=
  match n, m with
  | 0, 0 => Decidable.isTrue rfl
  | 0, Nat.succ _ => Decidable.isFalse (by simp)
  | Nat.succ _, 0 => Decidable.isFalse (by simp)
  | Nat.succ n', Nat.succ m' =>
    match nat_eq_decidable n' m' with
    | Decidable.isTrue h => Decidable.isTrue (congrArg Nat.succ h)
    | Decidable.isFalse h => Decidable.isFalse (fun h' => h (Nat.succ.inj h'))
```

### Natural Number Ordering

```lean
-- Decidable less-than-or-equal for natural numbers
def nat_le_decidable (n m : Nat) : Decidable (n ≤ m) :=
  match n, m with
  | 0, _ => Decidable.isTrue (Nat.zero_le _)
  | Nat.succ _, 0 => Decidable.isFalse (Nat.not_succ_le_zero _)
  | Nat.succ n', Nat.succ m' =>
    match nat_le_decidable n' m' with
    | Decidable.isTrue h => Decidable.isTrue (Nat.succ_le_succ h)
    | Decidable.isFalse h => Decidable.isFalse (fun h' => h (Nat.le_of_succ_le_succ h'))

-- This gives us computational power
example : Decidable (100 ≤ 200) := nat_le_decidable 100 200
example : Decidable (200 ≤ 100) := nat_le_decidable 200 100
```

### Boolean Decidability

```lean
-- Every boolean equation is decidable
instance (b c : Bool) : Decidable (b = c) := Bool.decidableEq b c

-- Boolean predicates are decidable
def is_true_decidable (b : Bool) : Decidable (b = true) :=
  if h : b = true then
    Decidable.isTrue h
  else
    Decidable.isFalse h

-- Complex boolean expressions
def complex_bool_prop (a b c : Bool) : Prop :=
  (a ∧ b) ∨ (¬a ∧ c) = true

instance (a b c : Bool) : Decidable (complex_bool_prop a b c) := by
  unfold complex_bool_prop
  infer_instance

#eval decide (complex_bool_prop true false true)  -- true
```

## Decidable Relations

For binary relations, we can define decidability in terms of all pairs:

```lean
-- A relation is decidable if we can decide it for any pair
class DecidableRel {α β : Type*} (r : α → β → Prop) where
  decidable_rel : ∀ a b, Decidable (r a b)

-- Natural number equality as a decidable relation
instance : DecidableRel (@Eq Nat) where
  decidable_rel := fun a b => Nat.decidableEq a b

-- Less-than-or-equal as a decidable relation
instance : DecidableRel (· ≤ · : Nat → Nat → Prop) where
  decidable_rel := Nat.decidableLe

-- Using decidable relations
def find_first_ge (n : Nat) (threshold : Nat) : Option Nat :=
  if decide (n ≥ threshold) then some n
  else if n < 100 then find_first_ge (n + 1) threshold
  else none

#eval find_first_ge 0 50  -- some 50
```

## Classical vs Constructive Decidability

There's an important distinction between classical and constructive decidability:

```lean
-- Classical decidability: we know P ∨ ¬P but can't compute which
open Classical

def classical_decidable (P : Prop) : Decidable P :=
  if h : P then Decidable.isTrue h
  else Decidable.isFalse h

-- This relies on classical logic and doesn't give us an algorithm

-- Constructive decidability: we have an actual algorithm
def constructive_nat_even (n : Nat) : Decidable (Even n) :=
  if h : n % 2 = 0 then
    Decidable.isTrue ⟨n / 2, by rw [Nat.two_mul_div_two_of_even]; exact Nat.dvd_iff_mod_eq_zero.mp ⟨2, h⟩⟩
  else
    Decidable.isFalse (fun ⟨k, hk⟩ => h (by rw [hk, Nat.mul_mod, Nat.mod_self]; simp))

-- This actually computes the result
#eval decide (Even 10)  -- true
#eval decide (Even 11)  -- false
```

## Undecidable Propositions

Not all propositions are decidable. Some famous examples:

### The Halting Problem

```lean
-- We cannot decide if an arbitrary function terminates
-- This is a metamathematical statement, not expressible directly in Lean's logic
-- But we can give the intuition:

-- Hypothetical: if we could decide termination
axiom terminates : (Nat → Nat) → Prop
axiom termination_decidable : ∀ f, Decidable (terminates f)

-- Then we could construct a paradox (diagonalization argument)
-- This shows such a decision procedure cannot exist
```

### Gödel's Incompleteness

```lean
-- Some arithmetic statements are undecidable in any consistent formal system
-- For example, the consistency of the system itself

-- We cannot prove within Lean that Lean is consistent
-- (If we could, this would violate Gödel's second incompleteness theorem)

-- However, we can work with statements that are relatively decidable
def goldbach_conjecture (n : Nat) : Prop :=
  n > 2 ∧ Even n → ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

-- We can decide this for any particular n, but the universal statement
-- ∀ n, goldbach_conjecture n is not known to be decidable
```

## Practical Applications

### Automation in Lean

Decidability enables powerful automation:

```lean
-- The `decide` tactic can prove decidable goals automatically
example : 1000 + 2000 = 3000 := by decide
example : 50 < 100 ∧ 100 < 200 := by decide
example : ¬(List.length [1, 2, 3] = 5) := by decide

-- Complex arithmetic
example : (15 * 23 + 7) * 2 = 704 := by decide

-- Boolean reasoning
example : ∀ a b : Bool, a ∧ (a ∨ b) = a := by decide
```

### Proof by Computation

We can prove properties by computing:

```lean
-- Define a computational check
def is_sorted (l : List Nat) : Bool :=
  match l with
  | [] | [_] => true
  | a :: b :: rest => a ≤ b && is_sorted (b :: rest)

-- Prove specific instances by computation
example : is_sorted [1, 2, 3, 5, 8] = true := by decide

-- Connect computational and logical views
theorem is_sorted_correct (l : List Nat) :
  is_sorted l = true ↔ List.Sorted (· ≤ ·) l := by
  -- Proof would require induction and lemmas about List.Sorted
  sorry

-- Now we can prove sortedness by computation
example : List.Sorted (· ≤ ·) [1, 3, 5, 7, 9] := by
  rw [← is_sorted_correct]
  decide
```

## Reflective Programming

Decidability enables **reflection**—treating code as data:

```lean
-- We can represent propositions as data and decide them
inductive SimpleProp : Type where
  | true : SimpleProp
  | false : SimpleProp
  | and : SimpleProp → SimpleProp → SimpleProp
  | or : SimpleProp → SimpleProp → SimpleProp
  | not : SimpleProp → SimpleProp

-- Interpret simple propositions
def eval_simple_prop : SimpleProp → Bool
  | SimpleProp.true => true
  | SimpleProp.false => false
  | SimpleProp.and p q => eval_simple_prop p && eval_simple_prop q
  | SimpleProp.or p q => eval_simple_prop p || eval_simple_prop q
  | SimpleProp.not p => not (eval_simple_prop p)

-- Decision procedure for simple propositions
def decide_simple_prop : SimpleProp → Bool := eval_simple_prop

-- Example: decide complex formulas by computation
def example_formula : SimpleProp :=
  SimpleProp.or
    (SimpleProp.and SimpleProp.true SimpleProp.false)
    (SimpleProp.not SimpleProp.false)

#eval decide_simple_prop example_formula  -- true
```

Decidability represents one of type theory's great achievements: the unification of **logic** and **computation**. It shows that mathematical truth and algorithmic computation are intimately connected. In Lean, this connection is not just philosophical but practical—we can prove theorems by running programs, and our proofs **are** programs.

This computational view of logic opens doors to:

- **Verified computation**: Programs whose correctness is guaranteed by types
- **Automated reasoning**: Letting computers handle routine proofs
- **Reflective programming**: Programs that reason about themselves
- **Constructive mathematics**: Mathematics with computational content

The boundary between decidable and undecidable propositions continues to be an active area of research, with profound implications for both mathematics and computer science.

---

[System F](./Logic.system_f.html)
