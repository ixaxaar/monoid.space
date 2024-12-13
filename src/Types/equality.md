****
[Contents](contents.html)
[Previous](Types.relations.html)
[Next](Types.operations.html)

# Equality

****

- [Equality](#equality)
  - [Definitional Equality](#definitional-equality)
  - [Computational Equality](#computational-equality)
  - [Propositional Equality](#propositional-equality)

```lean
import data.bool
import data.Nat.basic
import data.list.basic
import logic.relation
```

Equality is a fundamental concept in mathematics and logic, yet it can be more subtle than it first appears. In type theory, particularly in proof assistants like Lean, equality comes in different forms, each with its own nuances and uses. In type theory, equality can be broadly classified into three kinds:

- **Propositional equality**
- **Computational equality**
- **Definitional equality**

## Definitional Equality

Definitional equality is the most straightforward form of equality. It refers to expressions that are equal by virtue of their definitions or because they are syntactically identical after unfolding definitions. In Lean, two terms are definitionally equal if they reduce to the same expression via computation steps like beta reduction (function application) or delta reduction (unfolding definitions). In easier terms, if two terms are equal by definition, they are definitionally equal. For example:

```lean
def defEqual₁ : Nat :=
  7

def defEqual₂ : Nat :=
  Nat.succ (Nat.succ 5)
```

Here, `defEqual₁` and `defEqual₂` both are equal, with equality of the kind "definitional equality".

```lean
#eval defEqual₁  -- Output: 7
#eval defEqual₂  -- Output: 7
```

Another way to define definitional equality is by using the `rfl` tactic, which stands for "reflexivity":

```lean
def seven : Nat := 7
def also_seven : Nat := 3 + 4

-- These are definitionally equal
example : seven = also_seven := rfl
```

Note here the `example` keyword is used to define a theorem, which is a statement that needs to be proven. The `rfl` tactic is used to prove that the two terms are equal by definition.

Definitional equality as a relation satisfies reflexivity, symmetry, and transitivity, i.e.:

1. **Reflexivity**: For any term `a`, `a = a`
  ```lean
  example (a : Nat) : a = a := rfl
  ```

2. **Symmetry**: If `a = b`, then `b = a`
  ```lean
  example (a b : Nat) (h : a = b) : b = a := Eq.symm h
  ```

3. **Transitivity**: If `a = b` and `b = c`, then `a = c`
  ```lean
  example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := Eq.trans h₁ h₂
  ```

Definitional equality is important in type theory because:

- It's automatic and doesn't require explicit proofs, i.e., it's built into the system
- It's used by the type checker to ensure the correctness of programs
- It's based on computation rules and the structure of terms
- It's decidable (the system can always determine if two terms are definitionally equal)

## Computational Equality

Computational equality arises when expressions are not identical as written but can be reduced to the same value through computation. This includes evaluating functions, simplifying expressions, and performing arithmetic operations. An example of such an equality is applying a function:

```lean
example : (λ x, x + x) 2 = 2 + 2 :=
  rfl
```

Here `λ x, x + x` is a lambda function that doubles its argument, and `(λ x, x + x) 2` applies this function to `2`, which evaluates to `2 + 2`. The `rfl` tactic is used to prove that the two expressions are equal by computation.

Expansions of recursors also fall under this kind of equality:

```lean
example : 2 + 2 = Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) :=
  rfl

example : Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) = Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))) :=
  rfl
```

Even though `2 + 2` and `Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))` look different, they both reduce to the number 4 through computation, so they are computationally equal.

In Lean, computational equality can be conflated with definitional equality because both rely on the underlying computation rules of the system.

Computational equality satisfies the same properties as definitional equality: reflexivity, symmetry, and transitivity.

1. **Reflexivity**: For any term `a`, `a = a`.

   ```lean
   example (a : Nat) : a = a := rfl
   ```

2. **Symmetry**: If `a = b`, then `b = a`.

   ```lean
   example (a b : Nat) (h : a = b) : b = a := Eq.symm h
   ```

3. **Transitivity**: If `a = b` and `b = c`, then `a = c`.

   ```lean
   example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := Eq.trans h₁ h₂
   ```

Computational equality is based on the idea that expressions can be reduced through computation to establish equality. Practically, computational equalities can often be handled automatically using tactics like `rfl`, which checks for definitional equality and is thus deeply integrated into Lean's type-checking system.

## Propositional Equality

Propositional equality is a more general form of equality that requires explicit proofs. It represents the notion that two expressions are equal because there exists a proof that demonstrates their equality, even if they are not definitionally or computationally equal. For instance, the commutativity of addition can be expressed as a proposition:

```lean
theorem add_comm (a b : Nat) : a + b = b + a :=
begin
  induction a with a ha,
  { simp },
  { simp [ha] },
end
```

Propositional equality is represented in Lean using the `=` symbol, which is defined as an inductive type:

```lean
inductive eq {α : Sort u} (a : α) : α → Prop
  | refl : eq a
```

The `eq` type is a binary relation that takes two arguments of the same type and returns a proposition. The `refl` constructor of `eq` represents reflexivity, which states that every element is equal to itself. The `eq` type is used to define the propositional equality in Lean.

Propositional equality satisfies some properties of relations:


1. **Reflexivity**: For any element `a`, `a = a`. This is captured by the `refl` constructor:

    ```lean
    example (a : Nat) : a = a := eq.refl a
    ```

2. **Symmetry**: If `a = b`, then `b = a`. This can be proved using the `eq.symm` theorem:

    ```lean
    example (a b : Nat) (h : a = b) : b = a := eq.symm h
    ```

3. **Transitivity**: If `a = b` and `b = c`, then `a = c`. This is proved using the `eq.trans` theorem:

    ```lean
    example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := eq.trans h₁ h₂
    ```

4. **Substitution**: If `a = b`, then for any function `f`, `f a = f b`. This is captured by the `congrArg` theorem:

    ```lean
    example (a b : Nat) (f : Nat → Nat) (h : a = b) : f a = f b := congrArg f h
    ```

****
[Product Types / Σ-types](./Types.product.html)
