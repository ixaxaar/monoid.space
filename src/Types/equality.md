****
[Contents](contents.html)
[Previous](Types.relations.html)
[Next](Types.operations.html)

# Equality

****

- [Equality](#equality)
  - [Definitional Equality](#definitional-equality)
    - [The `example` Keyword](#the-example-keyword)
  - [Computational Equality](#computational-equality)
  - [Propositional Equality](#propositional-equality)
  - [Hetereogeneous Equality](#hetereogeneous-equality)
  - [Equivalence Relations](#equivalence-relations)
  - [Transport](#transport)

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

Now we need to prove that `defEqual₁` and `defEqual₂` are definitionally equal, and for that we need to introduce the `example` keyword and basic theorem proving tactics in Lean.

### The `example` Keyword

Theorem proving is at the center of Lean's functionality. The `example` keyword is used to define an unnamed theorem, while the keyword `theorem` is used to define a named theorem. The `example` keyword is often used to demonstrate theorems or properties without giving them a name. `example`s also cannot be reused in later proofs, so they are more like throwaway theorems.

Theorem proving involves tactics, which are commands that manipulate the proof state. Tactics can be used to prove theorems, simplify expressions, and interact with the proof state. The `example` keyword is often used in conjunction with tactics to demonstrate theorems or properties. Reflexivity, or the `rfl` tactic, is a common tactic used to prove equality.

As a simple example, one way to define definitional equality is by using the `rfl` tactic, which stands for "reflexivity":

```lean
def seven : Nat := 7
def also_seven : Nat := 3 + 4

-- These are definitionally equal
example : seven = also_seven := rfl
```

Similarly, our `defEqual₁` and `defEqual₂` can be proven to be definitionally equal using the `rfl` tactic:

```lean
example : defEqual₁ = defEqual₂ := rfl
```

Theorem proving can also be used to see whether definitional equality saitisfies the properties of an equivalence relation:

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
- It's decidable (the system can always determine if two terms are definitionally equal)

Notice that we have also used the `Eq` module to access the `symm` and `trans` theorems, which are used to prove symmetry and transitivity of equality, respectively. These are fundamental theorems in Lean's type theory and we are simply using them, instead of proving anything new.

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

Even though `2 + 2` and `Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))` look different, they both reduce to the number 4 through computation, so they are computationally equal. Computational equality satisfies the same properties as definitional equality: reflexivity, symmetry, and transitivity.

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

Propositional equality is a more general form of equality that requires explicit proofs. It represents the notion that two expressions are equal because there exists a proof that demonstrates their equality, even if they are not definitionally or computationally equal. Propositional equality is represented in Lean using the `=` symbol, which is defined as an inductive type:

```lean
inductive eq {α : Sort u} (a : α) : α → Prop
  | refl : eq a
```

The `eq` type is a binary relation that takes two arguments of the same type and returns a proposition. The `refl` constructor of `eq` represents reflexivity, which states that every element is equal to itself. Propositional equality is used to prove theorems and properties that are not immediately obvious from definitions or computations.

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

## Hetereogeneous Equality

Heterogeneous equality, also known as John Major equality, extends propositional equality to cases where the two terms being compared belong to different types. In Lean, heterogeneous equality is represented by the `HEq` type, which is defined as:

```lean
structure HEq {α : Sort u} (a : α) {β : Sort v} (b : β) : Prop
```

This becomes essential when working with dependent types, where types themselves can depend on values. Consider vectors:

```lean
def Vec (A : Type) (n : Nat) : Type  -- Vector type of length n
```

Here the type `Vec A n` represents a vector of length `n` with elements of type `A`. If you have two vectors `v : Vec A n` and `w : Vec A m`, where `n` and `m` are natural numbers, you can't directly compare them using propositional equality because they belong to different types. This is where heterogeneous equality comes in:

```lean
def vecEq {A : Type} {n m : Nat} (v : Vec A n) (w : Vec A m) : HEq n m → HEq (Vec A n) (Vec A m) → v = w
```

Here we defined a way to compare vectors of different lengths using heterogeneous equality. The `vecEq` function takes two vectors `v` and `w`, along with proofs that the lengths `n` and `m` are equal and that the vector types `Vec A n` and `Vec A m` are equal. This allows us to compare vectors of different lengths using heterogeneous equality.

## Equivalence Relations

An equivalence relation is a relation that is reflexive, symmetric, and transitive. Propositional equality is an example of an equivalence relation. Equivalences are used to classify structures into equivalence classes, which are sets of structures that are related by the equivalence relation. Lets look at the formal definition of an equivalence relation:

An equivalence relation on a type `A` is a relation `R : A → A → Prop` that satisfies the following properties:

1. Reflexivity: `∀ a : A, R a a`
2. Symmetry: `∀ a b : A, R a b → R b a`
3. Transitivity: `∀ a b c : A, R a b → R b c → R a c`

The property of an equivalence relation can be expressed as follows:

```lean
def reflexive {A : Type} (R : A → A → Prop) : Prop := ∀ x : A, R x x

def symmetric {A : Type} (R : A → A → Prop) : Prop := ∀ x y : A, R x y → R y x

def transitive {A : Type} (R : A → A → Prop) : Prop := ∀ x y z : A, R x y → R y z → R x z

def equivalence_relation {A : Type} (R : A → A → Prop) : Prop :=
  reflexive R ∧ symmetric R ∧ transitive R
```

This defines a function `equivalence_relation` that takes a relation `R` on type `A` and returns a proposition stating that `R` is an equivalence relation on `A`. Let us now look at using this to prove that `=` is an equivalence relation on `Nat`.Now we can use this machinery to write a proof for any given relation `R` that it is an equivalence relation. The most striaghtforward example is proving that `=` is an equivalence relation on `Nat`.

To prove that `=` is an equivalence relation on `Nat`, the strategy would be to prove that it satisfies the three properties of an equivalence relation: reflexivity, symmetry, and transitivity. For each of these properties, we can use Lean's built-in theorems and tactics to construct the proof to keep things light for now. Here is how you can prove that `=` is an equivalence relation on `Nat`:

```lean
theorem eq_is_equivalence : equivalence_relation (@Eq Nat) := by
  -- since equivalence relation is an AND of three properties, we need to prove each separately
  -- so we use And.intro to successively split the goal into three subgoals
  apply And.intro     -- Split into first part and (second ∧ third) parts
  · intro x          -- "Let x be any natural number"
    rfl              -- "Obviously x = x"

  -- first time we split (reflexivity ^ (symmetry ∧ transitivity)) into reflexivity and (symmetry ∧ transitivity)
  -- now we split (symmetry ∧ transitivity) into symmetry and transitivity
  apply And.intro     -- Split remaining into second and third parts
  · intro x y h      -- "Let x,y be numbers and h be proof that x = y"
    symm             -- "Flip the equality"
    exact h          -- "Use h to prove that they're still equal"

  -- we are left only with transitivity now, no need to split
  · intro x y z h₁ h₂ -- "Let x,y,z be numbers with h₁: x=y and h₂: y=z"
    exact Eq.trans h₁ h₂  -- "Chain the equalities together"
```

Here is the code's explanation:

In order to prove that `=` or `Eq` is an equivalence relation on `Nat`, we first use the `theorem` keyword to define a named theorem `eq_is_equivalence`. We then use the `by` keyword to start a proof block. Now, since an equivalence relation is defined as an AND `∧` of these three properties, we use `apply And.intro` to break our goal into proving each property separately. This is called **destructuring** the goal, and it's a common technique in Lean proofs.

- For reflexivity, We say "take any natural number x" `intro x` and then use `rfl` tactic to prove that `x = x`.
- For symmetry, we say "take any two numbers x and y, and assume they're equal (that's what h means)". Then symm flips the equality around, and exact h uses our assumption to complete the proof. The `h` here is the proof that `x = y`, and `symm` flips it to `y = x`.
- For transitivity, we say "take any three numbers x, y, and z, and assume that x = y and y = z". Then we use the `Eq.trans` theorem to chain these two equalities together and prove that `x = z`.

This is a common pattern in Lean proofs: you state the goal, break it down into smaller subgoals, and then prove each subgoal step by step.

Here are the new syntax elements used in this proof:

1. **`apply`**: Used when your goal matches the conclusion of another theorem/lemma
   ```lean
   apply And.intro  -- When your goal is to prove A ∧ B
   ```

2. **`intro`**: Brings hypotheses into your context
   ```lean
   intro x    -- Introduces one variable
   intro x y h -- Introduces multiple things
   ```
   - Used when proving statements with ∀ (for all) or →  (implies)

3. **`exact`**: "This exactly proves the goal"
   ```lean
   exact h    -- When h is exactly what you need to prove
   exact Eq.trans h₁ h₂  -- When combining h₁ and h₂ exactly proves your goal
   ```
   - Think of `exact` as saying "this is precisely what we need"
   - It's like fitting a perfect puzzle piece

4. **`·`** (bullet point): Separates different subgoals
   ```lean
   apply And.intro
   · first subgoal
   · second subgoal
   ```

## Transport

Intuitively, if any two elements are equal, then any property that holds for one element should also hold for the other. Transport is a fundamental principle in type theory that allows us to "transport" properties or structures along an equality path. Imagine you have a property `P` that holds for a term `x`. If you can prove that `x` is equal to another term `y`, transport allows you to "transport" the proof of `P x` to a proof of `P y`. This is formalized as:

```lean
def transport {A : Type} {x y : A} (P : A → Type) (p : x = y) : P x → P y
```

Practically, transport is used to rewrite terms based on equalities. For example, consider the following proof that the sum of two numbers is commutative:

```lean
theorem add_comm (a b : Nat) : a + b = b + a :=
begin
  induction a with a ha,
  { simp },
  { simp [ha] },
end
```

Here, `simp` is a tactic that simplifies the goal using various rules, including the commutativity of addition. The `simp` tactic uses transport to rewrite the goal based on the equality `a + b = b + a`. Transport is also intrinsically linked to **path induction**, a fundamental principle in homotopy type theory. Path induction states that to prove a property holds for any path (equality proof) between two terms, it suffices to prove it for the reflexivity path (the proof that a term is equal to itself). This is because any path can be continuously deformed into the reflexivity path. This is expressed as:

```lean
def J {A : Type} {x : A} (P : ∀ (y : A), x = y → Type)
  (refl_case : P x (Eq.refl x))
  {y : A} (p : x = y) : P y p
```

The `J` rule effectively says: "If you can prove `P` for the reflexive case where `y` is `x` and the proof `p` is `Eq.refl x`, then you can prove `P` for *any* `y` and *any* proof `p` of `x = y`." This is a powerful induction principle for reasoning about equality.

****
[Operations](./Types.operations.html)
