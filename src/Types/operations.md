****
[Contents](contents.html)
[Previous](Types.equality.html)
[Next](Types.product.html)

# Operations

****

- [Operations](#operations)
  - [Nullary Operations](#nullary-operations)
  - [Unary Operations](#unary-operations)
  - [Binary Operations](#binary-operations)
  - [Higher Arity Operations](#higher-arity-operations)
    - [Curry-Howard Isomorphism](#curry-howard-isomorphism)
  - [Operator Laws](#operator-laws)
    - [Associativity](#associativity)
    - [Commutativity](#commutativity)
    - [Distributivity](#distributivity)
    - [Absorption](#absorption)
    - [Cancellation](#cancellation)
  - [Special Operations](#special-operations)
    - [Identity](#identity)
    - [Inverse](#inverse)
    - [Elimination (Annihilator)](#elimination-annihilator)
    - [Congruence](#congruence)
    - [Respecting a Relation](#respecting-a-relation)
    - [Equivalence Relations](#equivalence-relations)

An operation can be thought of as a map or a function between types with a certain arity. Operations can also be thought of as functions that may take zero or more operands and return an output value. Some examples are addition, subtraction, multiplication, and division of natural, real, and complex numbers. Based on arity, operations can be:

- **Nullary**: Takes no arguments.
- **Unary**: Takes one argument.
- **Binary**: Takes two arguments.
- **Ternary**: Takes three arguments.

Operations of higher arity can often be decomposed into ones of lower arity using techniques like currying.

```lean
import Data.Set
import Data.Equiv
import Logic.Function.Basic
```

## Nullary Operations

A nullary operation `♠` on a set `A` is a function that takes no arguments and returns an element of type `A`. All constants are examples of nullary operations, as they do not require any arguments to return a value (themselves) e.g. 3 can be thought of as a nullary operation that returns 3. In Lean, a nullary operation `♠` on a type `A` can be defined as:

```lean
def nullary_operation {A : Type*} (f : A) : Prop := true
```

We can also define a nullary operation that respects a relation `R` on `A`:

```lean
def nullary_operation_respects {A : Type*} (R : A → A → Prop) (f : A) : Prop := true
```

Here, `R` is a relation on `A` that is respected by the nullary operation `f`, and respecting means that the relation `R` is preserved under the operation `f`.

## Unary Operations

A unary operation `♠` on a set `A` is a function that takes an element of type `A` and returns an element of `A`:

```math
♠ : A → A
```

In Lean, a unary operation `♠` on a type `A` can be defined as:

```lean
def unary_operation {A : Type*} (f : A → A) : Prop := true
```

We can also define a unary operation that respects a relation `R` on `A`:

```lean
def unary_operation_respects {A : Type*} (R : A → A → Prop) (f : A → A) : Prop :=
  ∀ x y : A, R x y → R (f x) (f y)
```

Here, `R` is a relation on `A` that is respected by the unary operation `f`, and respecting means that if `x ~ y`, then `f(x) ~ f(y)` i.e. the relation `R` is preserved under the operation `f`.

## Binary Operations

A binary operation `★` on a set `A` is a function that takes two elements of type `A` and returns an element of `A`:

```math
★ : A → A → A
```

In Lean, a binary operation `★` on a type `A` can be defined as:

```lean
def binary_operation {A : Type*} (op : A → A → A) : Prop := true
```

We can also define a binary operation that respects a relation `R` on `A`:

```lean
def binary_operation_respects {A : Type*} (R : A → A → Prop) (op : A → A → A) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : A, R x₁ x₂ → R y₁ y₂ → R (op x₁ y₁) (op x₂ y₂)
```

Here, "respecting" means that if `x₁ ~ x₂` and `y₁ ~ y₂`, then `x₁ ★ y₁ ~ x₂ ★ y₂` i.e. the relation `R` is preserved under the operation `op`.

## Higher Arity Operations

Operations of arity greater than 2 can be defined similarly. Higher operations can also be composed of lower arity operations. For example, a ternary operation can be defined in terms of a binary operation:

```math
♠ : A → A → A → A
♠ x y z = (x ★ y) ★ z
```

In Lean, we can define a ternary operation as:

```lean
def ternary_operation {A : Type*} (op : A → A → A → A) : Prop :=
  ∀ x y z : A, op x y z = op (op x y) z
```

### Curry-Howard Isomorphism

The Curry-Howard isomorphism is a correspondence between logic and computation. It states that logical formulas correspond to types, proofs correspond to programs, and proof normalization corresponds to program evaluation. In this context, operations can be thought of as functions that take arguments and return values, similar to functions in programming languages.

Let's break that down:

1. **Logical Formulas Correspond to Types**: Logical formulas like `A → B` correspond to types like `A → B`. For example, the formula `A → B` corresponds to the type `A → B` in Lean.
2. **Proofs Correspond to Programs**: Proofs of logical formulas correspond to programs that inhabit the corresponding types. For example, a proof of `A → B` corresponds to a program that takes an argument of type `A` and returns a value of type `B`.
3. **Proof Normalization Corresponds to Program Evaluation**: Normalizing (or simplifying) proofs corresponds to evaluating programs. For example, normalizing a proof of `A → B` corresponds to evaluating a program that takes an argument of type `A` and returns a value of type `B`.
4. **Operations Correspond to Functions**: Operations like `A → A → A` correspond to functions that take two arguments of type `A` and return a value of type `A`. For example, the operation `A → A → A` corresponds to a function that takes two arguments of type `A` and returns a value of type `A`.

This correspondence, or isomorphism, between logic and computation is the foundation of functional programming languages like Lean, where logical formulas are types and proofs are programs, and proof normalization is program evaluation, making theorem proving a form of programming possible.

There is another conseqquence of this: currying. Currying is the process of converting a function that takes multiple arguments into a sequence of functions that each take a single argument. This is useful for partial application of functions, where some arguments are fixed and others are left as parameters. In Lean, currying can be achieved using the `→` type constructor, which is right-associative:

```lean
def curry {A B C : Type*} (f : A × B → C) : A → B → C :=
  λ a b, f (a, b)
```

Practically, currying allows us to define functions that take multiple arguments as a sequence of functions that each take a single argument. This can be useful for partial application of functions, where some arguments are fixed and others are left as parameters. Currying is also a method to construct higher-arity operations from lower-arity operations.

Let us look at a more involved example in lean:

```lean
def curry {A B C : Type*} (f : A × B → C) : A → B → C :=
  λ a b, f (a, b)

def uncurry {A B C : Type*} (f : A → B → C) : A × B → C :=
  λ p, f p.1 p.2

def add : ℕ × ℕ → ℕ := λ p, p.1 + p.2
def add' : ℕ → ℕ → ℕ := curry add
def add'' : ℕ × ℕ → ℕ := uncurry add'

#eval add (3, 4)  -- 7
#eval add' 3 4     -- 7
#eval add'' (3, 4) -- 7
```

In this example, we define a binary operation `add` that takes a pair of natural numbers and returns their sum. We then curry this operation to obtain a function `add'` that takes two natural numbers and returns their sum. We also uncurry the operation to obtain a function `add''` that takes a pair of natural numbers and returns their sum. We evaluate these functions with the arguments `(3, 4)` and `3` and `4` to obtain the sum `7` in each case.

## Operator Laws

Similar to how relations have properties like reflexivity, symmetry, and transitivity, operations have properties like associativity, commutativity, identity element, inverse element, distributivity, absorption, cancellation, and congruence. These properties help us understand how operations behave and interact with each other. Mathematical objects are often defined in terms of the data they carry, the operations they support, and the laws that govern these operations.

### Associativity

Mathematically, given a binary operation `★` on a type `A`, the operation is **associative** if:

```math
∀ x, y, z ∈ A, \quad x ★ (y ★ z) = (x ★ y) ★ z
```

or order of operations does not matter, i.e. x and y can be operated on first or y and z can be operated on first, the final result will be the same.

In Lean, we can define associativity of a binary operation as:

```lean
def associative {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y z : A, op (op x y) z = op x (op y z)
```

This property can be used as:

```lean
example : associative (λ x y : Nat => x + y) :=
  λ x y z => by simp [Nat.add_assoc]
```

Here we provide an example of associativity for the addition $(+)$ operation on natural numbers. The `simp` tactic is used to simplify the expression and prove the associativity property. Note that `λ` and `fun` are used interchangeably in Lean to define functions, so this is equivalent to the above code:

```lean
example : associative (fun x y : Nat => x + y) :=
  fun x y z => by simp [Nat.add_assoc]
```

### Commutativity

A binary operation `★` on type `A` is **commutative** if:

```math
∀ x, y ∈ A, \quad x ★ y = y ★ x
```

In Lean, the commutativity of a binary operation property can be defined as:

```lean
def commutative {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y : A, op x y = op y x
```

And operations can be proven to be commutative, with an example for addition of natural numbers:

```lean
example : commutative (λ x y : Nat => x + y) :=
  λ x y => by simp [Nat.add_comm]
```

### Distributivity

An operation `*` is **distributive** over another operation `+` if:

- **Left Distributivity**:

  ```math
  ∀ x, y, z ∈ A, \quad x * (y + z) = (x * y) + (x * z)
  ```

- **Right Distributivity**:

  ```math
  ∀ x, y, z ∈ A, \quad (y + z) * x = (y * x) + (z * x)
  ```

In Lean, we define distributivity as:

```lean
def left_distributive {A : Type*} (mul add : A → A → A) : Prop :=
  ∀ x y z : A, mul x (add y z) = add (mul x y) (mul x z)

def right_distributive {A : Type*} (mul add : A → A → A) : Prop :=
  ∀ x y z : A, mul (add y z) x = add (mul y x) (mul z x)

def distributive {A : Type*} (mul add : A → A → A) : Prop :=
  left_distributive mul add ∧ right_distributive mul add
```

### Absorption

Two operations `∙` and `∘` are **absorptive** if:

```math
∀ x, y ∈ A, \quad x ∙ (x ∘ y) = x \quad \text{and} \quad x ∘ (x ∙ y) = x
```

In Lean, we define absorption as:

```lean
def absorbs {A : Type*} (op1 op2 : A → A → A) : Prop :=
  ∀ x y : A, op1 x (op2 x y) = x ∧ op2 x (op1 x y) = x

def absorptive {A : Type*} (op1 op2 : A → A → A) : Prop :=
  absorbs op1 op2 ∧ absorbs op2 op1
```

### Cancellation

An operation is **cancellative** if one can "cancel" an element from both sides of an equation involving that operation. Specifically:

- **Left Cancellation**:

  ```math
  ∀ x, y, z ∈ A, \quad x ★ y = x ★ z \implies y = z
  ```

- **Right Cancellation**:

  ```math
  ∀ x, y, z ∈ A, \quad y ★ x = z ★ x \implies y = z
  ```

In Lean, we define cancellation as:

```lean
def left_cancellative {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y z : A, op x y = op x z → y = z

def right_cancellative {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y z : A, op y x = op z x → y = z

def cancellative {A : Type*} (op : A → A → A) : Prop :=
  left_cancellative op ∧ right_cancellative op
```

## Special Operations

### Identity

An element `e ∈ A` is called an **identity element** for the operation `★` if:

```math
∀ x ∈ A, \quad e ★ x = x \quad \text{and} \quad x ★ e = x
```

Identitiy elements are unique and are often denoted as `e` or `1`. Identities can also be handled separately as left and right identities. Left identity is defined as the property that for all `x` in `A`, the operation `★` with `e` on the left side returns `x`. Similarly, right identity is defined as the property that for all `x` in `A`, the operation `★` with `e` on the right side returns `x`. The sidedness of the identity element is important for non-commutative operations. The sides can be combined to define the identity element property.

- **Left Identity**:

  ```math
  ∀ x ∈ A, \quad e ★ x = x
  ```

- **Right Identity**:

  ```math
  ∀ x ∈ A, \quad x ★ e = x
  ```

In Lean, we can define left and right identity separately and then define identity as the conjunction of both:

```lean
def left_identity {A : Type*} (e : A) (op : A → A → A) : Prop :=
  ∀ x : A, op e x = x

def right_identity {A : Type*} (e : A) (op : A → A → A) : Prop :=
  ∀ x : A, op x e = x

def identity {A : Type*} (e : A) (op : A → A → A) : Prop :=
  left_identity e op ∧ right_identity e op
```

A given function can be proven to have an identity element, with an example for the addition operation on natural numbers:

```lean
example : identity 0 (λ x y : Nat => x + y) :=
  ⟨Nat.zero_add, Nat.add_zero⟩
```

Similarly, we can prove that multiplication has an identity element:

```lean
example : identity 1 (λ x y : Nat => x * y) :=
  ⟨Nat.one_mul, Nat.mul_one⟩
```

We use the square brackets `⟨ ⟩` to construct a pair of proofs for left and right identity. The proofs are provided as lambda functions that take an argument `x` and return the result of the operation with the identity element.

I'll rewrite this with a more practical example from linear algebra and matrix operations, which is commonly used in computer graphics, data science, and engineering:

### Inverse

An element `x⁻¹ ∈ A` is called an **inverse** of `x ∈ A` with respect to identity element `e` if:

```math
x ★ x⁻¹ = e \quad \text{and} \quad x⁻¹ ★ x = e
```

Given a unary operation `♠` (denoted as `inv`), we define what it means for it to assign inverses:

```lean
def left_inverse {A : Type*} (e : A) (inv : A → A) (op : A → A → A) : Prop :=
  ∀ x : A, op (inv x) x = e

def right_inverse {A : Type*} (e : A) (inv : A → A) (op : A → A → A) : Prop :=
  ∀ x : A, op x (inv x) = e

def inverse {A : Type*} (e : A) (inv : A → A) (op : A → A → A) : Prop :=
  left_inverse e inv op ∧ right_inverse e inv op
```

### Elimination (Annihilator)

An **annihilator** (or absorbing element) is a special element that "dominates" an operation, making the result predictable regardless of what you combine it with. Its like multiplication by 0 renders any real number with the same result - 0. In matrix algebra, the zero matrix (containing all zeros) is an annihilator for matrix multiplication:

```math
\begin{bmatrix} 0 & 0 \\ 0 & 0 \end{bmatrix} \times
\begin{bmatrix} a & b \\ c & d \end{bmatrix} =
\begin{bmatrix} 0 & 0 \\ 0 & 0 \end{bmatrix}
```

The annihilator property helps in getting rid of redundant or unnecessary operations for simplification. In Lean, we can define the annihilator property as:

```lean
def left_annihilator {A : Type*} (e : A) (op : A → A → A) : Prop :=
  ∀ x : A, op e x = e

def right_annihilator {A : Type*} (e : A) (op : A → A → A) : Prop :=
  ∀ x : A, op x e = e

def annihilator {A : Type*} (e : A) (op : A → A → A) : Prop :=
  left_annihilator e op ∧ right_annihilator e op
```

An example of an annihilator for matrix multiplication can be shown as:

```lean
example : annihilator (λ i j, 0) (λ A B, λ i j, ∑ k, A i k * B k j) :=
  ⟨λ A, funext $ λ i, funext $ λ j, by simp,
   λ A, funext $ λ i, funext $ λ j, by simp⟩
```

Here, we define the annihilator as a function that takes two matrices `A` and `B` and returns a matrix of the same size with all elements as 0. We then prove that this function is an annihilator for matrix multiplication by showing that it satisfies the left and right annihilator properties.

### Congruence

A relation `~` on `A` is a **congruence** with respect to an operation `★` if it is preserved under that operation. That is:

```math
∀ a₁, a₂, b₁, b₂ ∈ A, \quad a₁ ~ a₂ \land b₁ ~ b₂ \implies (a₁ ★ b₁) ~ (a₂ ★ b₂)
```

In Lean, congruence is defined as:

```lean
def congruence {A : Type*} (R : A → A → Prop) (op : A → A → A) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : A, R a₁ a₂ → R b₁ b₂ → R (op a₁ b₁) (op a₂ b₂)
```

Additionally, for a unary operation `♠`:

```lean
def congruent_unary {A : Type*} (R : A → A → Prop) (f : A → A) : Prop :=
  ∀ a b : A, R a b → R (f a) (f b)
```

### Respecting a Relation

A function `f : A → B` **respects** a relation `∼` on `A` if:

```math
∀ x, y ∈ A, \quad x ∼ y \implies f(x) ∼ f(y)
```

In Lean, we can define this as:

```lean
def respects {A B : Type*} (R : A → A → Prop) (f : A → B) : Prop :=
  ∀ x y : A, R x y → f x = f y  -- Adjusted for equality in B
```

For operations, we may want to consider functions that preserve relations in more general contexts.

### Equivalence Relations

An **equivalence relation** on a set `A` is a relation that is reflexive, symmetric, and transitive. In Lean:

```lean
def equivalence {A : Type*} (R : A → A → Prop) : Prop :=
  reflexive R ∧ symmetric R ∧ transitive R
```

An equivalence relation partitions a set into equivalence classes where elements are related to each other.

****
[Equational Reasoning](./Algebra.equational.html)
