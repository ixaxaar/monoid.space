****
[Contents](contents.html)
[Previous](Types.equality.html)
[Next](Types.product.html)

# Operations

****

- [Operations](#operations)
  - [Operator Laws](#operator-laws)
    - [Associativity](#associativity)
    - [Commutativity](#commutativity)
    - [Identity Element](#identity-element)
    - [Elimination (Annihilator)](#elimination-annihilator)
    - [Inverse Element](#inverse-element)
    - [Distributivity](#distributivity)
    - [Absorption](#absorption)
    - [Cancellation](#cancellation)
    - [Congruence](#congruence)
    - [Respecting a Relation](#respecting-a-relation)
    - [Equivalence Relations](#equivalence-relations)

An operation can be thought of as a map or a function between types with a certain arity. Operations can also be thought of as functions that may take zero or more operands and return an output value. Some examples are addition, subtraction, multiplication, and division of natural, real, and complex numbers. Based on arity, operations can be:

- **Nullary**: Takes no arguments (e.g., a function that returns a constant).
- **Unary**: Takes one argument.
- **Binary**: Takes two arguments.
- **Ternary**: Takes three arguments.

Operations of higher arity can often be decomposed into ones of lower arity using techniques like currying. We will start by defining operations and the laws these operations may obey.

```lean
import data.set
import data.equiv
import logic.function.basic
```

A **binary operation** `★` on a set `A` is a function that takes two elements of type `A` and returns an element of `A`:

```math
★ : A × A → A
```

More often, the operation is applied to the two elements `x, y ∈ A` in an infix fashion `x ★ y`.

A **unary operation**, on the other hand, operates on only one element of `A` to return an element of `A`:

```math
♠ : A → A
```

In Lean, a homogeneous binary operation `★` on a type `A` can be defined as:

```lean
def bin_op (A : Type*) := A → A → A
```

And a unary operation `♠` as:

```lean
def unary_op (A : Type*) := A → A
```

## Operator Laws

We now describe a few laws that operations might follow. This enables us to study algebraic structures built on top of these operations, as well as structure-preserving maps (homomorphisms) that preserve the underlying structure of such objects.

### Associativity

Mathematically, given an operation `★`, it is called **associative** if:

```math
∀ x, y, z ∈ A, \quad x ★ (y ★ z) = (x ★ y) ★ z
```

In Lean, we can define associativity of a binary operation as:

```lean
def associative {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y z : A, op (op x y) z = op x (op y z)
```

### Commutativity

An operation is **commutative** if:

```math
∀ x, y ∈ A, \quad x ★ y = y ★ x
```

In Lean, commutativity is defined as:

```lean
def commutative {A : Type*} (op : A → A → A) : Prop :=
  ∀ x y : A, op x y = op y x
```

### Identity Element

An element `e ∈ A` is called an **identity element** for the operation `★` if:

```math
∀ x ∈ A, \quad e ★ x = x \quad \text{and} \quad x ★ e = x
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

### Elimination (Annihilator)

An element `z ∈ A` is called an **annihilator** for the operation `★` if:

```math
∀ x ∈ A, \quad z ★ x = z \quad \text{or} \quad x ★ z = z
```

In Lean, we define left and right zero (annihilator):

```lean
def left_zero {A : Type*} (z : A) (op : A → A → A) : Prop :=
  ∀ x : A, op z x = z

def right_zero {A : Type*} (z : A) (op : A → A → A) : Prop :=
  ∀ x : A, op x z = z

def zero {A : Type*} (z : A) (op : A → A → A) : Prop :=
  left_zero z op ∧ right_zero z op
```

### Inverse Element

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
