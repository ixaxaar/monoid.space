---

[Contents](contents.html)
[Previous](Lean.types.html)
[Next](Lean.algorithms.html)

# Functions

---

- [Basic Syntax](#basic-syntax)
- [Pattern matching](#pattern-matching)
  - [Syntax](#syntax)
  - [The Logical Not](#the-logical-not)
  - [The logical AND](#the-logical-and)
  - [The logical OR](#the-logical-or)
  - [The logical XOR](#the-logical-xor)
  - [Pattern matching with guards](#pattern-matching-with-guards)
  - [Nested pattern matching](#nested-pattern-matching)
- [Recursion](#recursion)
  - [Addition of natural numbers](#addition-of-natural-numbers)
  - [Length of a List](#length-of-a-list)
- [Dependent Types](#dependent-types)
  - [Syntax](#syntax-1)
  - [Conditional Types](#conditional-types)
  - [Length-Indexed Vectors](#length-indexed-vectors)
  - [Working with Implicit Arguments](#working-with-implicit-arguments)
- [Lambda Functions](#lambda-functions)
  - [Syntax](#syntax-2)
  - [Implicit Arguments](#implicit-arguments)
  - [Dependent Pattern Matching](#dependent-pattern-matching)
  - [Map](#map)
- [Advanced Concepts](#advanced-concepts)
  - [Parametric Polymorphism](#parametric-polymorphism)
  - [Function Composition](#function-composition)
  - [Currying and Partial Application](#currying-and-partial-application)
  - [Local definitions](#local-definitions)
  - [Termination Checking](#termination-checking)
  - [Mutual Recursion](#mutual-recursion)
  - [Higher-Order Functions](#higher-order-functions)

Functions in Lean are defined using the `def` keyword. The syntax for defining functions in Lean is similar to defining inductive types.

These are the different types of functions we can define in Lean:

| Type of Function | Description                                                   |
| ---------------- | ------------------------------------------------------------- |
| Pattern-matching | Functions that match patterns to produce outputs              |
| Recursive        | Functions that call themselves to compute results             |
| Dependent        | Functions where the result type depends on the argument value |
| Lambda           | Anonymous functions that can be passed as arguments           |

Functions are also first-class citizens in Lean, meaning they can be passed as arguments to other functions, returned as results, and stored in data structures.

## Basic Syntax

The syntax for defining functions in Lean is as follows:

```lean
def functionName (arg1 : Type1) (arg2 : Type2) ... (argN : TypeN) : ReturnType :=
  -- function body here
```

The function body may be a single expression or a block of code, or it may use pattern matching to define different cases for the function or it may be recursive or any combination of these.

Here is an example of a simple function that is a single expression (adds two natural numbers):

```lean
def add (x : Nat) (y : Nat) : Nat :=
  x + y
```

A function defined using pattern matching (computes the factorial of a natural number):

```lean
def factorial : (x : Nat) → Nat
  match x with
    | 0 => 1
    | n+1 => (n+1) * factorial n
```

A function that is recursive (computes the length of a list):

```lean
def length {α : Type} : (x : List α) → Nat
  match x with
    | []      => 0
    | _ :: xs => 1 + length xs
```

And finally an example combining all of these (computes the sum of squares of a list of natural numbers):

```lean
def sumOfSquares : (x : List Nat) → Nat
  match x with
    | []      => 0
    | x :: xs => x * x + sumOfSquares xs
```

Lets look at each of these in more detail.

## Pattern matching

Pattern-matching functions are functions that match patterns to produce outputs. They are defined using the `def` keyword, followed by the function name, type, and pattern-matching clauses.

### Syntax

The verbose lean syntax for pattern matching functions is:

```lean
def functionName : inputType → outputType
  match inputType with
    | pattern₁ => output₁
    | pattern₂ => output₂
    ...
    | patternN => outputN
```

This can be shortened to:

```lean
def functionName : inputType → outputType
  | pattern₁ => output₁
  | pattern₂ => output₂
  ...
  | patternN => outputN
```

There is also a version of pattern matching that uses a wildcard pattern (`_`) to match any value:

```lean
def functionName : inputType → outputType
  | pattern₁ => output₁
  | _        => defaultOutput
```

There are also infix functions, which are functions that can be used in infix notation. For example, the `and` function can be used as `true ∧ false`.

```lean
def functionName : inputType → inputType → outputType
  | pattern₁, pattern₂ => output
  | pattern₃, pattern₄ => output
```

Finally, you can define functions with multiple arguments:

```lean
def functionName : inputType₁ → inputType₂ → outputType
  | pattern₁, pattern₂ => output
  | pattern₃, pattern₄ => output
```

### The Logical Not

The simplest of functions simply match patterns. For example, the function for `not`:

```lean
def not : Bool → Bool
  | true  => false -- return false if we are given a true
  | false => true  -- return a true if we are given a false
```

We could also use a wildcard pattern (`_`) like this:

```lean
def not₁ : Bool → Bool
  | true => false -- return false if we are given a true
  | _    => true  -- return true in all other cases
```

### The logical AND

In Lean, function names containing symbols can be used as infix operators. We can define precedence and associativity using `infix`, `infixl`, or `infixr`.

```lean
def and : Bool → Bool → Bool
  | true,  b => b     -- true AND whatever is whatever
  | false, _ => false -- false AND whatever is false

infixr:70 " ∧ " => and
```

This can be applied as:

```lean
#check true ∧ false ∧ true  -- Bool
#eval true ∧ false ∧ true   -- false
```

### The logical OR

```lean
def or : Bool → Bool → Bool
  | true,  _ => true -- true or whatever is true
  | false, b => b    -- false or whatever is whatever

infixr:60 " ∨ " => or
```

which can be applied as:

```lean
#check true ∨ false ∨ true  -- Bool
#eval true ∨ false ∨ true   -- true
```

### The logical XOR

The xor function with multiple arguments and wildcards:

```lean
def xor : Bool → Bool → Bool
  | true,  false => true  -- true XOR false is true
  | false, true  => true  -- false XOR true is true
  | _,     _     => false -- all other cases are false
```

### Pattern matching with guards

"Guards" are conditions that can be added to pattern-matching clauses to further refine the matching process. They are represented by `if` expressions that evaluate to `true` or `false`. Guards can be used to add conditions to patterns like the `max3` below function which takes three natural numbers `x`, `y`, and `z` and returns the maximum of the three numbers. It uses pattern matching with guards to compare the numbers and determine the maximum.

```lean
def max3 : Nat → Nat → Nat → Nat
  | x, y, z if x >= y && x >= z => x -- x is largest
  | x, y, z if y >= x && y >= z => y -- y is largest
  | x, y, z                     => z -- z is largest
```

### Nested pattern matching

Pattern matching can also be nested to handle more complex patterns, as well as using `match` expressions inside function bodies. For example, the `deepMatch` function takes a list of optional natural numbers (`List (Option Nat)`) and computes a natural number based on the values in the list. It uses nested pattern matching to handle the different cases of the list and the optional values. Note that `::` here is the list constructor, and `none` and `some n` are the constructors for the `Option` type.

```lean
def deepMatch : List (Option Nat) → Nat
  | [] => 0
  | none :: xs => deepMatch xs
  | some n :: xs =>
    match n with
    | 0 => deepMatch xs
    | m+1 => m + 1 + deepMatch xs
```

## Recursion

Recursive functions are functions that call themselves to compute results. They are useful for defining functions that operate on recursive data structures or have recursive behavior. The syntax for defining recursive functions in Lean is similar to pattern-matching functions, but with a recursive call to the function itself.

### Addition of natural numbers

The addition of natural numbers is a classic example of a recursive function. Here's how it can be defined in Lean:

```lean
def add : Nat → Nat → Nat
  | 0,    n => n -- base case: 0 + n is n
  | m+1,  n => (add m n) + 1 -- recursive case: (m+1) + n is (m + n) + 1

infixl:65 " + " => add
```

### Length of a List

The length of a list consists of traversing through the list and adding one for each element:

```lean
def length {α : Type} : List α → Nat
  | []      => 0 -- base case: empty list has length 0
  | _ :: xs => 1 + length xs -- recursive case: 1 + length of the rest of the list
```

The `length` function takes a list of any type `α` and returns a natural number (`Nat`). It uses pattern matching to handle two cases:

1. If the list is empty (`[]`), the length is `0`.
2. If the list has at least one element (`_ :: xs`), the length is 1 plus the length of the rest of the list (`xs`).

This function recursively processes the list, accumulating the total count of elements until it reaches the empty list.

## Dependent Types

Dependent function types, also known as Π-types (Pi-types), represent one of the most powerful features in dependent type theory and Lean. Unlike simple function types where input and output types are fixed, dependent function types allow the _output type to depend on the input value_. This capability enables us to express complex relationships between values and types that would be impossible in simply-typed languages.

### Syntax

In Lean, dependent function types can be written in several ways:

- Using `Π` (Pi) notation
- Using `∀` (forall) notation
- Using arrow notation `→` when appropriate

Let's start with a simple example to illustrate the concept:

```lean
def id {α : Type} (x : α) : α := x
```

Here, `id` is a function that takes a value `x` of any type `α` and returns the same value. The type variable `α` is implicit, meaning Lean can infer it from the context when the function is called. This function is polymorphic, as it can operate on values of any type.

### Conditional Types

One powerful application of dependent types is the ability to have different return types based on a condition. Here's an example:

```lean
/-- This function returns either a Nat or a String depending on the boolean input.
    Note how the return type uses an if-expression directly in the type! -/
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
```

Let's examine what happens when we use this function:

```lean
#check natOrStringThree true   -- Nat
#check natOrStringThree false  -- String
#eval natOrStringThree true    -- 3
#eval natOrStringThree false   -- "three"
```

As we can see, the return type of `natOrStringThree` depends on the input value `b`. If `b` is `true`, the function returns a `Nat`, and if `b` is `false`, it returns a `String`.

### Length-Indexed Vectors

Perhaps the most classic example of dependent types is vectors - lists whose lengths are encoded in their types. This example showcases how dependent types can enforce properties at the type level:

A Vector is a list whose length is tracked in its type. α is the type of elements. The second parameter (Nat) indicates this is indexed by natural numbers:

```lean
inductive Vector (α : Type) : Nat → Type
  | nil  : Vector α 0                                        -- Empty vector has length 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)    -- Adding an element increases length by 1
```

Get the length of a vector. Note that we don't need to examine the vector itself, as the length is encoded in its type:

```lean
def vectorLength {α : Type} {n : Nat} (v : Vector α n) : Nat := n
```

Append two vectors. Notice how the return type shows that lengths add:

```lean
def append {α : Type} : {n m : Nat} → Vector α n → Vector α m → Vector α (n + m)
  | 0, m, Vector.nil, ys => ys
  | n+1, m, Vector.cons x xs, ys => Vector.cons x (append xs ys)
```

Let's create some vectors to see how this works:

```lean
def v1 := Vector.cons 1 Vector.nil           -- Vector Nat 1
def v2 := Vector.cons 2 (Vector.cons 3 Vector.nil)  -- Vector Nat 2
#check append v1 v2  -- Vector Nat 3
```

### Working with Implicit Arguments

Dependent types often work with implicit arguments, which Lean can infer from context. Consider a function that creates a vector of a specified length filled with a value:

```lean
-- Notice how {α : Type} is implicit but (n : Nat) is explicit
def replicate {α : Type} (n : Nat) (x : α) : Vector α n :=
  match n with
  | 0 => Vector.nil
  | n+1 => Vector.cons x (replicate n x)
```

Next, we define a `map` function that applies a function to each element of a vector:

```lean
def map {α β : Type} {n : Nat} (f : α → β) : Vector α n → Vector β n
  | Vector.nil => Vector.nil
  | Vector.cons x xs => Vector.cons (f x) (map f xs)
```

Let's see how these functions work:

```lean
#eval replicate 3 true   -- Vector of 3 trues
#check map (· + 1) (replicate 3 0)  -- Vector Nat 3
```

As we can see, the `replicate` function creates a vector of a specified length filled with a given value, and the `map` function applies a function to each element of a vector.

## Lambda Functions

Lambda functions, also known as anonymous functions, are functions that are not bound to a specific name. They are useful for defining functions on the fly, passing functions as arguments, and returning functions as results. In Lean, lambda functions are defined using the `λ` symbol.

### Syntax

Lambda (or anonymous) functions can be defined using the following syntax:

```lean
def example₁ := λ (α : Type) (x : α) => x
```

Here are a few examples of lambda functions:

### Implicit Arguments

Functions in Lean can work with implicit parameters, which means the compiler can infer certain argument values. For example:

```lean
def append {α : Type} : List α → List α → List α
  | [],    ys => ys
  | x::xs, ys => x :: append xs ys

infixr:65 " ++ " => append
```

Curly braces `{}` denote implicit arguments in Lean. Values of implicit arguments are derived from other argument values and types by solving type equations. You don't have to apply them explicitly (though they can be explicitly passed like `@function_name α`).

This function takes a type as a parameter `α`, and thus can work on `List`s of any type `α`. This feature of functions is called "parametric polymorphism", more on that later.

### Dependent Pattern Matching

Lean supports dependent pattern matching, which is similar to Agda's dot patterns. Here's an example:

```lean
inductive Square : Nat → Type where
  | sq : (m : Nat) → Square (m * m)

def root : (n : Nat) → Square n → Nat
  | _, Square.sq m => m
```

### Map

We implement the `map` function, of "map-reduce" fame, for `List`s:
A map function for a `List` is a function that applies a lambda (un-named) function to all elements of a `List`.

If `f` were a lambda function, mapping `f` over `List(a, b, c, d)` would produce `List(f(a), f(b), f(c), f(d))`

```lean
def map {α β : Type} : (α → β) → List α → List β
  | _, []      => []
  | f, x :: xs => f x :: map f xs
```

Here, we apply the function `addOne` to a list, using `map`:

```lean
def addOne : Nat → Nat
  | x => x + 1

#eval map addOne [1, 2, 3, 4]  -- Output: [2, 3, 4, 5]
```

## Advanced Concepts

### Parametric Polymorphism

Parametric polymorphism is a feature of some programming languages that allows functions and data types to be generic over types. This means that functions and data types can be defined without specifying the exact type they operate on, making them more flexible and reusable.

In Lean, parametric polymorphism is achieved using type variables. Type variables are placeholders for types that can be instantiated with any concrete type. They are denoted by names enclosed in curly braces `{}`.

Here's an example of a parametrically polymorphic function in Lean:

```lean
def id {α : Type} (x : α) : α := x
```

In this example, `id` is a function that takes a value of any type `α` and returns the same value. The type variable `α` is used to indicate that the function is generic over types.

Lets now look at a slightly more complex example:

```lean
def swap {α β : Type} (p : α × β) : β × α :=
  match p with
  | (a, b) => (b, a)
```

In this example, `swap` is a function that takes a pair of values of types `α` and `β` and returns a pair with the values swapped. The type variables `α` and `β` indicate that the function is generic over types. The function `swap` can be used with any pair of values of any types:

```lean
#eval swap (1, "hello")  -- Output: ("hello", 1)
#eval swap ("world", 42)  -- Output: (42, "world")
```

### Function Composition

Function composition is a fundamental concept in functional programming that allows you to combine multiple functions to create a new function. In Lean, function composition can be achieved using the `∘` operator.

Here's an example of function composition in Lean:

```lean
def addOne : Nat → Nat := λ x => x + 1
def double : Nat → Nat := λ x => x * 2
```

We can compose the `addOne` and `double` functions to create a new function that first adds one to a number and then doubles the result:

```lean
def addOneThenDouble : Nat → Nat := double ∘ addOne
```

The `∘` operator is used to compose the `double` function with the `addOne` function. The resulting `addOneThenDouble` function first applies `addOne` to a number and then applies `double` to the result.

### Currying and Partial Application

Currying is the process of converting a function that takes multiple arguments into a sequence of functions, each taking a single argument. This allows for partial application of functions, where some arguments are provided, and the function returns a new function that takes the remaining arguments.

In Lean, currying and partial application can be achieved using lambda functions. Here's an example:

```lean
def add : Nat → Nat → Nat := λ x y => x + y
```

The `add` function takes two arguments and returns their sum. We can curry the `add` function to create a new function that takes one argument and returns a function that takes the second argument:

```lean
def addCurried : Nat → Nat → Nat := λ x => λ y => x + y
```

We can then partially apply the `addCurried` function to create a new function that adds 5 to a number:

```lean
def addFive : Nat → Nat := addCurried 5
```

The `addFive` function is a partially applied version of the `addCurried` function that adds 5 to a number. We can use the `addFive` function to add 5 to any number:

```lean
#eval addFive 10  -- Output: 15
#eval addFive 20  -- Output: 25
```

### Local definitions

Local definitions are used to define functions or values within the scope of another function. They are useful for breaking down complex functions into smaller, more manageable parts.

Here's an example of using local definitions in Lean:

```lean
def sumOfSquares : Nat → Nat → Nat
| x, y =>
  let square (z : Nat) : Nat := z * z
  square x + square y
```

In this example, the `sumOfSquares` function takes two numbers `x` and `y` and calculates the sum of their squares. The `square` function is defined locally within the `sumOfSquares` function and is used to calculate the square of a number.

Local definitions are scoped to the function in which they are defined and cannot be accessed outside that function. They are a powerful tool for organizing and structuring code.

### Termination Checking

In Lean, functions are required to be total, meaning they must terminate for all inputs. This is enforced by the termination checker, which ensures that recursive functions make progress towards a base case.

Here's an example of a recursive function that calculates the factorial of a number:

```lean
def factorial : Nat → Nat
| 0 => 1
| n+1 => (n+1) * factorial n
```

The `factorial` function calculates the factorial of a number by recursively multiplying the number by the factorial of the previous number until it reaches the base case of 0. The termination checker ensures that the recursive calls to `factorial` make progress towards the base case of 0.

Functions that do not terminate or make progress towards a base case will be rejected by the termination checker, preventing non-terminating functions from being defined in Lean.

### Mutual Recursion

Mutual recursion is a technique where two or more functions call each other in a cycle. This can be useful for defining functions that have interdependent behavior.

Here's an example of mutual recursion in Lean:

```lean
mutual
  def isEven : Nat → Bool
  | 0 => true
  | n+1 => isOdd n

  def isOdd : Nat → Bool
  | 0 => false
  | n+1 => isEven n
```

In this example, the `isEven` and `isOdd` functions are defined mutually recursively. The `isEven` function checks if a number is even by calling the `isOdd` function, and the `isOdd` function checks if a number is odd by calling the `isEven` function. This mutual recursion allows the functions to work together to determine if a number is even or odd.

### Higher-Order Functions

Higher-order functions are functions that take other functions as arguments or return functions as results. They are a powerful feature of functional programming that allows for the composition and abstraction of functions.

Here's an example of a higher-order function in Lean:

```lean
def apply {α β : Type} (f : α → β) (x : α) : β := f x
```

The `apply` function takes a function `f` that maps values of type `α` to values of type `β` and a value `x` of type `α` and applies the function `f` to the value `x`. This higher-order function allows for the application of arbitrary functions to values.

A slight variation of the `apply` function is the `applyTwice` function:

```lean
def applyTwice {α : Type} (f : α → α) (x : α) : α := f (f x)
```

The `applyTwice` function takes a function `f` and a value `x` of type `α` and applies the function `f` twice to the value `x`. This higher-order function allows for the composition of functions by applying a function multiple times.

Similarly, higher order functions can be used to define functions that return functions as results. For example:

```lean
def addN : Nat → Nat → Nat := λ n => λ x => x + n
```

The `addN` function takes a number `n` and returns a function that adds `n` to a number. This higher-order function allows for the creation of specialized functions that add a specific number to values.

Filtering functions are another example of higher-order functions. Here's an example of a `filter` function that takes a predicate function and a list and returns a new list containing only the elements that satisfy the predicate:

```lean
def filter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x::xs => if p x then x :: filter p xs else filter p xs
```

The `filter` function takes a predicate function `p` that maps values of type `α` to booleans, a list of values of type `α`, and returns a new list containing only the elements that satisfy the predicate `p`. This higher-order function allows for the selective extraction of elements from a list based on a condition.

---

[Algorithms](./Lean.algorithms.html)
