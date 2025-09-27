---

[Contents](contents.html)
[Previous](Lean.types.html)
[Next](Lean.algorithms.html)

# Functions

---

- [Basic Syntax](#basic-syntax)
  - [Simple Function Syntax](#simple-function-syntax)
  - [Arrow Function Syntax](#arrow-function-syntax)
  - [Function Bodies](#function-bodies)
  - [Key Syntax Elements](#key-syntax-elements)
  - [Implicit Arguments](#implicit-arguments)
- [Pattern Matching](#pattern-matching)
  - [Two Pattern Matching Approaches](#two-pattern-matching-approaches)
  - [Multiple Arguments](#multiple-arguments)
  - [Common Patterns](#common-patterns)
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
  - [Syntax](#syntax)
  - [Conditional Types](#conditional-types)
  - [Length-Indexed Vectors](#length-indexed-vectors)
  - [Working with Implicit Arguments](#working-with-implicit-arguments)
- [Lambda Functions](#lambda-functions)
  - [Syntax](#syntax-1)
  - [Implicit Arguments](#implicit-arguments-1)
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
- [Data Structure Operations](#data-structure-operations)
  - [String Operations](#string-operations)
  - [List Operations](#list-operations)
  - [Array Operations](#array-operations)
  - [Set Operations](#set-operations)
  - [Stack Operations](#stack-operations)
  - [Queue Operations](#queue-operations)
  - [Map Operations](#map-operations)
  - [Binary Tree Operations](#binary-tree-operations)
  - [Graph Operations](#graph-operations)
  - [Shape Operations](#shape-operations)
  - [Type Class Operations](#type-class-operations)
  - [Dependent Type Operations](#dependent-type-operations)

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

Functions in Lean are defined using the `def` keyword, which is similar to function definitions in many other programming languages. However, Lean offers several syntactic forms for defining functions, each suited to different situations. Understanding these different forms will help you write more expressive and readable code.

There are two main syntactic forms for function definitions:

### Simple Function Syntax

The most straightforward way to define functions is with explicit parameters. This syntax is familiar to programmers coming from languages like TypeScript, Kotlin, or Swift:

```lean
def functionName (arg1 : Type1) (arg2 : Type2) : ReturnType :=
  functionBody
```

Here's a simple example - a function that adds two natural numbers:

```lean
def add (x : Nat) (y : Nat) : Nat :=
  x + y
```

This reads naturally: "define a function called `add` that takes two natural numbers `x` and `y`, and returns their sum."

### Arrow Function Syntax

Sometimes it's more natural to emphasize the function's type signature, especially when using pattern matching or when the function type is complex. In these cases, we use arrow syntax:

```lean
def functionName : InputType → ReturnType :=
  functionBody
```

Here's the same add function using arrow syntax:

```lean
def add : Nat → Nat → Nat :=
  fun x y => x + y
```

The arrow notation `→` reads as "maps to" - so this says "`add` maps a `Nat` to a function that maps a `Nat` to a `Nat`". This emphasizes that functions in Lean are actually curried by default - more on that later!

### Function Bodies

The body of a function - the part that actually does the computation - can be written in several different ways depending on what you're trying to achieve. Let's explore each approach:

**1. Simple expressions:**
The most straightforward approach is to write a single expression that computes the result:
```lean
def double (x : Nat) : Nat := x * 2
```

**2. Using `fun` (lambda) syntax:**
When using arrow syntax, you'll often want to use anonymous functions (lambdas) in the body:
```lean
def add : Nat → Nat → Nat := fun x y => x + y
-- or equivalently using the Greek letter λ (lambda):
def add : Nat → Nat → Nat := λ x y => x + y
```
Both `fun` and `λ` mean exactly the same thing - it's just a matter of preference!

**3. Using `match` expressions for pattern matching:**
When you need to handle different cases based on the structure of your input, `match` expressions are very powerful:
```lean
def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ => false
```

**4. Direct pattern matching (shorthand):**
For functions that are primarily about pattern matching, Lean provides a convenient shorthand:
```lean
def isZero : Nat → Bool
  | 0 => true
  | _ => false
```
This is exactly equivalent to the `match` version above, but more concise!

### Key Syntax Elements

- **`def`** - keyword to define functions
- **`fun`** or **`λ`** - lambda (anonymous) functions
- **`match ... with`** - pattern matching expressions
- **`| pattern => result`** - pattern matching cases
- **`_`** - wildcard pattern (matches anything)
- **`=>`** - separates patterns from results

### Implicit Arguments

Before we dive deeper into pattern matching and more complex functions, there's one more crucial concept to understand: implicit arguments. You'll see these everywhere in Lean code, and they make functions much more pleasant to use.

Consider this function that calculates the length of a list:

```lean
def length {α : Type} : List α → Nat  -- {α : Type} is implicit
  | []      => 0
  | _ :: xs => 1 + length xs
```

Notice the `{α : Type}` - those curly braces make this an *implicit* argument. Here's what the different bracket types mean:

- **Explicit arguments:** `(x : Type)` - you must provide these when calling the function
- **Implicit arguments:** `{x : Type}` - Lean figures these out automatically based on context
- **Type class constraints:** `[TypeClass α]` - requirements for the type (we'll cover this later)

The beauty of implicit arguments is that you don't have to think about them most of the time:

```lean
#eval length [1, 2, 3]       -- Lean knows this is a List Nat, so α = Nat
#eval length ["a", "b"]      -- Lean knows this is a List String, so α = String
```

But if for some reason you need to be explicit, you can use `@` to override the implicitness:
```lean
#eval @length Nat [1, 2, 3]  -- Explicitly tell Lean that α = Nat
```

This system makes Lean code much cleaner - imagine having to write `length Nat [1, 2, 3]` every time!

Let's explore each of these concepts in detail.

## Pattern Matching

One of the most powerful features of Lean is pattern matching, which allows functions to behave differently based on the structure of their inputs. If you've used languages like Rust, Scala, or Haskell, this will feel familiar. If not, don't worry - it's an incredibly useful concept that will soon become second nature!

Pattern matching is particularly useful when working with algebraic data types (like the ones we defined in the previous chapter). Instead of having to check conditions manually, we can let Lean automatically figure out which case we're dealing with.

As we saw in the basic syntax section, there are two main ways to write pattern matching in Lean:

### Two Pattern Matching Approaches

**1. Using `match` expressions (explicit):**
This approach is great when you need to do some computation before the pattern matching, or when the pattern matching is just part of a larger function body:

```lean
def functionName (input : InputType) : OutputType :=
  match input with
  | pattern₁ => result₁
  | pattern₂ => result₂
  | _        => defaultResult
```

**2. Direct pattern matching (shorthand):**
When your function is primarily about pattern matching (which is very common!), this shorthand syntax is cleaner and more idiomatic:

```lean
def functionName : InputType → OutputType
  | pattern₁ => result₁
  | pattern₂ => result₂
  | _        => defaultResult
```

Both approaches do exactly the same thing - it's just a matter of style and what feels more natural for your particular function.

### Multiple Arguments

One of the nice things about pattern matching is that it works seamlessly with multiple arguments. This is particularly useful for functions that need to consider combinations of different inputs:

```lean
def functionName : Type₁ → Type₂ → OutputType
  | pattern₁, pattern₂ => result₁
  | pattern₃, pattern₄ => result₂
  | _,       _        => defaultResult
```

Notice how we separate the patterns with commas, and we can mix specific patterns with wildcards (`_`) as needed.

### Common Patterns

As you work with Lean, you'll encounter these common pattern types again and again. Don't worry about memorizing them all at once - you'll pick them up naturally through practice:

- **Literal values:** `0`, `true`, `"hello"` - match exact values
- **Wildcards:** `_` - matches anything (useful for "catch-all" cases)
- **Variables:** `n`, `x` - bind the matched value to a name you can use
- **Constructors:** `none`, `some x`, `x :: xs` - match data type constructors
- **Arithmetic patterns:** `n + 1`, `m * 2` - special patterns for natural numbers

The real power comes when you combine these - for example, `some (x + 1)` matches an optional value containing a natural number that's at least 1!

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

## Data Structure Operations

Now comes the fun part - putting everything we've learned into practice! This section shows how to implement real-world operations on the data structures we defined in the Types chapter. These examples will help you see how pattern matching, recursion, and function definition work together to create useful, practical code.

Don't worry if some of these seem complex at first - they're meant to be examples you can study, experiment with, and learn from. Each operation demonstrates different aspects of functional programming in Lean, from simple pattern matching to more advanced concepts like type class constraints.

Think of this as your practice playground - try running these examples, modify them, and see what happens!

### String Operations

Let's start with something familiar - string operations! These examples show how you can implement common string functions using pattern matching. Notice how we handle the empty string case explicitly:

```lean
-- Check if a string is empty using pattern matching
def stringIsEmpty : String → Bool
  | "" => true      -- Empty string case
  | _ => false      -- Any other string

-- Get the length of a string
def stringLength : String → Nat
  | "" => 0                    -- Empty string has length 0
  | s => s.data.length        -- Use built-in length on the underlying data

-- Concatenate two strings together
def stringConcat : String → String → String
  | s1, s2 => String.mk (s1.data ++ s2.data)

-- Safely get a character at a specific position (returns Option)
def stringGet : String → Nat → Option Char
  | s, i => s.data.get? i     -- Returns 'some char' or 'none' if out of bounds
```

These functions demonstrate basic pattern matching and show how Lean handles edge cases safely - notice how `stringGet` returns an `Option` rather than potentially crashing!

### List Operations

Lists are where recursion really shines! These examples show classic recursive patterns that you'll use again and again. Pay attention to how each function handles the empty list base case and the recursive case:

```lean
-- Calculate the length of a list recursively
def listLength {α : Type} : List α → Nat
  | [] => 0                    -- Base case: empty list has length 0
  | _ :: xs => 1 + listLength xs  -- Recursive case: 1 + length of tail

-- Append two lists together (this is how ++ works!)
def listAppend {α : Type} : List α → List α → List α
  | [], ys => ys               -- Base case: appending to empty list gives second list
  | x :: xs, ys => x :: listAppend xs ys  -- Recursive: prepend head, append tails

-- Reverse a list (inefficient but educational!)
def listReverse {α : Type} : List α → List α
  | [] => []                   -- Empty list reversed is empty
  | x :: xs => listAppend (listReverse xs) [x]  -- Reverse tail, append head at end

-- Filter elements based on a predicate (higher-order function!)
def listFilter {α : Type} (p : α → Bool) : List α → List α
  | [] => []                   -- No elements to filter in empty list
  | x :: xs =>
    if p x then x :: listFilter p xs    -- Keep element if predicate is true
    else listFilter p xs               -- Skip element if predicate is false
```

These are classic examples of structural recursion - each function breaks down the problem by handling one element and recursively processing the rest. Notice how `listFilter` is a higher-order function that takes another function as an argument!

### Array Operations

Array operations built on list foundations:

```lean
def arrayGet {α : Type} (arr : Array α) (i : Nat) : Option α :=
  arr.data.get? i

def arrayPush {α : Type} (arr : Array α) (x : α) : Array α :=
  { data := arr.data ++ [x] }

def arraySize {α : Type} (arr : Array α) : Nat :=
  arr.data.length

def arrayMap {α β : Type} (f : α → β) (arr : Array α) : Array β :=
  { data := map f arr.data }
```

### Set Operations

HashSet operations for unique collections:

```lean
def setContains {α : Type} [DecidableEq α] (s : HashSet α) (x : α) : Bool :=
  s.elems.contains x

def setInsert {α : Type} [DecidableEq α] (s : HashSet α) (x : α) : HashSet α :=
  if setContains s x then s
  else { elems := x :: s.elems }

def setRemove {α : Type} [DecidableEq α] (s : HashSet α) (x : α) : HashSet α :=
  { elems := s.elems.filter (· ≠ x) }

def setUnion {α : Type} [DecidableEq α] (s1 s2 : HashSet α) : HashSet α :=
  s1.elems.foldl setInsert s2
```

### Stack Operations

Stack implementation using lists with LIFO behavior:

```lean
def stackPush {α : Type} (s : Stack α) (x : α) : Stack α :=
  { elems := x :: s.elems }

def stackPop {α : Type} (s : Stack α) : Option (α × Stack α) :=
  match s.elems with
  | [] => none
  | x :: xs => some (x, { elems := xs })

def stackPeek {α : Type} (s : Stack α) : Option α :=
  match s.elems with
  | [] => none
  | x :: _ => some x

def stackIsEmpty {α : Type} (s : Stack α) : Bool :=
  match s.elems with
  | [] => true
  | _ => false
```

### Queue Operations

Queue implementation with FIFO behavior:

```lean
def queueEnqueue {α : Type} (q : Queue α) (x : α) : Queue α :=
  { elems := q.elems ++ [x] }

def queueDequeue {α : Type} (q : Queue α) : Option (α × Queue α) :=
  match q.elems with
  | [] => none
  | x :: xs => some (x, { elems := xs })

def queuePeek {α : Type} (q : Queue α) : Option α :=
  match q.elems with
  | [] => none
  | x :: _ => some x

def queueSize {α : Type} (q : Queue α) : Nat :=
  q.elems.length
```

### Map Operations

Map operations for key-value associations:

```lean
def mapFind {α β : Type} [DecidableEq α] (m : Map α β) (key : α) : Option β :=
  match m.pairs.find? (fun (k, _) => k == key) with
  | some (_, v) => some v
  | none => none

def mapInsert {α β : Type} [DecidableEq α] (m : Map α β) (key : α) (value : β) : Map α β :=
  let filtered := m.pairs.filter (fun (k, _) => k ≠ key)
  { pairs := (key, value) :: filtered }

def mapRemove {α β : Type} [DecidableEq α] (m : Map α β) (key : α) : Map α β :=
  { pairs := m.pairs.filter (fun (k, _) => k ≠ key) }

def mapKeys {α β : Type} (m : Map α β) : List α :=
  m.pairs.map (fun (k, _) => k)
```

### Binary Tree Operations

Trees are fascinating data structures! These examples show how to work with binary search trees, where elements are organized so that smaller values go left and larger values go right.

Notice the `[Ord α]` constraint in these functions - this is a **type class constraint** that means "α must be a type that supports ordering comparisons." In other words, we need to be able to compare values with `<`, `>`, `≤`, etc. This works for numbers, strings, characters, and many other types, but not for types like functions where ordering doesn't make sense:

```lean
-- Insert a value into a binary search tree
def treeInsert {α : Type} [Ord α] (t : BinTree α) (x : α) : BinTree α :=
  match t with
  | BinTree.leaf => BinTree.node x BinTree.leaf BinTree.leaf  -- Empty tree: create new node
  | BinTree.node y left right =>
    if x < y then BinTree.node y (treeInsert left x) right     -- Smaller: insert left
    else if x > y then BinTree.node y left (treeInsert right x)  -- Larger: insert right
    else t  -- x == y, no duplicate insertion needed

-- Search for a value in the tree
def treeSearch {α : Type} [Ord α] (t : BinTree α) (x : α) : Bool :=
  match t with
  | BinTree.leaf => false                    -- Not found in empty tree
  | BinTree.node y left right =>
    if x < y then treeSearch left x          -- Search left subtree
    else if x > y then treeSearch right x    -- Search right subtree
    else true  -- x == y, found it!

-- Get all elements in sorted order (inorder traversal)
def treeInorder {α : Type} (t : BinTree α) : List α :=
  match t with
  | BinTree.leaf => []                       -- Empty tree gives empty list
  | BinTree.node x left right =>
    treeInorder left ++ [x] ++ treeInorder right  -- Left, root, right
```

These tree operations demonstrate how the structure of data can make algorithms efficient - searching a balanced tree is much faster than searching a list!

### Graph Operations

Graph traversal and analysis functions:

```lean
def graphNeighbors (v : Vertex) (g : Graph) : List Vertex :=
  g.edges.filterMap fun e =>
    if e.from == v then some e.to
    else none

def graphHasEdge (from to : Vertex) (g : Graph) : Bool :=
  g.edges.any fun e => e.from == from && e.to == to

def graphAddVertex (v : Vertex) (g : Graph) : Graph :=
  if g.vertices.contains v then g
  else { g with vertices := v :: g.vertices }

def graphAddEdge (e : Edge) (g : Graph) : Graph :=
  let g' := graphAddVertex e.from (graphAddVertex e.to g)
  if g'.edges.contains e then g'
  else { g' with edges := e :: g'.edges }
```

### Shape Operations

Pattern matching on sum types for geometric calculations:

```lean
def shapeArea : Shape → Float
  | Shape.circle r => Float.pi * r * r
  | Shape.rectangle w h => w * h

def shapePerimeter : Shape → Float
  | Shape.circle r => 2.0 * Float.pi * r
  | Shape.rectangle w h => 2.0 * (w + h)

def shapeScale (factor : Float) : Shape → Shape
  | Shape.circle r => Shape.circle (r * factor)
  | Shape.rectangle w h => Shape.rectangle (w * factor) (h * factor)
```

### Type Class Operations

Here's where Lean really shows its power! These functions work with *any* type that has the required operations. This is called "ad-hoc polymorphism" - the same function can work on numbers, strings, or any custom type you define.

You'll notice some new syntax here - the square brackets `[Add α]`, `[Ord α]`, etc. These are **type class constraints**. They tell Lean "this function only works with types that support these operations":

- `[Add α]` means "α must support addition (`+`)"
- `[OfNat α 0]` means "α must have a way to represent the number 0"
- `[Ord α]` means "α must support ordering comparisons (`<`, `≤`, etc.)"

Think of type classes as "contracts" - if a type implements the contract, it can use functions that require it:

```lean
-- Sum all elements in a list (works for any type that can be added!)
def listSum {α : Type} [Add α] [OfNat α 0] : List α → α
  | [] => 0           -- Empty list sums to zero
  | x :: xs => x + listSum xs  -- Add current element to sum of rest

-- Find the maximum of two values (works for any orderable type!)
def genericMax {α : Type} [Ord α] (x y : α) : α :=
  if x ≤ y then y else x

-- Find the maximum element in a list
def listMax {α : Type} [Ord α] : List α → Option α
  | [] => none        -- Empty list has no maximum
  | x :: xs =>
    match listMax xs with
    | none => some x          -- x is the only element
    | some y => some (genericMax x y)  -- Compare x with max of rest
```

The beauty here is that `listSum` works on `List Nat`, `List Float`, or even `List String` (since strings can be "added" via concatenation). Type classes let you write generic code that's still type-safe!

### Dependent Type Operations

Finally, here's the most advanced example - dependent types! These operations on length-indexed vectors are completely type-safe. The compiler *guarantees* that you can't take the head of an empty vector or access out-of-bounds elements:

```lean
-- Get the first element (only works on non-empty vectors!)
def vectorHead {α : Type} {n : Nat} : Vector α (n+1) → α
  | Vector.cons x _ => x    -- The type signature ensures n+1 ≥ 1, so this is safe!

-- Get everything except the first element
def vectorTail {α : Type} {n : Nat} : Vector α (n+1) → Vector α n
  | Vector.cons _ xs => xs  -- Result has length n, one less than input

-- Append two vectors (notice how the result length is n + m!)
def vectorAppend {α : Type} {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
  | Vector.nil, ys => ys                      -- 0 + m = m
  | Vector.cons x xs, ys => Vector.cons x (vectorAppend xs ys)  -- (n+1) + m = (n + m) + 1

-- Apply a function to every element (preserves length)
def vectorMap {α β : Type} {n : Nat} (f : α → β) : Vector α n → Vector β n
  | Vector.nil => Vector.nil                  -- Empty vector maps to empty vector
  | Vector.cons x xs => Vector.cons (f x) (vectorMap f xs)  -- Length preserved
```

This is the power of dependent types - the type system itself prevents runtime errors! You literally cannot call `vectorHead` on an empty vector because the types don't match.

---

[Algorithms](./Lean.algorithms.html)
