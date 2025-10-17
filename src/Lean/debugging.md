---

[Contents](contents.html)
[Previous](Lean.algorithms.html)
[Next](Types.introduction.html)

# Debugging

---

- [Holes](#holes)
- [Checking and Evaluating](#checking-and-evaluating)
  - [`#check`](#check)
  - [`#eval`](#eval)
- [Inspecting Definitions](#inspecting-definitions)
  - [`#print`](#print)
  - [`#reduce`](#reduce)
- [Local Definitions](#local-definitions)
  - [`let` expressions](#let-expressions)
- [Practical Debugging Examples](#practical-debugging-examples)
- [Best Practices](#best-practices)

Debugging in Lean involves understanding types, values, and how expressions evaluate. This chapter covers the basic tools you need to debug the functions and algorithms we've covered so far.

## Holes

Holes are a powerful debugging tool in Lean. They allow you to insert placeholders in your code for incomplete or unknown parts. You can use the `_` symbol to create a hole, and Lean will tell you what type is expected there.

Here's an example of using holes in Lean:

```lean
def add (x y : Nat) : Nat :=
  _ + y
```

When you hover over or check this code, Lean will tell you:

```
don't know how to synthesize placeholder
context:
x y : Nat
⊢ Nat
```

This tells you that Lean expects a `Nat` in that position. You can then replace the hole with the correct expression:

```lean
def add (x y : Nat) : Nat :=
  x + y
```

Holes are particularly useful when:

- You're building up complex expressions incrementally
- You want to see what type Lean expects in a specific position
- You're not sure what expression to write next

## Checking and Evaluating

The two most basic and frequently used debugging commands are `#check` and `#eval`.

### `#check`

Use `#check` to see the type of any expression. This is essential for understanding what you're working with:

```lean
#check 1 + 1           -- Nat
#check "Hello"         -- String
#check [1, 2, 3]       -- List Nat
#check add             -- Nat → Nat → Nat

-- Check the type of more complex expressions
#check List.map        -- {α β : Type} → (α → β) → List α → List β
#check (1, "hello")    -- Nat × String
```

### `#eval`

Use `#eval` to evaluate an expression and see its result:

```lean
#eval 2 + 2                    -- 4
#eval "Hello, " ++ "World!"    -- "Hello, World!"
#eval [1, 2, 3].length         -- 3
#eval add 5 3                  -- 8

-- Evaluate function calls
#eval map (· + 1) [1, 2, 3]    -- [2, 3, 4]
#eval listFilter (· > 2) [1, 2, 3, 4]  -- [3, 4]
```

Note: `#eval` only works on computable expressions. It won't work on proofs or non-computable functions.

## Inspecting Definitions

### `#print`

The `#print` command shows you the definition of constants, functions, or types:

```lean
#print Nat.add
#print List
#print add
```

This is useful when:

- You want to understand how a standard library function works
- You've forgotten what a function you defined earlier looks like
- You're debugging why a function behaves unexpectedly

### `#reduce`

The `#reduce` command reduces an expression to its normal form, showing all computation steps:

```lean
#reduce 2 + 2              -- 4
#reduce [1, 2] ++ [3, 4]   -- [1, 2, 3, 4]
#reduce map (· * 2) [1, 2, 3]  -- [2, 4, 6]
```

The difference between `#eval` and `#reduce`:

- `#eval` compiles and runs the code (faster, for runtime)
- `#reduce` shows the reduction steps (slower, for understanding evaluation)

## Local Definitions

### `let` expressions

Use `let` to create local bindings within expressions. This helps break down complex computations and makes debugging easier:

```lean
def sumOfSquares (x y : Nat) : Nat :=
  let xSquared := x * x
  let ySquared := y * y
  xSquared + ySquared

#eval sumOfSquares 3 4  -- 25
```

You can also use `let` for debugging by inserting intermediate values:

```lean
def complexCalculation (n : Nat) : Nat :=
  let step1 := n * 2
  let step2 := step1 + 5
  let step3 := step2 * step2
  step3

#eval complexCalculation 3  -- 121
-- If you want to debug, you can add #eval for each step
```

## Practical Debugging Examples

Let's look at common debugging scenarios:

**1. Type Mismatch:**

```lean
def incorrect_add (x : Nat) (y : Int) : Nat :=
  x + y  -- Error: type mismatch
         -- expected: Nat
         -- got: Int
```

Debug using `#check`:

```lean
#check x + y  -- This helps you see the type of the expression
```

Fix using type conversion:

```lean
def correct_add (x : Nat) (y : Int) : Nat :=
  x + y.toNat
```

**2. Understanding Function Types:**

```lean
#check map
-- {α β : Type} → (α → β) → List α → List β
-- This shows: map is polymorphic, takes a function and a list, returns a list
```

**3. Debugging Complex Expressions:**

```lean
def processData (xs : List Nat) : Nat :=
  let filtered := listFilter (· > 5) xs
  let mapped := map (· * 2) filtered
  let result := listSum mapped
  result

#eval processData [1, 6, 3, 8]             -- 28
```

**4. Incomplete Pattern Matching:**

```lean
inductive Color
  | Red | Green | Blue

def colorToString (c : Color) : String :=
  match c with
  | Color.Red => "red"
  | Color.Green => "green"
  -- Error: missing case Color.Blue

-- Use holes to find what's missing:
def colorToString' (c : Color) : String :=
  match c with
  | Color.Red => "red"
  | Color.Green => "green"
  | Color.Blue => _  -- Lean tells you: expected String
```

## Best Practices

1. **Use `#check` liberally** - Check types frequently to catch errors early

2. **Test incrementally** - Use `#eval` to test functions as you write them

3. **Break down complex functions** - Use `let` bindings to create intermediate steps

4. **Use holes strategically** - Insert `_` to see what Lean expects

5. **Keep functions small** - Smaller functions are easier to test and debug

6. **Use descriptive names** - Good names make debugging much easier

```lean
-- Good: clear what each step does
def processNumbers (xs : List Nat) : Nat :=
  let filtered := listFilter (· > 0) xs
  let doubled := map (· * 2) filtered
  listSum doubled

-- Less clear: harder to debug
def processNumbers' (xs : List Nat) : Nat :=
  listSum (map (· * 2) (listFilter (· > 0) xs))
```

7. **Test edge cases** - Always test with empty lists, zero values, etc.

```lean
#eval processNumbers []          -- Test empty case
#eval processNumbers [0]         -- Test zero
#eval processNumbers [1, 2, 3]   -- Test normal case
```

---

[Type Theory - Introduction](./Types.introduction.html)
