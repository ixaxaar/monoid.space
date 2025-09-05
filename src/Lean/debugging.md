---

[Contents](contents.html)
[Previous](Lean.other.html)
[Next](Types.introduction.html)

# Debugging

---

- [Holes](#holes)
- [Global commands](#global-commands)
  - [`#check` and `#eval`](#check-and-eval)
  - [`#print`](#print)
  - [`#reduce`](#reduce)
  - [`#exit`](#exit)
- [Goal-specific commands](#goal-specific-commands)
  - [`show_goal`](#show_goal)
  - [`trace`](#trace)
  - [`sorry`](#sorry)
  - [`have`](#have)
  - [`let`](#let)
  - [`show`](#show)
- [Practical Debugging Examples](#practical-debugging-examples)
- [Debugging Tactics](#debugging-tactics)
- [Best Practices](#best-practices)

Errors in Lean can come in many forms: type mismatches, incomplete proofs, incorrect tactics, or even logical inconsistencies. Here are some common debugging techniques used in Lean development:

1. Error messages: Lean provides detailed error messages that can help you identify the source of the problem. These messages often include information about the expected type, actual type, and the context in which the error occurred.
2. Holes: Lean allows you to insert holes in your code using the `_` symbol. These holes can be used to indicate incomplete or unknown parts of your code. You can then use the `#check` command to see the type of the hole and the context in which it appears.
3. Interactive theorem proving: Lean's interactive mode allows you to step through your code and see the state of the proof at each step. This can help you identify where the error occurred and how to fix it.

## Holes

Holes are a powerful debugging tool in Lean. They allow you to insert placeholders in your code for incomplete or unknown parts. You can then use the `#check` command to see the type of the hole and the context in which it appears. This can help you identify the source of the error and guide you in completing the proof.

Here's an example of using holes in Lean:

```lean
def add (x y : Nat) : Nat :=
  _ + y
```

In this example, the `_` symbol is used as a hole to indicate an incomplete part of the code. You can then use the `#check` command to see the type of the hole and the context in which it appears:

```lean
#check add
```

This will display the type of the `add` function and the context in which it appears, helping you identify the source of the error.

For example, `add : Nat → Nat → Nat` indicates that the `add` function takes two `Nat` arguments and returns a `Nat` value. We can then complete the definition by replacing the hole with the correct expression (e.g., `x + y`).

## Global commands

Global commands are used to interact with the Lean environment and perform various operations such as checking types, evaluating expressions, printing definitions, reducing expressions, and exiting proofs.

| Command   | Description                                                                |
| --------- | -------------------------------------------------------------------------- |
| `#check`  | Shows the type of an expression                                            |
| `#eval`   | Evaluates an expression                                                    |
| `#print`  | Displays the definition of a declaration                                   |
| `#reduce` | Reduces an expression to normal form                                       |
| `#exit`   | Terminate an unfinished proof without marking the entire file as incorrect |

### `#check` and `#eval`

The `#check` and `#eval` commands are the most basic commands used for debugging.

- **`#check`**: Use this to check the type of an expression. This is especially useful when trying to understand type mismatches or when you're unsure of the result type of a complex expression.

  ```lean
  #check 1 + 1  -- Output: Nat
  #check "Hello"  -- Output: String
  ```

- **`#eval`**: This command evaluates an expression and returns its value. It is helpful for testing functions and verifying that they behave as expected.

  ```lean
  #eval 2 + 2  -- Output: 4
  #eval "Hello, " ++ "World!"  -- Output: "Hello, World!"
  ```

### `#print`

The `#print` command can be used to see the definitions of constants, theorems, or even entire modules. This is particularly useful when you need to understand how something is implemented or when you suspect that a definition might be incorrect.

```lean
#print Nat.add
```

### `#reduce`

The `#reduce` command reduces an expression to its normal form. This can be useful when you want to see the result of a computation or when you're trying to understand how a complex expression is evaluated.

```lean
#reduce 2 + 2  -- Output: 4
#reduce 2 * 3  -- Output: 6
```

### `#exit`

The `#exit` command allows you to terminate an unfinished proof without marking the entire file as incorrect. This is useful if you want to quickly move past a problematic proof and return to it later.

```lean
example (n : Nat) : n + 0 = n := by
  -- Proof in progress
  #exit
```

## Goal-specific commands

Lean has several commands that can be used to interact with the current proof state. These commands can help understand the current goal, trace the execution of a proof, or temporarily fill a hole in a proof.

| Command     | Description                         |
| ----------- | ----------------------------------- |
| `show_goal` | Displays the current goal           |
| `trace`     | Outputs debug information           |
| `sorry`     | Temporarily fills a hole in a proof |

When working on a specific goal, Lean provides additional commands that can be used to introduce hypotheses, create local definitions, or restate the current goal.

| Command | Description                 |
| ------- | --------------------------- |
| `have`  | Introduces a new hypothesis |
| `let`   | Creates a local definition  |
| `show`  | Restates the current goal   |

### `show_goal`

The `show_goal` command displays the current goal in the proof state. This can be helpful when you're working on a complex proof and need to understand the current context.

```lean
example (n : Nat) : n + 0 = n := by
  show_goal
```

This will display the current goal in the proof state, helping you understand what you need to prove next.

### `trace`

The `trace` command outputs debug information during the execution of a proof. This can be useful for understanding how a proof is progressing or for tracing the execution of a complex proof.

```lean
example (n : Nat) : n + 0 = n := by
  trace "Starting proof"
  -- Continue with the proof
```

This will output the debug information "Starting proof" during the execution of the proof.

### `sorry`

The `sorry` command is used to temporarily fill a hole in a proof. This can be helpful when you want to work incrementally on a proof or when you're not sure how to complete a particular step.

```lean
example (n : Nat) : n + 0 = n := by
  sorry
```

This will fill the hole with a placeholder value and allow you to continue working on the proof. However, it is important to replace `sorry` with a valid proof before finalizing the proof.

### `have`

The `have` command introduces a new hypothesis in a proof. This can be useful when you need to break down a complex proof into smaller steps or when you want to document intermediate results.

```lean
example (n : Nat) : n + 0 = n := by
  have h1 : n + 0 = n := by rfl
  -- Continue with the proof
```

This introduces a new hypothesis `h1` in the proof and allows you to continue working on the proof incrementally.

### `let`

The `let` command creates a local definition in a proof. This can be useful when you need to introduce a new variable or function in a proof or when you want to simplify the proof by defining intermediate values.

```lean
example (n : Nat) : n + 0 = n := by
  let m := 0
  -- Continue with the proof
```

This creates a local definition `m` with the value `0` and allows you to use it in the proof.

### `show`

The `show` command restates the current goal in a proof. This can be useful when you want to clarify the current goal or when you need to restate the goal in a different form.

```lean
example (n : Nat) : n + 0 = n := by
  show n + 0 = n
  -- Continue with the proof
```

This restates the current goal in the proof and allows you to continue working on the proof.

## Practical Debugging Examples

Let's look at some common debugging scenarios:

1. Type Mismatch:

```lean
def incorrect_add (x : Nat) (y : Int) : Nat :=
  x + y  -- Error: type mismatch
         -- expected: Nat
         -- got: Int
```

Fix using type conversion:

```lean
def correct_add (x : Nat) (y : Int) : Nat :=
  x + y.toNat
```

2. Incomplete Pattern Matching:

```lean
inductive Color
  | Red | Green | Blue

def to_string (c : Color) : String :=
  match c with
  | Color.Red => "red"
  | Color.Green => "green"
  -- Error: missing case Color.Blue
```

3. Proof Debugging:

```lean
example (n m : Nat) : n + m = m + n := by
  induction n with
  | zero =>
    -- Use trace to debug
    trace "Base case"
    simp
  | succ n ih =>
    -- Use sorry to work incrementally
    sorry
```

## Debugging Tactics

Lean's tactic framework provides several debugging tactics that can be used to trace the execution of a proof, output custom debugging information, or simplify expressions. These tactics can be helpful when you're working on a complex proof and need to understand how the proof is progressing.

- **`trace`**: The `trace` tactic is used to output custom debugging information to the Info View. This can be useful for tracing the values of variables or the progress of a proof.

  ```lean
  example (n : Nat) : n + 0 = n := by
    trace "Starting proof"
    induction n with
    | zero => rfl
    | succ n ih =>
      trace "Inductive case"
      simp
  ```

- **`simp` and `rw`**: These tactics are also useful for debugging because they allow you to simplify expressions or rewrite parts of a proof. When a proof fails, `simp` can often help you identify which part of the expression is not simplifying as expected.

  ```lean
  example (n : Nat) : n + 0 = n := by
    simp  -- Simplifies `n + 0` to `n`
  ```

## Best Practices

1. Use Small Steps

   - Break complex proofs into smaller lemmas
   - Use `have` statements to document intermediate steps

   ```lean
   theorem complex_proof (n m : Nat) : n + m = m + n := by
     have h1 : n + 0 = n := by rfl
     have h2 : m + 0 = m := by rfl
     -- continue with smaller steps
   ```

2. Leverage Type Information

   - Use `#check` frequently
   - Examine Info View feedback
   - Insert holes (`_`) to see expected types

3. Interactive Development

   - Use `sorry` for incremental development
   - Test sub-lemmas independently
   - Keep proofs organized and well-documented

4. Error Handling

   ```lean
   def safe_div (x y : Nat) : Option Nat :=
     if y = 0 then
       none
     else
       some (x / y)
   ```

---

[Type Theory - Introduction](./Types.introduction.html)
