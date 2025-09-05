---

[Contents](contents.html)
[Previous](Lean.setup.html)
[Next](Lean.types.html)

# Naming conventions

---

- [Modules](#modules)
- [Naming Conventions](#naming-conventions)
- [Literate programming](#literate-programming)
- [Identifiers](#identifiers)
- [Other material](#other-material)

## Modules

In Lean, each file implicitly declares a module with the same name as the file (without the `.lean` extension). For example, a file named `intro.lean` implicitly declares a module named `intro`.

You can also explicitly declare modules within a file:

```lean
module MyModule where
  -- Module contents here
```

Modules can be imported using relative or absolute paths:

```lean
import Basic.Numbers            -- absolute import
import .Numbers                 -- relative import
import «Numbers»                -- import using Unicode characters
```

## Naming Conventions

- Functions and Variables: Use snake_case (e.g., is_prime, find_max).
- Types and Structures: Use PascalCase (e.g., NaturalNumber, GroupTheory).
- Modules: Generally use PascalCase for module names, such as Data.List or Algebra.Ring.
- Constants and Axioms: Use descriptive names and often use PascalCase (e.g., ExcludedMiddle, AxiomOfChoice).

## Literate programming

Lean supports literate programming through its `.lean` files. While not as extensive as Agda's literate programming options, you can include markdown-style comments in your Lean files:

```lean
/-
# This is a markdown-style comment
It can span multiple lines and include *formatting*.
-/

def example := 42
```

## Identifiers

Lean has some common naming practices, though they're more guidelines than strict rules:

1. Functions and variables: Use snake_case (e.g., `add_numbers`, `total_count`)
2. Types and structures: Use PascalCase (e.g., `NaturalNumber`, `BinaryTree`)
3. Modules: Use PascalCase (e.g., `Data.List`, `Logic.Propositional`)
4. Constants and axioms: Often use PascalCase (e.g., `Pi`, `ExcludedMiddle`)
5. Unicode characters: Lean supports Unicode, so mathematical symbols are common (e.g., `∀`, `λ`, `→`)
6. Notation: Lean has a powerful notation system for defining custom syntax

Remember that in Lean, clarity and readability are paramount. Choose names that accurately describe the purpose or behavior of the identifier. Consistency within a project or library is more important than strictly adhering to any particular convention.

## Other material

Here's a list of resources for learning Lean:

1. [Lean's official documentation](https://leanprover.github.io/lean4/doc/): A great guide to get started with Lean 4.

2. [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/): An introduction to theorem proving using Lean.

3. [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): A tutorial on formalizing mathematics in Lean.

4. [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/): A guide to functional programming concepts in Lean.

5. [Lean for the Curious Mathematician](https://leanprover-community.github.io/lean-for-the-curious-mathematician-2023/): An introduction to Lean for mathematicians.

6. [Lean Zulip Chat](https://leanprover.zulipchat.com/): A community chat for Lean users and developers.

7. [Lean Together](https://leanprover-community.github.io/lt2021/): Materials from the Lean Together workshops.

8. [Lean 4 Examples](https://github.com/leanprover/lean4-samples): A collection of example Lean 4 projects.

9. [The Natural Number Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/): An interactive tutorial for learning Lean through number theory.

10. [Formal Abstractions](https://www.youtube.com/c/FormalAbstractions): A YouTube channel with Lean tutorials and demonstrations.

---

[Types](./Lean.types.html)
