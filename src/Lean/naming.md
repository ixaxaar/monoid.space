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

Modules are a fundamental way to organize code in Lean, similar to other programming languages. They help to group related definitions, theorems, and proofs together, making it easier to manage large codebases.

### File-based modules

In Lean, each file implicitly declares a module with the same name as the file (without the `.lean` extension). The file path determines the module name using dot notation:

- `src/Basic.lean` → module `Basic`
- `src/Data/List.lean` → module `Data.List`
- `test/TestBasic.lean` → module `test.TestBasic` (if test directory is configured as a `root` in `lakefile.toml`)

### Importing modules

Modules can be imported using absolute paths based on the project structure:

```lean
import Basic.Numbers            -- imports src/Basic/Numbers.lean
import Data.List.Lemmas         -- imports src/Data/List/Lemmas.lean
import test.TestNumbers         -- imports test/TestNumbers.lean
import TestNumbers              -- imports test/TestNumbers.lean
```

For all the direcories listed in the `lakefile.toml` as `srcDir` or `root`, the files inside them can be imported using their relative paths.

### Explicit module declarations

You can also explicitly declare modules within a file:

```lean
module MyModule where
  -- Module contents here
  def myFunction := 42

module NestedModule where
  -- Nested module contents
  def nestedFunction := 24
```

This creates namespaces that can help organize code within a single file.

## Naming Conventions

Lean has some common naming practices, though they're more guidelines than strict rules:

1. Functions and variables: Use camelCase (e.g., `addNumbers`, `totalCount`)
2. Types and structures: Use PascalCase (e.g., `NaturalNumber`, `BinaryTree`)
3. Modules: Use PascalCase (e.g., `Data.List`, `Logic.Propositional`)
4. Constants and axioms: Often use PascalCase (e.g., `Pi`, `ExcludedMiddle`)
5. Unicode characters: Lean supports Unicode, so mathematical symbols are common (e.g., `∀`, `λ`, `→`)
6. Notation: Lean has a powerful notation system for defining custom syntax

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
