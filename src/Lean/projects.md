---

[Contents](contents.html)
[Previous](Lean.setup.html)
[Next](Lean.types.html)

# Projects and Structure in Lean

---

- [Project setup](#project-setup)
  - [Build targets](#build-targets)
  - [Organizing in files and directories](#organizing-in-files-and-directories)
    - [Simple](#simple)
    - [Multiple source directories](#multiple-source-directories)
- [Libraries and dependencies](#libraries-and-dependencies)
  - [Adding dependencies](#adding-dependencies)
  - [Common libraries](#common-libraries)
  - [Managing dependencies](#managing-dependencies)
  - [Working with local libraries](#working-with-local-libraries)
  - [Example: Complete lakefile.toml](#example-complete-lakefiletoml)
- [Modules](#modules)
  - [File-based modules](#file-based-modules)
  - [Importing modules](#importing-modules)
  - [Explicit module declarations](#explicit-module-declarations)
- [Naming Conventions](#naming-conventions)
- [Project Organization](#project-organization)
  - [Directory Structure](#directory-structure)
  - [Import Patterns](#import-patterns)
- [Learning Resources](#learning-resources)

## Project setup

Lean comes with a project management tool called `lake`. To set up a new Lean project:

1. Create a new directory for the project and navigate into it:

   ```bash
   mkdir my_lean_project
   cd my_lean_project
   ```

2. Initialize the project with `lake`:

   ```bash
   lake init
   ```

3. Build the project:

   ```bash
   lake build
   ```

### Build targets

Lean has two main types of build targets: libraries and executables. Libraries are collections of Lean code that can be reused across multiple projects, while executables are standalone programs that can be run directly. Usually a library project will also have an executable target for testing or demo purposes.

By default, `lake build` only builds library targets. To ensure executables are also built when running `lake build` without arguments, add a `defaultTargets` configuration to your `lakefile.toml`:

```toml
name = "myproject"
defaultTargets = ["MyLib", "myexe"]

[[lean_lib]]
name = "MyLib"
srcDir = "src"

[[lean_exe]]
name = "myexe"
root = "main.lean"
```

This ensures that both the library and executable are built when you run `lake build`.

### Organizing in files and directories

As Lean projects grow, code should be organized across multiple files and directories. Lake supports several ways to structure projects:

#### Simple

For basic projects, files can be organized in subdirectories within the `srcDir`:

```bash
src/
├── MyProject.lean          # Main module
├── Basic/
│   ├── Numbers.lean        # src/Basic/Numbers.lean
│   └── Structures.lean     # src/Basic/Structures.lean
└── Advanced/
    └── Theorems.lean       # src/Advanced/Theorems.lean
```

Import these files using dot notation:

```lean
import Basic.Numbers        -- imports src/Basic/Numbers.lean
import Advanced.Theorems    -- imports src/Advanced/Theorems.lean
```

#### Multiple source directories

To include files from directories outside the main `srcDir` (like test files), configure additional library targets:

```toml
[[lean_lib]]
name = "MyProject"
srcDir = "src"

[[lean_lib]]
name = "Tests"
srcDir = "."
roots = ["test"]

[[lean_exe]]
name = "test_runner"
root = "test_runner.lean"
```

With this structure, test files can be imported:

```lean
import test.TestModule      -- imports test/TestModule.lean
```

## Libraries and dependencies

Lean 4 uses `lake` as both a build system and package manager. Libraries are managed through dependencies in your project configuration.

### Adding dependencies

Dependencies must be added manually by editing the `lakefile.toml` file:

1. **Add to lakefile.toml**: Edit the project's `lakefile.toml` to include the dependency:

   ```toml
   [[require]]
   name = "mathlib"
   scope = "leanprover-community"
   ```

2. **Update dependencies**: After editing the lakefile, run:

   ```bash
   lake update
   ```

3. **Build with new dependencies**:

   ```bash
   lake build
   ```

### Common libraries

- **Mathlib**: The comprehensive mathematics library

  ```toml
  [[require]]
  name = "mathlib"
  scope = "leanprover-community"
  ```

- **Batteries**: Standard library extensions (formerly std)

  ```toml
  [[require]]
  name = "batteries"
  scope = "leanprover-community"
  ```

- **Aesop**: Automated theorem proving tactic

  ```toml
  [[require]]
  name = "aesop"
  git = "https://github.com/JLimperg/aesop"
  ```

### Managing dependencies

1. **Update all dependencies**:

   ```bash
   lake update
   ```

2. **Clean and rebuild**:

   ```bash
   lake clean
   lake build
   ```

3. **Check dependency status**:

   ```bash
   lake deps
   ```

### Working with local libraries

For local development, libraries can be referenced using relative paths in the `lakefile.toml`:

```toml
[[require]]
name = "mylib"
path = "../path/to/mylib"
```

### Example: Complete lakefile.toml

Here's an example of a mature `lakefile.toml` with multiple dependencies:

```toml
name = "MyMathProject"
version = "0.1.0"
keywords = ["math", "algebra", "category-theory"]
homepage = "https://github.com/user/MyMathProject"
repository = "https://github.com/user/MyMathProject.git"
authors = ["Author Name <email@example.com>"]
license = "Apache-2.0"
defaultTargets = ["MyMathProject", "main"]

[package]
buildType = "release"

[[lean_lib]]
name = "MyMathProject"
srcDir = "src"

[[lean_exe]]
name = "main"
root = "main.lean"

[[require]]
name = "mathlib"
scope = "leanprover-community"

[[require]]
name = "batteries"
scope = "leanprover-community"

[[require]]
name = "aesop"
git = "https://github.com/JLimperg/aesop"

[[require]]
name = "batteries"
scope = "leanprover-community"

# Local dependency example
[[require]]
name = "MyUtilLib"
path = "../MyUtilLib"
```

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

## Project Organization

### Directory Structure

Lean projects benefit from consistent organization. Here are common patterns:

**Mathematical projects:**

```bash
src/
├── Basic/
│   ├── Definitions.lean    # Core definitions
│   └── Properties.lean     # Basic properties
├── Algebra/
│   ├── Groups.lean         # Group theory
│   └── Rings.lean          # Ring theory
└── Logic/
    ├── Propositional.lean  # Propositional logic
    └── Predicate.lean      # Predicate logic
```

**Software projects:**

```bash
src/
├── Core/
│   ├── Types.lean          # Core data types
│   └── Utils.lean          # Utility functions
├── Parser/
│   ├── Lexer.lean          # Lexical analysis
│   └── Grammar.lean        # Grammar definitions
└── Compiler/
    ├── Frontend.lean       # Frontend processing
    └── Backend.lean        # Code generation
```

### Import Patterns

Lean imports should be structured to minimize dependencies and improve clarity. Here are some stuff to remember:

**Hierarchical imports:** Lean imports should ideally be hierarchical, importing from more general to more specific modules.

```lean
import Basic.Definitions    -- General definitions first
import Basic.Properties     -- Then their properties
import Algebra.Groups       -- Then specialized structures
```

**Avoiding circular imports:** Circular dependencies can lead to complications and Lean may fail to compile. Ensure that modules do not depend on each other in a circular manner.

```lean
-- ✓ Good: Clear dependency chain
Basic.Definitions → Basic.Properties → Algebra.Groups → Algebra.Advanced

-- ✗ Bad: Circular dependency
Groups ↔ Rings  -- Groups imports Rings, Rings imports Groups
```

**Selective imports:** Importing broad modules can lead to namespace pollution, leading to stuff like naming conflicts to increasing compilation times. Import only what is needed.

```lean
import Basic.Definitions (MyType, myFunction)
import Algebra.Groups (Group, group_axioms)
```

## Learning Resources

Here are recommended resources for learning Lean:

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
