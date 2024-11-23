****
[Contents](contents.html)
[Previous](Lean.functions.html)
[Next](Lean.debugging.html)

# Modules and Projects

****

- [Modules and Projects](#modules-and-projects)
  - [Basics](#basics)
  - [Projects](#projects)
    - [File Structure](#file-structure)
    - [Module System](#module-system)
    - [Lake Package Manager](#lake-package-manager)
  - [Tooling and Development Environment](#tooling-and-development-environment)
    - [VSCode Integration](#vscode-integration)
    - [Infoview](#infoview)
    - [Documentation](#documentation)
    - [Debugging Tools](#debugging-tools)
      - [Print Statements](#print-statements)
      - [Holes and Placeholders](#holes-and-placeholders)
  - [Advanced Features](#advanced-features)
    - [Metaprogramming](#metaprogramming)
    - [Custom Syntax](#custom-syntax)
    - [Unicode Support](#unicode-support)
  - [Best Practices](#best-practices)
    - [Naming Conventions](#naming-conventions)
    - [Code Organization](#code-organization)
    - [Performance Considerations](#performance-considerations)
  - [Common Patterns](#common-patterns)
    - [Error Handling](#error-handling)
    - [Builder Pattern](#builder-pattern)
    - [Monadic Operations](#monadic-operations)

## Basics

Lean files typically end with a `.lean` extension, and each file represents a module. The name of the file implicitly determines the name of the module, and this module can be imported by other modules.

- Each Lean file (.lean) defines a module, and the name of the file without the extension is the name of the module. For example, a file named group_theory.lean will define a module called group_theory.
- Files are organized into folders, and folder names are used as prefixes for module names. For instance, a file located at src/algebra/group.lean would define a module named algebra.group.

To quickly get started with Lean, you can create a simple `.lean` file and open it in vscode with the Lean extension installed. You can then start writing Lean code and see the real-time type information and error messages.

```lean
def hello : String := "Hello, Lean!"
#check hello
```

The lean extension has a sidebar that shows the structure of the file, and you can navigate to different sections of the file by clicking on the items in the sidebar, called the "lean infoview". The infoview also shows the type of the current expression under the cursor and any errors in the file. The infoview can be toggled using the `ctrl+shift+enter` shortcut.

The file can also be compiled using the Lean compiler, which will check the syntax and type correctness of the code. The Lean compiler can be run from the command line using the `lean` command.

```bash
lean my_file.lean
```

This is great to start a new project or experiment with Lean code. However, for larger projects, it is recommended to use a more structured approach with multiple files and modules.

## Projects

### File Structure
In Lean, projects typically follow a standard directory structure:

```
my_project/
├── lakefile.lean    # Project configuration file
├── lean-toolchain  # Specifies Lean version
├── Main.lean       # Main entry point
└── src/            # Source files
    ├── Basic/      # Basic definitions
    ├── Logic/      # Logic-related modules
    └── Utils/      # Utility functions
```

### Module System

Modules in Lean are used to organize code and manage namespaces. Each `.lean` file automatically creates a module matching its path.

```lean
-- In src/Basic/Numbers.lean
namespace Basic.Numbers

def add (x y : Nat) : Nat := x + y

end Basic.Numbers
```

Modules can be imported using relative or absolute paths:

```lean
import Basic.Numbers            -- absolute import
import «Basic.Numbers»         -- with quotes for names containing spaces
```

### Lake Package Manager

Lake is Lean's built-in package manager and build system. It uses `lakefile.lean` for configuration:

```lean
import Lake
open Lake DSL

package «my_project» where
  -- Package metadata
  version := "1.0"
  dependencies := #[
    { name := "mathlib4"
      git := "https://github.com/leanprover-community/mathlib4.git"
      rev := "main" }
  ]

lean_lib «MyProject» where
  -- Library configuration
  root := `src
```

Common Lake commands:
```bash
lake build        # Build the project
lake exe         # Build and run executables
lake clean       # Clean build artifacts
```

## Tooling and Development Environment

### VSCode Integration
VSCode is the primary IDE for Lean development. The Lean extension provides:
- Syntax highlighting
- Real-time type information
- Interactive theorem proving
- Go to definition
- Auto-completion

### Infoview
The Infoview panel is crucial for Lean development:
- Shows real-time type information
- Displays proof state
- Provides error messages
- Shows documentation

### Documentation
Lean supports documentation strings using `/-! ... -/` for modules and `/-- ... -/` for definitions:

```lean
/-!
# Basic Arithmetic Module
This module provides basic arithmetic operations.
-/

/--
`add` performs addition on natural numbers.
# Examples
```lean
#eval add 2 3  -- returns 5
```
-/
def add (x y : Nat) : Nat := x + y
```

### Testing
Lean supports unit testing through its `test` command:

```lean
def double (x : Nat) : Nat := x * 2

#test double 2 = 4        -- Basic test
#test double 0 = 0        -- Edge case
```

### Debugging Tools

#### Print Statements
```lean
def debugExample (x : Nat) : Nat :=
  dbg_trace "Processing {x}"  -- prints debug info
  x + 1
```

#### Holes and Placeholders
```lean
def incomplete (x : Nat) : Nat :=
  let y := x + 1
  sorry    -- placeholder for incomplete implementation
```

## Advanced Features

### Metaprogramming
Lean supports metaprogramming through its macro system:

```lean
macro "mylet" id:ident ":=" val:term : command =>
  `(def $id := $val)

mylet example := 42
```

### Custom Syntax
Lean allows defining custom syntax using macros:

```lean
syntax "show" term : tactic
macro_rules
  | `(tactic| show $e) => `(tactic| exact $e)
```

### Unicode Support
Lean has extensive Unicode support for mathematical notation:

```lean
def π : Float := 3.14159
def ∑ (f : Nat → Nat) (n : Nat) : Nat :=
  if n = 0 then f 0 else f n + ∑ f (n-1)
```

## Best Practices

### Naming Conventions
- Type names: PascalCase (e.g., `MyType`)
- Functions: camelCase (e.g., `myFunction`)
- Variables: camelCase (e.g., `myVar`)
- Constants: UPPERCASE (e.g., `MAX_VALUE`)

### Code Organization
- Group related definitions in modules
- Use sections for local scoping
- Keep files focused and manageable in size
- Document public interfaces

### Performance Considerations
- Use tail recursion when possible
- Prefer pattern matching over if-then-else
- Use type classes for polymorphic code
- Consider computational complexity

## Common Patterns

### Error Handling
```lean
def divide (x y : Nat) : Option Nat :=
  if y = 0 then none else some (x / y)
```

### Builder Pattern
```lean
structure Builder where
  field1? : Option String := none
  field2? : Option Nat := none

def build (b : Builder) : Option String :=
  match b.field1?, b.field2? with
  | some f1, some f2 => some s!"{f1}: {f2}"
  | _, _ => none
```

### Monadic Operations
```lean
def computeResult (x : Nat) : Option Nat := do
  let y ← if x > 0 then some x else none
  let z ← some (y * 2)
  return z + 1
```

****
[Debugging](./Lean.debugging.html)
