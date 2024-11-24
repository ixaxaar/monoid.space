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
  - [Lake Package Manager](#lake-package-manager)
  - [vscode / vscodium Integration](#vscode--vscodium-integration)
  - [elan](#elan)
  - [doc-gen4](#doc-gen4)
  - [Testing](#testing)

## Basics

Lean files typically end with a `.lean` extension, and each file represents a module. The name of the file implicitly determines the name of the module, and this module can be imported by other modules.

- Each Lean file (.lean) defines a module, and the name of the file without the extension is the name of the module. For example, a file named group_theory.lean will define a module called group_theory.
- Files are organized into folders, and folder names are used as prefixes for module names. For instance, a file located at src/algebra/group.lean would define a module named algebra.group.
- Modules can also be explicitly defined using the `module` keyword. This is useful when you want to define a module with a different name than the file name:

```lean
-- In src/algebra/group.lean
module my_group

-- code here
```

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

This is great to start a new project or experiment with Lean code. However, for larger projects, it is recommended to use a more structured approach with multiple files and modules, as we shall see below.

## Projects

In larger Lean projects, you will typically have multiple files organized into modules and directories. Lean projects can be managed using the Lake package manager, which helps with building, testing, and managing dependencies.

The Lake package manager can be used to create a new Lean project with the `lake new` command:

```bash
lake new my_project
```

This creates a new directory called `my_project` that contains the following files:

- `lakefile.toml`: The configuration file for the project.
- `lean-toolchain`: Specifies the Lean version.
- `Main.lean`: The main entry point for the project.
- `MyProject.lean` and `MyProject/Basic.lean`: scaffolding of a support library for the project.

In addition to this, it also creates a git repo for the project and a `.gitingore` file.

### File Structure

In Lean, projects typically follow a standard directory structure:

```
my_project/
├── lakefile.toml    # Project configuration file
├── lean-toolchain  # Specifies Lean version
├── Main.lean       # Main entry point
└── src/            # Source files
    ├── Basic/      # Basic definitions
    ├── Logic/      # Logic-related modules
    └── Utils/      # Utility functions
```

Directories under `src/` can be customized based on the project's needs. Each directory can contain multiple `.lean` files, each defining a module. The `Main.lean` file serves as the entry point for the project.

## Lake Package Manager

Lake is Lean's built-in package manager and build system for lean. It simplifies the process of building, testing, and managing Lean projects. Lake uses `lakefile.toml` for configuration:

```toml
name = "my_project"
version = "0.1.0"
defaultTargets = ["my_project"]

[[lean_lib]]
name = "MyProject"

[[lean_exe]]
name = "MyProject"
root = "Main"

[[dependencies]]
name = "mathlib"
version = "3.0.0"
```

Here are some key points about the configuration:

- `name`: The name of the project.
- `version`: The version of the project.
- `defaultTargets`: The default targets to build when running `lake build`.
- `[[lean_lib]]`: Defines a Lean library target.
- `[[lean_exe]]`: Defines a Lean executable target.
- `root`: The entry point for the executable.
- `[[dependencies]]`: Specifies dependencies for the project, such as mathlib.

There are several more options available for configuring the project in the `lakefile.toml` and can be found in the [Lake documentation](https://github.com/leanprover/lean4/blob/master/src/lake/README.md).

Common Lake commands:
```bash
lake build       # Build the project
lake exe         # Build and run executables
lake clean       # Clean build artifacts
```

## vscode / vscodium Integration

VSCode is the primary IDE for Lean development. The Lean extension provides several features like any modern development environment such as syntax highlighting, real-time type information, interactive theorem proving, go to definition, auto-completion, and an infoview that shows real-time type information, proof state, error messages, and documentation.

Other editor integrations are available such as `lean-mode` for Emacs and `lean.vim` for Vim. However, the VSCode extension is the most feature-rich and actively maintained.

## elan

`elan` is a tool for managing Lean installations. It allows you to install and manage multiple versions of Lean on your system. You can install elan using the following command:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Once installed, you can use elan to install the latest stable version of Lean:

```bash
elan default stable
```

You can also use elan to switch between different versions of Lean and manage your Lean environment.

```bash
elan install <version>  # Install a specific version of Lean
elan default <version>  # Set the default version of Lean
elan list               # List installed Lean versions
```

## doc-gen4

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

Lean also supports markdown-style comments for documentation:

```lean
/- Markdown-style comment
# Heading
This is a paragraph.
-/
```

Documentation strings can be accessed using the `#print` command:

```lean
#print add
```

[`doc-gen4`](https://github.com/leanprover/doc-gen4) is a tool that generates documentation for Lean projects and comes bundled with the Lean installation. Its setup includes creating a nested project for documentation building inside the lake project.

1. Create a directory called `docbuild` inside the project.
2. Create a `lakefile.toml` file inside the `docbuild` directory:

```toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "MyProject"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
# Use revision v4.x if you are developing against a stable Lean version.
rev = "main"
```

3. Run `lake update doc-gen4` within `docbuild` to pin `doc-gen4` and its dependencies to the chosen versions.
4. If the parent project has dependencies, they can be updated for building the documentation by running `lake update MyProject` in the `docbuild` directory.

## Testing

Lean supports unit testing through its `test` command:

```lean
def double (x : Nat) : Nat := x * 2

#test double 2 = 4        -- Basic test
#test double 0 = 0        -- Edge case
```

Tests can be run using the `lean --test` command:

```bash
lean --test my_file.lean
```

****

[Debugging](./Lean.debugging.html)
