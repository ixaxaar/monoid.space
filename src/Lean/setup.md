---

[Contents](contents.html)
[Previous](Lean.intro.html)
[Next](Lean.naming.html)

# Lean Installation

[Lean](https://leanprover.github.io/) is a powerful theorem prover and programming language. This guide provides various methods to install Lean on a system.

---

- [1. Using Docker](#1-using-docker)
- [2. Using elan (Lean Version Manager)](#2-using-elan-lean-version-manager)
- [3. Via Package Managers](#3-via-package-managers)
  - [Homebrew (macOS and Linux)](#homebrew-macos-and-linux)
  - [yay (Arch, Manjaro)](#yay-arch-manjaro)
  - [Nix (NixOS and other systems)](#nix-nixos-and-other-systems)
- [4. Building from Source](#4-building-from-source)
- [Project setup](#project-setup)
- [Libraries and dependencies](#libraries-and-dependencies)
- [Development Environment](#development-environment)
  - [VSCode Integration](#vscode-integration)
  - [Testing](#testing)
- [Documentation](#documentation)

## 1. Using Docker

Docker is the modern way to run applications in isolated environments. Using Docker for Lean ensures a consistent setup across different systems without worrying about "it works on my machine" issues.

1. Install Docker:

   - On Linux:

     ```bash
     curl -fsSL https://get.docker.com -o get-docker.sh && sh get-docker.sh
     ```

   - On macOS and Windows: Download and install Docker Desktop from the [official Docker website](https://www.docker.com/products/docker-desktop)

2. Pull the latest Lean image:

   ```bash
   docker pull leanprover/lean:latest
   ```

3. Run the Docker container:

   ```bash
   docker run -it -v /path/to/local/directory:/lean leanprover/lean:latest
   ```

4. Inside the container, Lean can now be used:

   ```bash
   lean --version
   ```

## 2. Using elan (Lean Version Manager)

elan is the recommended tool for installing and managing Lean versions.

1. Install elan:

   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Install the latest stable version of Lean:

   ```bash
   elan default stable
   ```

3. Verify the installation:

   ```bash
   lean --version
   ```

## 3. Via Package Managers

### Homebrew (macOS and Linux)

```bash
brew install lean
```

### yay (Arch, Manjaro)

```bash
yay -S lean4-bin
```

### Nix (NixOS and other systems)

```bash
nix-env -i lean
```

## 4. Building from Source

For the latest development version or specific customizations:

1. Ensure CMake and GCC are installed.

2. Clone the Lean repository:

   ```bash
   git clone https://github.com/leanprover/lean4.git
   cd lean4
   ```

3. Build and install:

   ```bash
   mkdir build && cd build
   cmake ..
   make
   ```

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

## Development Environment

### VSCode Integration

VSCode is the primary IDE for Lean development. The Lean extension provides a complete set of features required for end to end development in Lean. Other editor integrations are available such as `lean-mode` for Emacs and `lean.vim` for Vim. However, the VSCode extension is the most feature-rich and actively maintained.

### Testing

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

## Documentation

Lean supports documentation strings using `/-! ... -/` for modules and `/-- ... -/` for definitions:

```lean
/-!
# Basic Arithmetic Module
This module provides basic arithmetic operations.
-/

/--
`add` performs addition on natural numbers.
-/
#eval add 2 3  -- returns 5
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
rev = "main"
```

3. Run `lake update doc-gen4` within `docbuild` to pin `doc-gen4` and its dependencies to the chosen versions.
4. If the parent project has dependencies, they can be updated for building the documentation by running `lake update MyProject` in the `docbuild` directory.

---

[Naming Conventions](./Lean.naming.html)
