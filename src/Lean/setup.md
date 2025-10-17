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

elan can also be used to manage multiple versions of Lean:

```bash
elan install <version>  # Install a specific version of Lean
elan default <version>  # Set the default version of Lean
elan list               # List installed Lean versions
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

[Projects & Structure](./Lean.projects.html)
