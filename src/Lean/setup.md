---

[Contents](contents.html)
[Previous](Lean.intro.html)
[Next](Lean.naming.html)

# Lean Installation

[Lean](https://leanprover.github.io/) is a powerful theorem prover and programming language. This guide provides various methods to install Lean on your system.

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

## 1. Using Docker

Docker is the modern way to run applications in isolated environments. Using Docker for Lean ensures you have a consistent setup across different systems without worrying about "it works on my machine" issues.

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
   docker run -it -v /path/to/your/local/directory:/lean leanprover/lean:latest
   ```

4. Inside the container, you can now use Lean:

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

1. Ensure you have CMake and GCC installed.

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

1. Create a new directory for your project and navigate into it:

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

## Libraries and dependencies

Lean 4 uses `lake` as both a build system and package manager. Libraries are managed through dependencies in your project configuration.

### Adding dependencies

Dependencies must be added manually by editing your `lakefile.toml` file:

1. **Add to lakefile.toml**: Edit your project's `lakefile.toml` to include the dependency:

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

For local development, you can reference libraries using relative paths in your `lakefile.toml`:

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
authors = ["Your Name <email@example.com>"]
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

---

[Naming Conventions](./Lean.naming.html)
