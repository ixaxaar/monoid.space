****
[Contents](contents.html)
[Previous](Lang.intro.html)
[Next](Lang.naming.html)

# Lean Installation

****
- [Lean Installation](#lean-installation)
   - [1. Using Docker](#1-using-docker)
   - [2. Using elan (Lean Version Manager)](#2-using-elan-lean-version-manager)
   - [3. Via Package Managers](#3-via-package-managers)
      - [Homebrew (macOS and Linux)](#homebrew-macos-and-linux)
      - [apt (Debian, Ubuntu, Mint, etc.)](#apt-debian-ubuntu-mint-etc)
      - [yay (Arch, Manjaro)](#yay-arch-manjaro)
      - [Nix (NixOS and other systems)](#nix-nixos-and-other-systems)
   - [4. Building from Source](#4-building-from-source)
   - [Additional Setup](#additional-setup)

## 1. Using Docker

Docker provides a consistent environment across different platforms, making it an excellent choice for Lean development.

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

### apt (Debian, Ubuntu, Mint, etc.)
Lean is not available in the default repositories. Use elan or Docker instead.

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

## Additional Setup

1. Lean Standard Library:
   The standard library is included with Lean installations. To use it in your project, add this to your `leanpkg.toml`:
   ```toml
   [dependencies]
   std = {git = "https://github.com/leanprover/std4.git"}
   ```

2. Editor Integration:
   - For VS Code: Install the "lean4" extension
   - For Emacs: Use lean-mode
   - For Vim: Use lean.vim

For the most up-to-date information, always refer to the [official Lean documentation](https://leanprover.github.io/lean4/doc/).
****
[Naming Conventions](./Lang.naming.html)
