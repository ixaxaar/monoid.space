****
[Contents](contents.html)
[Previous](Lang.intro.html)
[Next](Lang.naming.html)

- [Setup and Installation](#setup-and-installation)
   - [1. Using Docker](#1-using-docker)
   - [2. Using GHCup](#2-using-ghcup)
   - [3. Via Package Managers](#3-via-package-managers)
      - [Homebrew (macOS and Linux)](#homebrew-macos-and-linux)
      - [apt (Debian, Ubuntu, Mint, etc.)](#apt-debian-ubuntu-mint-etc)
      - [pacman (Arch, Manjaro)](#pacman-arch-manjaro)
      - [Nix (NixOS and other systems)](#nix-nixos-and-other-systems)
   - [4. Building from Source](#4-building-from-source)
   - [Additional Setup](#additional-setup)

# Setup and Installation

## 1. Using Docker

Docker provides a consistent environment across different platforms, making it an excellent choice for Agda development.

1. Install Docker:
   - On Linux:
     ```bash
     curl -fsSL https://get.docker.com -o get-docker.sh && sh get-docker.sh
     ```
   - On macOS and Windows: Download and install Docker Desktop from the [official Docker website](https://www.docker.com/products/docker-desktop)

2. Pull the latest Agda image:
   ```bash
   docker pull agda/agda:latest
   ```

3. Run the Docker container:
   ```bash
   docker run -it -v /path/to/your/local/directory:/agda agda/agda:latest
   ```

4. Inside the container, you can now use Agda:
   ```bash
   agda --version
   ```

## 2. Using GHCup

GHCup is a versatile installer for Haskell toolchains, including Agda.

1. Install GHCup:
   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
   ```

2. Install Agda using GHCup:
   ```bash
   ghcup install agda
   ghcup set agda latest
   ```

3. Verify the installation:
   ```bash
   agda --version
   ```

## 3. Via Package Managers

### Homebrew (macOS and Linux)
```bash
brew install agda
```

### apt (Debian, Ubuntu, Mint, etc.)
```bash
sudo apt update
sudo apt install agda agda-mode
```

### pacman (Arch, Manjaro)
```bash
sudo pacman -S agda agda-stdlib
```

### Nix (NixOS and other systems)
```bash
nix-env -i agda
```

## 4. Building from Source

For the latest development version or specific customizations:

1. Ensure you have GHC (Glasgow Haskell Compiler) and Cabal installed.

2. Clone the Agda repository:
   ```bash
   git clone https://github.com/agda/agda.git
   cd agda
   ```

3. Build and install:
   ```bash
   cabal update
   cabal install --only-dependencies
   cabal install
   ```

## Additional Setup

1. Agda Standard Library:
   ```bash
   git clone https://github.com/agda/agda-stdlib.git
   cd agda-stdlib
   cabal install
   ```

2. Editor Integration:
   - For Emacs: Install agda2-mode
   - For VS Code: Install the "agda-mode" extension
   - For Vim: Use agda-vim

Remember to configure your `~/.agda/libraries` file to point to your Agda standard library installation.

For the most up-to-date information, always refer to the [official Agda documentation](https://agda.readthedocs.io/en/latest/getting-started/installation.html).

****
[Naming Conventions](./Lang.naming.html)
