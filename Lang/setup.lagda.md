****
[Contents](contents.html)
[Previous](contents.html)
[Next](Lang.intro.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Agda](#agda)
- [Setup and installation](#setup-and-installation)
  - [1. Using Docker](#1-using-docker)
    - [Run](#run)
  - [2. Using Stack](#2-using-stack)
  - [3. Via package managers](#3-via-package-managers)
    - [apt (Debian, Ubuntu, Mint, Elementary, MX Linux etc)](#apt-debian-ubuntu-mint-elementary-mx-linux-etc)
    - [yum (Fedora, openSUSE, RHEL)](#yum-fedora-opensuse-rhel)
    - [pacman (Arch, Manjaro, Antergos)](#pacman-arch-manjaro-antergos)
    - [brew (OSX)](#brew-osx)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Agda

Agda is a dependently-typed functional programming language that functions as a "proof assistant", i.e. it is a language used to write mathematical proofs which its compiler then performs formal verification on to check if the proofs really do what they claim. This is done by using Type theory as the language for writing proofs in Agda. Traditionally, the act of checking the validity of a proof has been an extremely manual and painstaking process, however, the proofs when represented in this `code ⇆ compiler` paradigm, erases the need for manual intervention. There are more alternatives available to Agda, [documented here](https://en.wikipedia.org/wiki/Proof_assistant#Comparison_of_systems).

We begin with setting up our Agda environment.

# Setup and installation

```agda
module Lang.setup where
```

![Figure 1: Install](./install.png)

## 1. Using Docker

We've done most of the heavy-lifting, and packaged everything into a docker container. This is a platform-independent solution and can be run inside any major operating system. Though it is recommended to run all of the subsequent code.

Install docker

```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh
```

OR download and install docker binaries for your operating system [here](https://github.com/docker/engine/releases).

Pull the pre-configured docker image

```bash
docker pull ixaxaar/agda:latest
```

### Run

To run the agda compiler with docker:

- Launch the docker container while mounting the local source directory:

```bash
docker run -it -v /local/source/directory:/local/source/directory ixaxaar/agda bash
```

- Compile `whatever.agda`

```bash
agda ./whatever.agda
```


## 2. Using Stack

Stack is one of haskell's package manager. Install stack first, if not done already

```bash
curl -sSL https://get.haskellstack.org/ | sh
```

Clone [https://github.com/ixaxaar/monoid.space](https://github.com/ixaxaar/monoid.space) and `cd` into it. Proceed to use stack to install agda:

```bash
stack setup
stack build
```

## 3. Via package managers

Note: none of these are guaranteed to work as distro maintainers always seem to disagree with haskell subsystem's practices and rituals.

### apt (Debian, Ubuntu, Mint, Elementary, MX Linux etc)

```bash
sudo apt-get install agda-mode agda-stdlib
```

### yum (Fedora, openSUSE, RHEL)

```bash
sudo yum install Agda
```

### pacman (Arch, Manjaro, Antergos)

```bash
sudo pacman -S agda agda-stdlib
```

### brew (OSX)

```bash
brew install agda
```

Other ways to install Agda are documented [in the official documentation](https://agda.readthedocs.io/en/v2.5.4/getting-started/installation.html).

That's pretty much it. Now we go ahead and learn some basics of the language.

****
[Introduction](./Lang.languageIntro.html)
