****
[Contents](contents.html)
[Previous](Lang.intro.html)
[Next](Lang.naming.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

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

# Setup and installation

```agda
module Lang.setup where
```

## 1. Using Docker

We've done most of the heavy-lifting, and packaged everything into a docker container. This is a platform-independent solution and can be run inside any major operating system. But first we would need to:

1. Install docker

```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh
```

OR download and install docker binaries for your operating system [here](https://github.com/docker/engine/releases).

2. Pull the pre-configured docker image

```bash
docker pull ixaxaar/agda:latest
```

### Run

To run the agda compiler with docker:

- Launch the docker container while mounting the local source directory:

```bash
docker run -it -v /local/source/directory:/directory/inside/container ixaxaar/agda bash
```

- Compile `whatever.agda`

```bash
agda /directory/inside/container/whatever.agda
```

## 2. Using Stack

[Stack](https://www.haskellstack.org/) is one of haskell's package managers, apart from [Cabal](https://www.haskell.org/cabal/). Stack uses cabal internally and is easier to practically deal with. In order to do a stack-based install:

1. Install Stack:

```bash
curl -sSL https://get.haskellstack.org/ | sh
```

2. Clone [https://github.com/ixaxaar/monoid.space](https://github.com/ixaxaar/monoid.space) and `cd` into it. Proceed to use stack to install agda:

```bash
stack setup
stack build
```

## 3. Via package managers

Note: none of these are guaranteed to work. This way of installation might just work, or might require one to pull significant amounts of one's own hair.

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
[Naming Conventions](./Lang.naming.html)
