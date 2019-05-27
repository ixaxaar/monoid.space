****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Setup and installation](#setup-and-installation)
  - [Using Docker](#using-docker)
  - [Stack](#stack)
  - [Via package managers](#via-package-managers)
    - [apt (Debian, Ubuntu, Mint, Elementary, MX Linux etc)](#apt-debian-ubuntu-mint-elementary-mx-linux-etc)
    - [yum (Fedora, openSUSE, RHEL)](#yum-fedora-opensuse-rhel)
    - [pacman (Arch, Manjaro, Antergos)](#pacman-arch-manjaro-antergos)
    - [brew (OSX)](#brew-osx)
- [Run](#run)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

We begin with setting up our Agda environment.

# Setup and installation

```agda
module Lang.setup where
```

![install](./install.png)

## Using Docker

We've done most of the heavy-lifting, and packaged everything into a docker container. This is a platform-independent solution and can be run inside any major operating system. Though it is recommended to run all of the subsequent code in a [Linux-based OS](https://www.wikihow.com/Use-Linux) as the author disregards "windouz™" enough to not even consider googling for installation instructions to put them here.

Install docker

```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh
```

Pull the pre-configured docker image

```bash
docker pull ixaxaar/agda:latest
```

## Stack

Stack is one of haskell's package manager. Install stack first, if not done already

```bash
curl -sSL https://get.haskellstack.org/ | sh
```

Proceed to use stack to install agda

```bash
stack install cabal-install
stack install happy
stack --resolver lts-12.0 --install-ghc install Agda
```

## Via package managers

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

# Run

To run the agda compiler:

- Launch the docker container's bash:

```bash
docker run -it -v /local/source/directory:/local/source/directory ixaxaar/agda bash
```

- Compile `whatever.agda`

```bash
agda ./whatever.agda
```

That's pretty much it. Now we go ahead and learn some basics of the language.

****
[Introduction](./Lang.languageIntro.html)
