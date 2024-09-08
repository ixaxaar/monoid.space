<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Setup and Installation](#setup-and-installation)
  - [1. Using Docker](#1-using-docker)
  - [2. Using Stack](#2-using-stack)
  - [3. Via Package Managers](#3-via-package-managers)
    - [apt (Debian, Ubuntu, Mint, etc.)](#apt-debian-ubuntu-mint-etc)
    - [yum (Fedora, openSUSE, RHEL)](#yum-fedora-opensuse-rhel)
    - [pacman (Arch, Manjaro, Antergos)](#pacman-arch-manjaro-antergos)
    - [brew (OSX)](#brew-osx)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

****
[Contents](contents.html)
[Previous](Lang.intro.html)
[Next](Lang.naming.html)

- [Setup and Installation](#setup-and-installation)
  - [1. Using Docker](#1-using-docker)
  - [2. Using Stack](#2-using-stack)
  - [3. Via Package Managers](#3-via-package-managers)
    - [apt (Debian, Ubuntu, Mint, etc.)](#apt-debian-ubuntu-mint-etc)
    - [yum (Fedora, openSUSE, RHEL)](#yum-fedora-opensuse-rhel)
    - [pacman (Arch, Manjaro, Antergos)](#pacman-arch-manjaro-antergos)
    - [brew (OSX)](#brew-osx)

# Setup and Installation

## 1. Using Docker

1. Install Docker: `curl -fsSL https://get.docker.com -o get-docker.sh && sh get-docker.sh` or download [here](https://github.com/docker/engine/releases).
2. Pull the image: `docker pull ixaxaar/agda:latest`
3. Run: `docker run -it -v /local/source/directory:/directory/inside/container ixaxaar/agda bash`
4. Compile: `agda /directory/inside/container/whatever.agda`

## 2. Using Stack

1. Install Stack: `curl -sSL https://get.haskellstack.org/ | sh`
2. Clone [repo](https://github.com/ixaxaar/monoid.space), `cd` into it, and install Agda:
```bash
stack --resolver=lts-13.25 install Agda-2.6.0.1 EdisonCore-1.3.2.1 data-hash-0.2.0.1 equivalence-0.3.4 geniplate-mirror-0.7.6 EdisonAPI-1.3.1 STMonadTrans-0.4.3
```

## 3. Via Package Managers

*Note: success not guaranteed.*

### apt (Debian, Ubuntu, Mint, etc.)
`sudo apt-get install agda-mode agda-stdlib`

### yum (Fedora, openSUSE, RHEL)
`sudo yum install Agda`

### pacman (Arch, Manjaro, Antergos)
`sudo pacman -S agda agda-stdlib`

### brew (OSX)
`brew install agda`

More installation methods [here](https://agda.readthedocs.io/en/v2.5.4/getting-started/installation.html).

****
[Naming Conventions](./Lang.naming.html)
