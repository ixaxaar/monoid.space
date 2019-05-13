****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Setup and installation](#setup-and-installation)
  - [Using Docker](#using-docker)
  - [Via package managers](#via-package-managers)
    - [apt (Debian, Ubuntu, Mint, Elementary, MX Linux etc)](#apt-debian-ubuntu-mint-elementary-mx-linux-etc)
    - [yum (Fedora, openSUSE, RHEL)](#yum-fedora-opensuse-rhel)
    - [pacman (Arch, Manjaro, Antergos)](#pacman-arch-manjaro-antergos)
    - [brew (OSX)](#brew-osx)
    - [Cabal (OS-independent)](#cabal-os-independent)
- [Run the proofn checker / compiler](#run-the-proofn-checker--compiler)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Setup and installation

```agda
module Lang.setup where
```

## Using Docker

We've done most of the heavy-lifting, and packaged everything into a docker container.

Install docker

```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh
```

Pull the pre-configured docker image

```bash
docker pull ixaxaar/agda:latest
```

## Via package managers

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


### Cabal (OS-independent)

```bash
cabal new-install Agda
```

Windows users may look at [this blog](https://medium.com/@danidiaz/installing-agda-2-5-4-1-on-windows-10-7bf296f3e5bc) to install Agda.


# Run the proofn checker / compiler

To run the agda compiler:

- Launch the docker container's bash:

```bash
docker run -it -v /local/source/directory:/local/source/directory ixaxaar/agda bash
```

- Compile `whatever.agda`

```bash
agda ./whatever.agda
```

That's pretty much it :grimacing:

****
[Introduction](./Lang.languageIntro.html)
