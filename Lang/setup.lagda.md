
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
