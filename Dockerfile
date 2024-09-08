# Use the official Haskell image as a base
FROM haskell:9.4

# Set environment variables
ENV LANG C.UTF-8

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    libtinfo5 \
    libicu-dev \
    zlib1g-dev && rm -rf /var/lib/apt/lists/*

# Install Agda
RUN cabal update && cabal install Agda

# Install Agda standard library
RUN git clone https://github.com/agda/agda-stdlib.git /opt/agda-stdlib && cd /opt/agda-stdlib && cabal install

# Set up Agda libraries
RUN mkdir -p ~/.agda && echo "/opt/agda-stdlib/standard-library.agda-lib" >~/.agda/libraries && echo "standard-library" >~/.agda/defaults

# Set working directory
WORKDIR /agda

# Command to run when starting the container
CMD ["bash"]
