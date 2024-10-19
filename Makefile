
SHELL := /bin/bash

default: all

watch:
	@npx nodemon -e md --signal SIGKILL --exec ./compile.sh

clean:
	rm -rf html
	mkdir html
	find -name "*.agdai" | xargs rm -rf

all: clean
	@sh -c "zsh ./compile.sh"
	find -name "*.agdai" | xargs rm -rf
