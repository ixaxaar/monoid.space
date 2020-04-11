
SHELL := /bin/bash

default: all

watch:
	@sh -c 'cd src && npx nodemon -e md --signal SIGKILL --exec "agda ./contents.lagda.md || exit 1"'

clean:
	rm -rf html
	mkdir html
	find -name "*.agdai" | xargs rm -rf

all: clean
	@sh -c "zsh ./compile.sh"
	find -name "*.agdai" | xargs rm -rf
