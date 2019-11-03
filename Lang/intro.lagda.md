****
[Contents](contents.html)
[Previous](Lang.setup.html)
[Next](Lang.dataStructures.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Naming conventions](#naming-conventions)
  - [Files and modules](#files-and-modules)
  - [Literate programming](#literate-programming)
  - [Other material](#other-material)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Naming conventions

## Files and modules

A namespace in Agda, called a module, appears at the beginning of every file:

```agda
module Lang.intro where
```

Filenames and module headers are required to match. The supported filenames that can contain the module `intro` being:

- [x] intro.agda
- [x] intro.lagda
- [x] intro.lagda.md
- [x] intro.ladga.rst
- [x] intro.ladga.tex

This file is written in markdown and hence we use the name `intro.lagda.md`.

## Literate programming

The last three file extensions above are part of what's called "literate programming" wherein one can write markdown or latex documents with agda code surrounded in code blocks marked agda, similar to how this page itself is written!

![codeblock](./codeblock.png)

The Agda compiler can then validate the agda code inside the `agda` code blocks, thus guaranteeing the correctness of the math in the documents.

## Other material

There are a host of other high quality material on the web, though all of them might not be beginner friendly. They are listed in [Agda's official documentation](https://my-agda.readthedocs.io/en/latest/getting-started/tutorial-list.html). We flick some stuff from many of them and water them down for novices here.

****
[Data Structures](./Lang.dataStructures.html)
