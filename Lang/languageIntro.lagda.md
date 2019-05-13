****
[Contents](contents.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Language Introduction](#language-introduction)
  - [Module headers](#module-headers)
- [Literate programming](#literate-programming)
- [Emacs](#emacs)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Language Introduction

Here we provide some introduction to Agda and its functional style. Those familiar with haskell can brush quickly through this section pretty fast as it is still a programmer's territory.

## Module headers

A namespace in Agda, called a module, appears at the beginning of every file:

```agda
module Lang.languageIntro where
```

Filenames and module headers are required to match. The supported filenames that can contain the module `languageIntro` being:

[x] languageIntro.agda
[x] languageIntro.lagda
[x] languageIntro.lagda.md
[x] languageIntro.ladga.rst
[x] languageIntro.ladga.tex

# Literate programming

The last three file extensions above are part of what's called "literate programming" wherein one can write markdown or latex documents with agda code surrounded in code blocks marked agda, similar to how this page is itself written!


>     `` agda
>     -- agda code goes here
>     ``

The Agda compiler can then validate the agda code inside the ` agda ` code blocks, thus guaranteeing the correctness of the math in the documents.

# Emacs

Though Agda is integrated with emacs and similar behavior with [Atom](https://atom.io/packages/agda-mode). Agda emacs symbols is documented [here](https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html). This document does not really assume familiarity with Emacs, and neither do we use it in favor of the command-line compiler.

****
[Data Structures](./Lang.dataStructures.html)
