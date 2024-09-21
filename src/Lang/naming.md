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
  - [Identifiers](#identifiers)
  - [Other material](#other-material)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Naming conventions

## Files and modules

The namespace or package equivalent in Agda, called a module, appears at the beginning of every file:

```agda
module Lang.naming where
```

Filenames and module headers are required to match according to the following pattern: the supported filenames that can contain the module named `intro` are:

- [x] intro.agda
- [x] intro.lagda
- [x] intro.lagda.md
- [x] intro.ladga.rst
- [x] intro.ladga.tex

This file is written in markdown and hence we use the name `intro.lagda.md`.

## Literate programming

The last three file extensions above are part of what's called "literate programming" wherein one can write markdown or latex documents with agda code surrounded in code blocks marked agda, similar to how this page itself is written!

![codeblock](../artwork/codeblock.png)

The Agda compiler can then validate the agda code inside the `agda` code blocks, thus guaranteeing the correctness of the math in the documents.

## Identifiers

In Agda, naming conventions are not strictly enforced, but there are some common practices:

1. Types and data constructors: Start with a capital letter (e.g., `Nat`, `List`, `Vec`)
2. Functions and variables: Start with a lowercase letter (e.g., `add`, `map`, `x`)
3. Module names: Start with a capital letter (e.g., `Data.List`, `Relation.Binary`)
4. Unicode characters: Agda supports Unicode, so mathematical symbols are often used (e.g., `∀`, `λ`, `→`)
5. Mixfix operators: Can be defined using underscores (e.g., `_+_`, `if_then_else_`)

Remember that clarity and readability are key. Choose names that accurately describe the purpose or behavior of the identifier.

## Other material

There are a host of other high-quality materials on the web, though all of them might not be beginner-friendly. Here's an expanded list of resources:

1. [Agda's official documentation](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html): A comprehensive list of tutorials and courses.

2. [Programming Language Foundations in Agda](https://plfa.github.io/): An excellent introduction to programming language theory using Agda.

3. [Agda in a Hurry](https://ualib.org/agda-in-a-hurry.html): A quick introduction to Agda for those familiar with functional programming.

4. [Learn You an Agda](http://learnyouanagda.liamoc.net/): A beginner-friendly tutorial inspired by "Learn You a Haskell".

5. [Agda Tutorial](https://people.inf.elte.hu/divip/AgdaTutorial/Index.html): A comprehensive tutorial covering many Agda concepts.

6. [Verified Functional Programming in Agda](https://www.amazon.com/Verified-Functional-Programming-Agda-Books/dp/1970001240): A book by Aaron Stump that introduces Agda and its applications.

7. [Agda Cheatsheet](https://alhassy.github.io/AgdaCheatSheet/CheatSheet.html): A quick reference for Agda syntax and common operations.

8. [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html): A deep dive into Homotopy Type Theory using Agda.

9. [Software Foundations in Agda](https://plfa.github.io/): An adaptation of the famous Software Foundations series to Agda.

10. [Agda by Example](https://mazzo.li/posts/AgdaByExample.html): A collection of Agda examples for various programming concepts.

These resources cater to different levels of expertise and focus on various aspects of Agda and type theory. We flick some stuff from many of them and water them down for novices here.

****
[Data Structures](./Lang.dataStructures.html)
