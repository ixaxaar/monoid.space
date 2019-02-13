
# Introduction

## Code as propositions and theorems

In this, well whatever this turns out to be, we will try to take a look at various pure math disciplines while learning a new language for representing math. Agda, this "new langauge", is not quite new, given that it appeared first around 2007. It behaves as a proof assistant, as in it can prove the correctness of the written math represented as functional code, provided the code is correct of course. Hence, one can write math as functional code which can be automatically proof-checked by the compiler. This functional code is nothing but "Type Theory" in mathematics. We use this new language to "implement" various areas of algebra. We provide a complete example of implementing an area of math so as to suggest a strategy. This document is targetted towards coders primarily and assumes no prior knowledge of mathematics. Though, it assumes familiarity with coding, especially some minimal functional programming. Though it can be used by budding mathematicians as a tool to learn both a programming language and math.

## Structure of this document

This is basically what the order of the material presented here looks like:

- We will start with some basics of Agda, how to setup, and get up and running.
- First we learn Type Theory with examples in Agda. We go deeper in Agda as we explain more math to go along.
- Second, we dive into Category and look at how we can apply type theory to implement it
- Third, we then implement the equivalence principle and Homotopy Type Theory (HoTT) in Agda
- Finally, we construct an exapmple by writing algebraic geometry using the tools we developed in previous sections!

[Contents](./contents.lagda.md)
