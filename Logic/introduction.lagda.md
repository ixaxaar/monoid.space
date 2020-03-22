****
[Contents](contents.html)
[Previous](AppliedTypes.bindings.html)
[Next](Logic.logicBasics.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Introduction](#introduction)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Introduction

```agda
module Logic.introduction where
```

Boolean algebra is a branch of mathematics dealing with formalized logic, and is closest to the programmer's daily toolbox than any other branch of mathematics. Our computing infrastructure is built around binary values, and hence, computing systems are essentially compound machines consisting of simpler units that perform logical operations, think digital gates and circuits. In fact, the invention of logic gates that essentially ushered this new era of computing that we assume the reader to be familiar with.

We try to formally state the system of Logic and its mathematical machinery, consisting of various relations, transformations and laws using the language of Type Theory represented by Agda. We begin with the basics of logic - its objects and operations on those objects, then move on to constructively proving the laws of Boolean algebra. We end with a foray into what it means to be "decidable".

****
[Boolean Algebra](./Logic.logicBasics.html)
