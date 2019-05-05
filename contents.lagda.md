<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [Contents](#contents)
  - [1. Agda](#1-agda)
  - [2. Type Theory](#2-type-theory)
  - [3. Logic](#3-logic)
  - [4. Homotopy Type Theory](#4-homotopy-type-theory)
  - [5. Abstract Algebras](#5-abstract-algebras)
  - [7. Category Theory](#7-category-theory)
  - [8. Algebraic Topology](#8-algebraic-topology)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# Contents

## 1. Agda

![1](1.png)

  - [Setup](./Lang.setup.html)
  - [Introduction](./Lang.languageIntro.html)
  - [Data Structures](./Lang.dataStructures.html)
  - [Proofs as Data](./Lang.proofsAsData.html)
  - [Functions](./Lang.functions.html)
  - [Quirks of Syntax](./Lang.syntaxQuirks.html)
  - [Modules, Records and Postulates](./Lang.other.html)
  - [Debugging](./Lang.debugging.html)

## 2. Type Theory

![2](2.png)

  - [Introduction](./Types.introduction.html)
  - [Universes and families](./Types.universe.html)
  - [Relations](./Types.relations.html)
  - [Equality](./Types.equality.html)
  - [Product Types / Σ-types](./Types.typeBasics.html)
  - [Dependent Function Types / Π-types](./Types.functions.html)

## 3. Logic

![3](3.png)

  - [Introduction](./Logic.introduction.html)
  - [Boolean Algebra](./Logic.logicBasics.html)
  - [Equality](./Logic.equality.html)
  - [Laws of Logic](./Logic.laws.html)
  <!-- - [Decidability](./Logic.decidability.html) -->

## 4. Homotopy Type Theory

  - [Introduction](./HoTT.introduction.html)
  - [Identity Types](./HoTT.identity.html)

## 5. Abstract Algebras

![4](4.png)

  - [Introduction](./Algebra.introduction.html)
  - [Operations](./Algebra.operations.html)
  - [Equational Reasoning](./Algebra.equational.html)
  <!-- - [Ordered objects](./Algebra.order.html) -->
  <!-- - [Properties of ordered objects](./Algebra.orderProperties.html) -->
  - [Groups and family](./Algebra.groups.html)
  - [Groups and family 2](./Algebra.structures.html)
  - [Properties of Group-like objects](./Algebra.groupProperties.html)
  <!-- - [Rings and family](./Algebra.rings.html) -->
  <!-- - [Properties of Ring-like objects](./Algebra.ringProperties.html) -->

## 7. Category Theory

![6](6.png)

  - [Natural Transformations]
  - [Hom-Sets and constructions]
  - [The Yoneda Lemma]
  - [Limits and Co-Limits]
  - [Adjunctions]
  - [Kan Extensions]

## 8. Algebraic Topology

![5](5.png)

  - [Paths and connected spaces]
  - [The Fundamental Group and Groupoid]
  - [Functor]
  - [The Seifert - van-Kampen theorem]


<!--
## 7. The Curry-Howard-Lambek-Voevodsky isomorphism

![7](7.png)

## 8. The Equivalence principle

![8](8.png)

## 9. Homotopy Type Theory

![9](9.png) -->

Code: [Github](https://github.com/ixaxaar/monoid.space), [Gitlab](https://gitlab.com/ixaxaar/with_agda).

```agda
import Lang.setup
import Lang.languageIntro
import Lang.dataStructures
import Lang.proofsAsData
import Lang.functions
import Lang.syntaxQuirks
import Lang.other
import Lang.debugging

import Types.introduction
import Types.universe
import Types.relations
import Types.equality
import Types.typeBasics
import Types.functions

import HoTT.identity

import Logic.introduction
import Logic.logicBasics
import Logic.equality
import Logic.laws

import Algebra.introduction
import Algebra.operations
import Algebra.equational
import Algebra.order
import Algebra.groups
import Algebra.structures
import Algebra.groupProperties
```

****
