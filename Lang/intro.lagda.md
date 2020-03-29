****
[Contents](contents.html)
[Previous](contents.html)
[Next](Lang.setup.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
****

- [A Personal Journey](#a-personal-journey)
- [Who is this for](#who-is-this-for)
- [Agda](#agda)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

```agda
module Lang.intro where
```

The following work aims to be a primer and motivator for functional programmers to peer into the world of pure mathematics. This work is created by a functional programmer who, while discovering and using libraries and constructs like [cats](https://typelevel.org/cats/), [scalaz](https://github.com/scalaz/scalaz), [lens](https://hackage.haskell.org/package/lens), [monads](https://wiki.haskell.org/All_About_Monads) and various other functional constructs built into languages such as [haskell](https://www.haskell.org/), [scala](https://www.scala-lang.org/), [clojure](https://clojure.org/), [rust](https://www.rust-lang.org/), [purescript](http://www.purescript.org/) and so on, ended up with interest about the math behind them.

# A Personal Journey

This work primarily stems from a personal journey of peering deeper into pure mathematics. The journey started in about 2014 partly as hatred toward the verbosity of java and as a curiosity into the functional programming paradigm made possible on the JVM through scala. Learning scala was soon followed by several PL treats such as [generics](https://en.wikipedia.org/wiki/Generic_programming), [parametric polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism) and the likes making my life easier. Being a data engineer at that time, twitter's work on designing metrics as monoids and the [Algebird](https://www.michael-noll.com/blog/2013/12/02/twitter-algebird-monoid-monad-for-large-scala-data-analytics/) project had a lasting impression on my own work. This led me to explore libraries implementing bits of category theory such as [shapeless](https://github.com/milessabin/shapeless), [cats](https://typelevel.org/cats/), [Algebird's hyperloglog monoid](https://twitter.github.io/algebird/datatypes/approx/hyperloglog.html), [scalaz](https://github.com/scalaz/scalaz) followed by several "for programmer" tutorials into category theory, notably the ones by [Bartosz Milewski](https://www.youtube.com/user/DrBartosz/playlists). Soon I had to learn haskell − it being more "pure" and having a stronger ecosystem of libraries with a more formal programming-language-theory flavor so as to have more things accessible to explore.

In tandem, I started a parallel hobby-type thing where I picked up a few books on the subjects of abstract algebra and category theory to get a theoretical understanding of the "whole thing":

- [x] Category Theory for Programmers ~ Milewski ([repo](https://github.com/hmemcpy/milewski-ctfp-pdf))
- [x] Abstract Algebra ~ Dummit & Foote ([link](https://www.goodreads.com/book/show/264543.Abstract_Algebra))
- [x] Topoi - The Categorical Analysis of Logic ~ Goldblatt ([link](https://projecteuclid.org/euclid.bia/1403013939))
- [x] Categories for the Working Mathematician ~ Mac Lane ([link](https://en.wikipedia.org/wiki/Categories_for_the_Working_Mathematician))
- [x] Algebra ~ Lang ([link](https://www.springer.com/gp/book/9780387953854))

After trudging through some parts of the above books and getting a "feel" and practice of the mathematics in them, specifically category theory in various contexts, I turned toward some PL-theory:

- [x] Practical Foundations for Programming Languages ~ Harper ([link](https://www.cs.cmu.edu/~rwh/pfpl/))
- [x] An Introduction to Functional Programming Through Lambda Calculus - Michaelson ([pdf](http://www.macs.hw.ac.uk/~greg/books/gjm.lambook88.ps))
- [x] Robert Harper's lectures on:
  - [x] [Type Theory](https://www.youtube.com/watch?v=ev7AYsLljxk&list=PLLHd8G9sGDBP5z0Vk_MpaccuOWGUgZknd)
  - [x] [Proof Theory](https://www.youtube.com/watch?v=YRu7Xi-mNK8&list=PLLHd8G9sGDBOe7mzE_uKvS5-il8ZAVBVr)
  - [x] [Category Theory](https://www.youtube.com/playlist?list=PLLHd8G9sGDBPF4-f2tmY_p5qWzZ1Vl1TA)

By 2018, I decided to converge some aspects of my programming job with the act of taking math notes. After I came to know of Agda's capability to compile code in markdown docs (being a huge proponent of markdown for documentation), I decided to learn agda and concurrently document and code my exploration path into a series of notes, which ended up being this work.

One fine day, I saw this new "foundations of mathematics" thing, which apparently "cool kids" were reading on twitter. On further searching followed by reading online, I ended up ordering 2 copies from different sources, one of them never got delivered:

- [x] Homotopy Type Theory ~ Univalent Foundations of Mathematics ([link](https://homotopytypetheory.org/book/))

It took me a few months to read and grasp what was going on in that book. After spending considerable amounts of time through various other notes, mathoverflow, nlab, arxiv, I ended up with the feeling that I knew nothing about geometry and in no way could grasp homotopy theory. I took some time off in 2019 as these notes grew in volume and it became increasingly difficult to code them. During that time off I decided to cover some ground in geometry:

- [x] An Introduction to Manifolds ~ Tu ([link](https://www.springer.com/gp/book/9781441973993))
- [x] A Comprehensive Introduction to Differential Geometry Volume I ~ Spivak ([link](https://www.goodreads.com/book/show/211192.A_Comprehensive_Introduction_to_Differential_Geometry_Vol_1))
- [x] A Concise Course in Algebraic Topology ~ May ([pdf](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf))

After going through these I finally was able to have at least a sketchy view of homotopy type theory, higher category theory and higher topos theory. As things started getting more cutting-edge, I've mostly ended up printing and reading through various parts of:

- [x] nLab ([link](https://ncatlab.org/nlab/show/HomePage))
- [x] Infinite Paper Napkin ([likn](https://web.evanchen.cc/napkin.html))
- [x] The Stacks Project ([link](https://stacks.math.columbia.edu/browse))

Of late, I stumbled upon this work on mathematical physics:

- [x] Gauge fields, knots, and gravity ~ Baez ([link](https://www.worldscientific.com/worldscibooks/10.1142/2324))
- [x] Susskind's lectures on:
  - [x] [Quantum Mechanics](https://www.youtube.com/playlist?list=PL701CD168D02FF56F)
  - [x] [String Theory & M Theory](https://www.youtube.com/playlist?list=PL202191442DB1B300)

opening the path to these shiny new thingys that await:

- [x] geometry of physics ([link](https://ncatlab.org/nlab/show/geometry+of+physics))
- [ ] Differential cohomology in a cohesive ∞-topos ~ Schreiber ([link](https://arxiv.org/pdf/1310.7930.pdf))
- [ ] Quantum Gauge Field Theory in Cohesive Homotopy Type Theory ~ Schreiber ([pdf](https://arxiv.org/pdf/1408.0054.pdf))

Meanwhile I try to play catchup with this work and sometimes re-do some parts as my understanding gets clearer and sometimes implement new stuff as and when I have time (and patience). The direction I've been following here is if I could implement real numbers, followed by manifolds and such, I perhaps could attempt to implement gauge theories or Supermanifolds albeit it would take me a few years at least. I also need to finish a lot of TODOs. 😛

It has been almost 4 years now, and the "whole thing" does not seem to have an end!

# Who is this for

This work is intended to be a resource for anyone (like me) making a foray into pure mathematics. The "like me" here implies someone who:

- [x] knows programming.
- [x] has worked with functional programming in some capacity.
- [x] has at least a sketchy idea of what "pure mathematics" means.
- [x] has boundless motivation to explore.

# Agda

![Agda's Logo](../artwork/logo.svg)

Agda is a dependently-typed functional programming language that can be used as a "proof assistant" of the "propositions-as-types" flavor, i.e. it is a language used to write mathematical proofs, using a typesystem, which its compiler then verifies to check if the proofs really do what they claim. This is done by using Type theory as the language for writing proofs in Agda. Traditionally, the act of checking the validity of a proof has been a manual and painstaking process, however, the proofs when represented in this `code ⇆ compiler` paradigm, does away with the need for manual checking, thus making things considerably easier to implement, test and distribute. There are other alternative theorem provers, each with their own feature-sets, strengths and weaknesses, [documented here](https://en.wikipedia.org/wiki/Proof_assistant#Comparison_of_systems).

Agda was originally developed by Ulf Norell at Chalmers University of Technology with implementation described in his [PhD thesis](http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf). The current version is a full rewrite, and should be considered a new language that shares a name and tradition.

****
[Setup](./Lang.setup.html)
