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

# A Personal Journey

This work primarily stems from a personal journey of peering deeper into pure mathematics. The journey started as a curiosity into the functional programming paradigm, initially involving learning scala and basic PL theory such as [generics](https://en.wikipedia.org/wiki/Generic_programming), [parametric polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism) and the likes. Being a data engineer at that time, twitter's work on designing metrics as monoids culminating in [Algebird](https://www.michael-noll.com/blog/2013/12/02/twitter-algebird-monoid-monad-for-large-scala-data-analytics/) was something that had a lasting impression on my own work. This led me to explore libraries implementing bits of category theory such as [shapeless](https://github.com/milessabin/shapeless) [cats](https://typelevel.org/cats/), [Algebird's hyperloglog monoid](https://twitter.github.io/algebird/datatypes/approx/hyperloglog.html), [scalaz](https://github.com/scalaz/scalaz) followed by several "for programmer" tutorials into category theory, notably the ones by [Bartosz Milewski](https://www.youtube.com/user/DrBartosz/playlists).Soon I had to learn haskell − it being more "pure" and having a stronger ecosystem of libraries with a more formal programming-language-theory flavor so as to have more things in this space to explore.

In tandem, I picked up a few books on the subjects of abstract algebra and category theory to get a theoretical understanding of the "whole thing":

- [x] Category Theory for Programmers ~ Milewski ([repo](https://github.com/hmemcpy/milewski-ctfp-pdf))
- [x] Abstract Algebra ~ Dummit & Foote ([link](https://www.goodreads.com/book/show/264543.Abstract_Algebra))
- [x] Topoi - The Categorical Analysis of Logic ~ Goldblatt ([link](https://projecteuclid.org/euclid.bia/1403013939))
- [x] Categories for the Working Mathematician ~ Mac Lane ([link](https://en.wikipedia.org/wiki/Categories_for_the_Working_Mathematician))
- [x] Algebra ~ Lang ([link](https://www.springer.com/gp/book/9780387953854))

After that I turned toward some PL-theory:

- [x] Practical Foundations for Programming Languages ~ Harper ([link](https://www.cs.cmu.edu/~rwh/pfpl/))
- [x] An Introduction to Functional Programming Through Lambda Calculus - Michaelson ([pdf](http://www.macs.hw.ac.uk/~greg/books/gjm.lambook88.ps))

Followed by some "time off" into other areas of math:

- [x] An Introduction to Manifolds ~ Tu ([link](https://www.springer.com/gp/book/9781441973993))
- [x] A Comprehensive Introduction to Differential Geometry Volume I ~ Spivak ([link](https://www.goodreads.com/book/show/211192.A_Comprehensive_Introduction_to_Differential_Geometry_Vol_1))
- [x] A Concise Course in Algebraic Topology ~ May ([pdf](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf))

The "time off" ended upon discovering this new "foundations of mathematics" thing seen of twitter, materialized into 2 copies ordered from different sources, one of them never got delivered:

- [x] Homotopy Type Theory ~ Univalent Foundations of Mathematics ([link](https://homotopytypetheory.org/book/))

As things started getting more cutting-edge, it has mostly been a paper and articles reading affair since then. Major ones being:

- [x] nLab ([link](https://ncatlab.org/nlab/show/HomePage))
- [x] Infinite Paper Napkin ([likn](https://web.evanchen.cc/napkin.html))
- [x] The Stacks Project ([link](https://stacks.math.columbia.edu/browse))

Of late, I stumbled upon this work on mathematical physics:

- [x] Gauge fields, knots, and gravity ~ Baez ([link](https://www.worldscientific.com/worldscibooks/10.1142/2324))

opening the path to these shiny new thingys that await:

- [x] geometry of physics ([link](https://ncatlab.org/nlab/show/geometry+of+physics))
- [ ] Differential cohomology in a cohesive ∞-topos ~ Schreiber ([link](https://arxiv.org/pdf/1310.7930.pdf))
- [ ] Quantum Gauge Field Theory in Cohesive Homotopy Type Theory ~ Schreiber ([pdf](https://arxiv.org/pdf/1408.0054.pdf))

It has been almost 4 years now, and the "whole thing" does not seem to have an end!

# Who is this for

This work is intended to be a resource for anyone (like me) making a foray into pure mathematics. The "like me" here implies someone who:

- [x] knows programming.
- [x] has worked with functional programming in some capacity.
- [x] has at least a sketchy idea of what "pure mathematics" means.
- [x] has boundless motivation to explore.

# Agda

Agda is a dependently-typed functional programming language that can be used as a "proof assistant" of the "propositions-as-types" flavor, i.e. it is a language used to write mathematical proofs, using a typesystem, which its compiler then verifies to check if the proofs really do what they claim. This is done by using Type theory as the language for writing proofs in Agda. Traditionally, the act of checking the validity of a proof has been a manual and painstaking process, however, the proofs when represented in this `code ⇆ compiler` paradigm, does away with the need for manual checking, thus making things considerably easier to implement, test and distribute. There are other alternative theorem provers, each with their own feature-sets, strengths and weaknesses, [documented here](https://en.wikipedia.org/wiki/Proof_assistant#Comparison_of_systems).

****
[Setup](./Lang.setup.html)
