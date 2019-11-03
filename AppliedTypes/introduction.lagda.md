****
[Contents](contents.html)

```agda
module AppliedTypes.introduction where
```

Type Theory can be a tool for formally modeling various systems and writing proofs about them. These systems can technically be any system, though practically, real-world usage is minuscule and for niche use-cases, partly driven by the need for extreme caution or where adherence to formal specifications is paramount. For example, it's safer to write programs in such a way that their functionalities are formally proven instead of relying on tests that try to cover or test as much code and cases as possible. Use-cases include verifying protocols (e.g. in cryptography, cryptographic applications like cryptocurrencies), combinational circuits, digital circuits with internal memory, software systems in finance, embedded systems etc. Formal verification is especially big in the electronics hardware space as errors cost much more, and hence such an audience tends to have their own languages and tools for formal verification, such as Cadence's [Conformal equivalence checker](https://www.cadence.com/content/cadence-www/global/en_US/home/tools/digital-design-and-signoff/logic-equivalence-checking/conformal-equivalence-checker.html), Mentor Graphics' [FormalPro](https://www.mentor.com/products/fv/formalpro/), Synopsys' [formality](https://www.synopsys.com/implementation-and-signoff/signoff/formality.html) etc. According to Wikipedia, examples of mathematical objects often used to model systems are: finite state machines, labeled transition systems, Petri nets, vector addition systems, timed automata, hybrid automata, process algebra, formal semantics of programming languages such as operational semantics, denotational semantics, axiomatic semantics and Hoare logic.

Similar to how type checking in compiled languages grant a guarantee against runtime failures due to type errors, formal proofs offer stronger guarantees of equivalence, termination and spec-adherence. Here, we will implement a few formal systems and model some interesting technologies as applications of type theory and as a demonstration of what can be done in Agda. Finally, we will see how to use our formally checked code in the outside world.

****
[Gödel's T](./AppliedTypes.godels_t.html)
