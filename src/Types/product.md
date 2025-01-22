****
[Contents](contents.html)
[Previous](Types.operations.html)
[Next](Types.functions.html)

# Products & Co-products

****

- [Products \& Co-products](#products--co-products)
    - [Informal Introduction](#informal-introduction)

## Informal Introduction

Products and co-products are the most basic forms of type constructors in type theory. They are used to combine types in a way that preserves the information of the original types. Let us first start with a very informal definition of products and co-products.

Suppose we have a bunch of types `A`, `B`, `C`, `D`, etc. A product of these types is a type that contains all possible combinations of elements from `A`, `B`, `C`, `D`, etc. In the context of programming, this is similar to a tuple or a record:

```scala
case class Tuple2[A, B](a: A, b: B)
```

```java
type Tuple2<A, B> = Pair<A, B>
```

In both the above examples, we define a new type or class (an enclosure) that contains two elements of types `A` and `B`. This is a product type and is a very obvious way to combine types widely used in programming.

A co-product, on the other hand, is a type that can be either of the types `A`, `B`, `C`, `D`, etc. In programming, this is similar to a sum type or a union:

```scala
sealed trait Either[A, B]
case class Left[A, B](a: A) extends Either[A, B]
case class Right[A, B](b: B) extends Either[A, B]
```

```java
interface Either<A, B> {
  A getLeft();
  B getRight();
}
```

In both the above examples, we define a new type or class (an enclosure) that can be either of the two types `A` or `B`. This is a co-product type and is a very useful way to often handle errors or exceptions in programming, another very popular example being the `Option` type.


****
[Dependent Function Types / Π-types](./Types.functions.html)
