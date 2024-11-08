---

[Contents](contents.html)
[Previous](Lean.naming.html)
[Next](Lean.other.html)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

---

# Algorithms

---

- [Algorithms](#algorithms)
  - [Search Algorithms](#search-algorithms)
    - [Linear Search](#linear-search)
    - [Binary Search](#binary-search)
  - [Sorting Algorithms](#sorting-algorithms)
    - [Insertion Sort](#insertion-sort)
    - [Merge Sort](#merge-sort)
  - [Tree Algorithms](#tree-algorithms)
    - [Tree Traversal](#tree-traversal)
    - [Binary Search Tree Operations](#binary-search-tree-operations)
  - [Graph Algorithms](#graph-algorithms)
    - [Graph Representation](#graph-representation)
    - [Depth-First Search](#depth-first-search)
    - [Breadth-First Search](#breadth-first-search)
  - [Dynamic Programming](#dynamic-programming)
    - [Fibonacci Sequence](#fibonacci-sequence)
    - [Longest Common Subsequence](#longest-common-subsequence)
---


Algorithms in Lean are implemented as functions that operate on data structures. The implementation often closely mirrors mathematical definitions while ensuring termination and correctness.

These are the different types of algorithms we'll explore:

| Algorithm Type | Description                                  |
|----------------|----------------------------------------------|
| Search         | Finding elements in collections              |
| Sorting        | Ordering elements according to some criteria |
| Tree           | Operations on tree data structures           |
| Graph          | Traversal and analysis of graph structures   |
| Dynamic        | Solutions using optimal substructure         |

## Search Algorithms

Search algorithms find elements in collections. We'll implement two fundamental search algorithms: linear search and binary search.

### Linear Search

Linear search sequentially checks each element in a list until finding the target or reaching the end.

```lean
def linearSearch {α : Type} [BEq α] : List α → α → Option Nat
  | [],     _ => none
  | x::xs,  t => if x == t
                 then some 0
                 else match linearSearch xs t with
                      | none   => none
                      | some i => some (i + 1)

/-- Example usage: -/
def list1 := [1, 2, 3, 4, 5]
#eval linearSearch list1 3  -- some 2
#eval linearSearch list1 6  -- none
```

### Binary Search

Binary search requires a sorted list and repeatedly divides the search interval in half.

```lean
def binarySearch {α : Type} [Ord α] : List α → α → Option Nat
  | [],     _ => none
  | xs,     t => binarySearchHelper xs t 0 (xs.length - 1)
where
  binarySearchHelper (xs : List α) (t : α) (low high : Nat) : Option Nat :=
    if low > high then none
    else
      let mid := (low + high) / 2
      match xs.get? mid with
      | none     => none
      | some val => match compare val t with
                   | Ordering.eq => some mid
                   | Ordering.lt => binarySearchHelper xs t (mid + 1) high
                   | Ordering.gt => binarySearchHelper xs t low (mid - 1)

/-- Example usage: -/
def sortedList := [1, 3, 5, 7, 9]
#eval binarySearch sortedList 5  -- some 2
#eval binarySearch sortedList 6  -- none
```

## Sorting Algorithms

Sorting algorithms arrange elements in a specific order. We'll implement insertion sort and merge sort.

### Insertion Sort

Insertion sort builds the final sorted array one element at a time.

```lean
def insert {α : Type} [Ord α] : α → List α → List α
  | x, []     => [x]
  | x, y::ys  => match compare x y with
                 | Ordering.lt => x::y::ys
                 | _          => y::(insert x ys)

def insertionSort {α : Type} [Ord α] : List α → List α
  | []     => []
  | x::xs  => insert x (insertionSort xs)

/-- Example usage: -/
def unsortedList1 := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
#eval insertionSort unsortedList1
```

### Merge Sort

Merge sort uses the divide-and-conquer strategy to sort elements.

```lean
def merge {α : Type} [Ord α] : List α → List α → List α
  | [],     ys     => ys
  | xs,     []     => xs
  | x::xs', y::ys' => match compare x y with
                      | Ordering.lt => x::(merge xs' (y::ys'))
                      | _          => y::(merge (x::xs') ys')

def split {α : Type} : List α → (List α × List α)
  | []      => ([], [])
  | [x]     => ([x], [])
  | x::y::r => let (xs, ys) := split r
               (x::xs, y::ys)

def mergeSort {α : Type} [Ord α] : List α → List α
  | []  => []
  | [x] => [x]
  | xs  => let (ys, zs) := split xs
           merge (mergeSort ys) (mergeSort zs)

/-- Example usage: -/
#eval mergeSort unsortedList1
```

## Tree Algorithms

Tree algorithms operate on hierarchical data structures. We'll look at basic tree operations and traversals.

### Tree Traversal

First, we define a binary tree structure and implement different traversal methods:

```lean
inductive BinTree (α : Type)
  | leaf : BinTree α
  | node : BinTree α → α → BinTree α → BinTree α

def preorder {α : Type} : BinTree α → List α
  | BinTree.leaf => []
  | BinTree.node l x r => x :: (preorder l ++ preorder r)

def inorder {α : Type} : BinTree α → List α
  | BinTree.leaf => []
  | BinTree.node l x r => inorder l ++ [x] ++ inorder r

def postorder {α : Type} : BinTree α → List α
  | BinTree.leaf => []
  | BinTree.node l x r => postorder l ++ postorder r ++ [x]

/-- Example usage: -/
def tree1 := BinTree.node
  (BinTree.node BinTree.leaf 1 BinTree.leaf)
  2
  (BinTree.node BinTree.leaf 3 BinTree.leaf)

#eval preorder tree1   -- [2, 1, 3]
#eval inorder tree1    -- [1, 2, 3]
#eval postorder tree1  -- [1, 3, 2]
```

### Binary Search Tree Operations

Operations on binary search trees maintain the ordering property:

```lean
def insert_bst {α : Type} [Ord α] : BinTree α → α → BinTree α
  | BinTree.leaf, x => BinTree.node BinTree.leaf x BinTree.leaf
  | BinTree.node l y r, x =>
      match compare x y with
      | Ordering.lt => BinTree.node (insert_bst l x) y r
      | Ordering.gt => BinTree.node l y (insert_bst r x)
      | Ordering.eq => BinTree.node l y r

def contains_bst {α : Type} [Ord α] : BinTree α → α → Bool
  | BinTree.leaf, _ => false
  | BinTree.node l y r, x =>
      match compare x y with
      | Ordering.lt => contains_bst l x
      | Ordering.gt => contains_bst r x
      | Ordering.eq => true
```

## Graph Algorithms

Graph algorithms work with connected structures. We'll implement basic graph traversals.

### Graph Representation

We'll represent graphs using adjacency lists:

```lean
def Graph (α : Type) := List (α × List α)

def addEdge {α : Type} [BEq α] : Graph α → α → α → Graph α
  | [],     u, v => [(u, [v])]
  | (x,xs)::g, u, v =>
      if x == u
      then (x, v::xs)::g
      else (x,xs)::(addEdge g u v)

/-- Example usage: -/
def graph1 : Graph Nat := []
def graph2 := addEdge graph1 1 2
def graph3 := addEdge graph2 1 3
#eval graph3  -- [(1, [3, 2])]
```

### Depth-First Search

DFS explores as far as possible along each branch:

```lean
def dfs_helper {α : Type} [BEq α] :
  Graph α → α → List α → List α
  | g, u, visited =>
    if visited.contains u
    then visited
    else let neighbors := (g.find? (λ p => p.1 == u)).map (λ p => p.2).getD []
         neighbors.foldl (λ acc v => dfs_helper g v acc) (u::visited)

def dfs {α : Type} [BEq α] (g : Graph α) (start : α) : List α :=
  dfs_helper g start []

/-- Example usage: -/
def graph4 := addEdge (addEdge (addEdge graph3 2 4) 3 4) 4 1
#eval dfs graph4 1  -- [4, 3, 2, 1]
```

### Breadth-First Search

BFS explores neighbor nodes first:

```lean
def bfs_helper {α : Type} [BEq α] :
  Graph α → List α → List α → List α
  | _,  [],    visited => visited.reverse
  | g,  u::queue, visited =>
    if visited.contains u
    then bfs_helper g queue visited
    else
      let neighbors := (g.find? (λ p => p.1 == u)).map (λ p => p.2).getD []
      let newQueue := queue ++ (neighbors.filter (λ v => ¬visited.contains v))
      bfs_helper g newQueue (u::visited)

def bfs {α : Type} [BEq α] (g : Graph α) (start : α) : List α :=
  bfs_helper g [start] []

#eval bfs graph4 1  -- [1, 2, 3, 4]
```

## Dynamic Programming

Dynamic programming solves complex problems by breaking them down into simpler subproblems.

### Fibonacci Sequence

A classic example of dynamic programming:

```lean
def fib_memo : Nat → Array Nat → Nat × Array Nat
  | 0, memo => (0, memo)
  | 1, memo => (1, memo)
  | n+2, memo =>
    match memo.get? (n+2) with
    | some val => (val, memo)
    | none     =>
      let (val1, memo1) := fib_memo (n+1) memo
      let (val2, memo2) := fib_memo n memo1
      let result := val1 + val2
      (result, memo2.push result)

def fib (n : Nat) : Nat :=
  (fib_memo n #[0, 1]).1

#eval fib 10  -- 55
```

### Longest Common Subsequence

Finding the longest common subsequence of two sequences:

```lean
def lcs {α : Type} [BEq α] : List α → List α → List α
  | [],     _      => []
  | _,      []     => []
  | x::xs', y::ys' =>
      if x == y
      then x::(lcs xs' ys')
      else
        let l1 := lcs (x::xs') ys'
        let l2 := lcs xs' (y::ys')
        if l1.length ≥ l2.length then l1 else l2

/-- Example usage: -/
#eval lcs "ABCDGH".data "AEDFHR".data  -- ['A', 'D', 'H']
```

[Modules and projects](./Lean.other.html)
