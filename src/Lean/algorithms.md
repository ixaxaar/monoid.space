---

[Contents](contents.html)
[Previous](Lean.naming.html)
[Next](Lean.other.html)

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
  - [Graph Algorithms](#graph-algorithms)
    - [Graph Representation](#graph-representation)
    - [Depth-First Search](#depth-first-search)
    - [Breadth-First Search](#breadth-first-search)
  - [Dynamic Programming](#dynamic-programming)
    - [Fibonacci Sequence](#fibonacci-sequence)
    - [Longest Common Subsequence](#longest-common-subsequence)

Algorithms in Lean are implemented as functions that operate on data structures. The implementation often closely mirrors mathematical definitions while ensuring termination and correctness. This section is intended to also serve as a starting point where we use more real-world examples. A bunch of things are introduced here, and will be explained in more detail in the following sections.

These are the different types of algorithms we'll explore:

| Algorithm Type | Description                                  |
| -------------- | -------------------------------------------- |
| Search         | Finding elements in collections              |
| Sorting        | Ordering elements according to some criteria |
| Tree           | Operations on tree data structures           |
| Graph          | Traversal and analysis of graph structures   |
| Dynamic        | Solutions using optimal substructure         |

## Search Algorithms

Search algorithms find a givem elements in collections. We'll implement two fundamental search algorithms: linear search and binary search.

### Linear Search

Linear search sequentially checks each element in a list until finding the target or reaching the end of the list.

We have 2 cases to deal with:

- The list is empty, in which case we return `none`.
- The list is non-empty, in which case we check if the first element is equal to the target. If it is, we return `some 0`. Otherwise, we recursively search the rest of the list and increment the index by 1.

```lean
def linearSearch {α : Type} [BEq α] : List α → α → Option Nat
  | [],     _ => none -- trivial case
  | x::xs,  t => if x == t -- if the first element is the target,
                 then some 0 -- return the index 0
                 else match linearSearch xs t with -- otherwise, search the rest of the list
                      | none   => none -- if the target is not found, return none
                      | some i => some (i + 1) -- if the target is found, return the index + 1
```

`BEq` here is a typeclass that provides a way to compare elements of type `α`. It is similar to the `Eq` typeclass in Haskell, with the `B` standing for "binary".

Using this function in lean:

```lean
def list1 := [1, 2, 3, 4, 5]
#eval linearSearch list1 3  -- some 2
#eval linearSearch list1 6  -- none
```

### Binary Search

Binary search requires a sorted list and repeatedly divides the search interval in half.

We start with the usual trivial case of an empty list, in which case we return `none`.
We then define a helper function that takes the list, the target, and the low and high indices. If the low index is greater than the high index, we return `none`. Otherwise, we calculate the middle index and compare the middle element with the target. If they are equal, we return `some mid`. If the middle element is less than the target, we recursively search the right half of the list. If the middle element is greater than the target, we recursively search the left half of the list.

```lean
def binarySearch {α : Type} [Ord α] (xs : List α) (target : α) : Option Nat :=
  let rec aux (lo hi : Nat) (size : Nat) : Option Nat := -- recursive helper function
    if size = 0 then -- trivial case
      none
    else
      let mid := lo + size / 2 -- calculate the middle index
      match xs.get? mid with -- get the element at the middle index
      | none => none -- if the element is not found, return none
      | some x => -- if the element is found
        match compare x target with -- compare the middle element with the target
        | Ordering.eq => some mid -- if they are equal, return the middle index
        | Ordering.lt => aux (mid + 1) hi (size / 2) -- if the middle element is less than the target, search the right half
        | Ordering.gt => aux lo (mid - 1) (size / 2) -- if the middle element is greater than the target, search the left half
  termination_by size

  aux 0 (xs.length - 1) xs.length -- start the search from the beginning and end of the list
```

There are a few things to note here:

1. `Ord` is a typeclass that provides a way to compare elements of type `α`. It is similar to the `Ord` typeclass in Haskell. The `compare` function returns an `Ordering` value, which can be `lt`, `eq`, or `gt`.
2. We use the `get?` function to get the element at the middle index. This function returns an `Option` type, which we pattern match on.
3. We use the `let` keyword to bind the value of the middle element to `x`. `Let` is used to bind values to names in Lean, similar to `let` in Haskell, and `val` in Scala etc.
4. `termination_by size` is a directive that tells Lean that the function terminates when the `size` argument decreases. This is necessary because Lean requires that recursive functions are well-founded, i.e., they must terminate for all inputs. We will look at termination in more detail later.

This can be used as follows:

```lean
def sortedList := [1, 3, 5, 7, 9]
#eval binarySearch sortedList 5  -- some 2
#eval binarySearch sortedList 6  -- none
```

## Sorting Algorithms

Sorting algorithms arrange elements in a specific order. These algorithms can work on data types that support sorting, indicated by `[Ord α]` type constraint. We'll implement insertion sort and merge sort.

### Insertion Sort

Given a list, insertion sort builds the sorted list one element at a time by inserting each element into its correct position. We start with the trivial case of an empty list, in which case we return an empty list. For a non-empty list, we define a helper function that takes an element and a list. If the list is empty, we return a list containing the element. If the list is non-empty, we compare the element with the head of the list. If the element is less than the head, we insert the element at the beginning of the list. Otherwise, we recursively insert the element into the tail of the list.

```lean
def insert {α : Type} [Ord α] : α → List α → List α -- helper function to insert an element into a list
  | x, []     => [x] -- trivial case: if the list is empty, return a list containing the element
  | x, y::ys  => match compare x y with -- if the list is non-empty, compare the element with the head of the list
                 | Ordering.lt => x::y::ys -- if the element is less than the head, insert it at the beginning of the list
                 | _          => y::(insert x ys) -- otherwise, recursively insert the element into the tail of the list

def insertionSort {α : Type} [Ord α] : List α → List α -- insertion sort function
  | []     => [] -- trivial case: if the list is empty, return an empty list
  | x::xs  => insert x (insertionSort xs) -- for a non-empty list, insert the head into the sorted tail
```

```lean
def unsortedList1 := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
#eval insertionSort unsortedList1 -- [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]
```

### Merge Sort

Merge sort uses the divide-and-conquer strategy to sort elements. The algorithm works as follows:

1. Divide the list into two halves.
2. Recursively sort the two halves.
3. Merge the sorted halves.

We first define a `merge` function that merges two sorted lists.
We then define a `split` function that splits a list into two halves.
Finally, we define the `mergeSort` function that recursively splits the list into halves, sorts the halves, and merges them back together.

```lean
def merge {α : Type} [Ord α] : List α → List α → List α
  | [],     ys     => ys
  | xs,     []     => xs
  | x::xs', y::ys' =>
    match compare x y with
    | Ordering.lt => x::(merge xs' (y::ys'))
    | _           => y::(merge (x::xs') ys')

def split {α : Type} (list : List α) : (List α × List α) :=
  match list with
  | []      => ([], [])
  | [x]     => ([x], [])
  | x::y::r =>
    let (xs, ys) := split r
    (x::xs, y::ys)

def mergeSort {α : Type} [Ord α] (list : List α) : List α :=
  if list.length <= 1 then
    list
  else
    let (ys, zs) := split list
    merge (mergeSort ys) (mergeSort zs)
```

```lean
def unsortedList1 := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
#eval mergeSort unsortedList1
```

This code will not actually compile, as the Lean compiler will not be able to prove its termination. We see this error:

```md
failed to prove termination, possible solutions:

- Use `have`-expressions to prove the remaining goals
- Use `termination_by` to specify a different well-founded relation
- Use `decreasing_by` to specify your own tactic for discharging this kind of goal
  α : Type
  list : List α
  h✝ : ¬list.length ≤ 1
  ys : List α
  ⊢ sizeOf ys < sizeOf list
```

which says that the compiler is unable to prove that the size of the list decreases in each recursive call. We will look at proving termination in more detail later.

## Tree Algorithms

Trees have been used in computer science for a long time to represent hierarchical data. Data structures like binary trees, binary search trees, and heaps are a mainstay of computer science. General operations on trees include traversal, insertion, and deletion. There are also specialized trees like AVL trees, red-black trees, and B-trees and corresponding specialized operations on them.

### Tree Traversal

First, we define a binary tree structure and implement different traversal methods:

```lean
inductive BinTree (α : Type)
  | leaf : BinTree α -- leaf node
  -- internal node, note this is a complete binary tree
  | node : BinTree α → α → BinTree α → BinTree α
```

This can be used to create trees like:

```lean
def tree1 := BinTree.node
  (BinTree.node BinTree.leaf 1 BinTree.leaf)
  2
  (BinTree.node BinTree.leaf 3 BinTree.leaf)
```

We define three traversal methods: preorder, inorder, and postorder.

- Preorder traversal visits the root node first, then the left subtree, and finally the right subtree.
- Inorder traversal visits the left subtree first, then the root node, and finally the right subtree.
- Postorder traversal visits the left subtree first, then the right subtree, and finally the root node.

or in short:

- Preorder: root, left, right
- Inorder: left, root, right
- Postorder: left, right, root

```lean
def preorder {α : Type} : BinTree α → List α
  -- trivial case: if the tree is a leaf, return an empty list
  | BinTree.leaf => []
  -- for an internal node, visit the root, then the left and right subtrees
  | BinTree.node l x r => x :: (preorder l ++ preorder r)

def inorder {α : Type} : BinTree α → List α
  -- trivial case: if the tree is a leaf, return an empty list
  | BinTree.leaf => []
  -- for an internal node, visit the left subtree, then the root, and finally the right subtree
  | BinTree.node l x r => inorder l ++ [x] ++ inorder r

def postorder {α : Type} : BinTree α → List α
  -- trivial case: if the tree is a leaf, return an empty list
  | BinTree.leaf => []
  -- for an internal node, visit the left and right subtrees, then the root
  | BinTree.node l x r => postorder l ++ postorder r ++ [x]
```

Operations on binary search trees maintain the ordering property:

```lean
def insert_bst {α : Type} [Ord α] : BinTree α → α → BinTree α
  -- trivial case: if the tree is a leaf, create a new node with the element
  | BinTree.leaf, x => BinTree.node BinTree.leaf x BinTree.leaf
  -- for an internal node, compare the element with the root and insert it in the left or right subtree
  | BinTree.node l y r, x =>
      match compare x y with
      | Ordering.lt => BinTree.node (insert_bst l x) y r
      | Ordering.gt => BinTree.node l y (insert_bst r x)
      | Ordering.eq => BinTree.node l y r

def contains_bst {α : Type} [Ord α] : BinTree α → α → Bool
  -- trivial case: if the tree is a leaf, return false
  | BinTree.leaf, _ => false
  -- for an internal node, compare the element with the root and search in the left or right subtree
  | BinTree.node l y r, x =>
      match compare x y with
      | Ordering.lt => contains_bst l x
      | Ordering.gt => contains_bst r x
      | Ordering.eq => true
```

Lets look at a comprehensive example where we first create a rather complex tree and then perform various operations on it:

```lean
-- create a complex binary tree
def tree2 := BinTree.node
  (BinTree.node
    (BinTree.node
      BinTree.leaf 1
      (BinTree.node BinTree.leaf 2 BinTree.leaf)
    )
    3
    (BinTree.node
      BinTree.leaf 4
      (BinTree.node BinTree.leaf 5 BinTree.leaf)
    )
  )
  6
  (BinTree.node
    (BinTree.node
      (BinTree.node BinTree.leaf 7 BinTree.leaf)
      8
      BinTree.leaf
    )
    9
    (BinTree.node BinTree.leaf 10 BinTree.leaf)
  )

-- traversals
#eval preorder tree2  -- [6, 3, 1, 2, 4, 5, 9, 7, 8, 10]
#eval inorder tree2   -- [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval postorder tree2 -- [2, 1, 5, 4, 3, 7, 8, 10, 9, 6]

-- insertions
def tree3 := insert_bst tree2 0
def tree4 := insert_bst tree3 11
def tree5 := insert_bst tree4 6

-- verify if elements are present in the tree
#eval inorder tree5   -- [0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11]

-- search for elements in the tree
#eval contains_bst tree5 7  -- true
#eval contains_bst tree5 12 -- false
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

A classic example of dynamic programming is the Fibonacci sequence.

We implement the Fibonacci sequence using memoization. Memoization is a technique that stores the results of expensive function calls and returns the cached result when the same inputs occur again. Here we use an array to store the results of the Fibonacci sequence and return the result along with the updated array.

```lean
def fib_memo : Nat → Array Nat → Nat × Array Nat
  | 0, memo => (0, memo) -- trivial case: if n is 0, return 0
  | 1, memo => (1, memo) -- trivial case: if n is 1, return 1
  | n+2, memo => -- for n > 1, calculate the Fibonacci number using memoization
    match memo.get? (n+2) with -- check if the result is already memoized
    | some val => (val, memo) -- if the result is memoized, return the result
    | none     => -- if the result is not memoized
      let (val1, memo1) := fib_memo (n+1) memo -- calculate the Fibonacci number for n+1
      let (val2, memo2) := fib_memo n memo1 -- calculate the Fibonacci number for n
      let result := val1 + val2 -- calculate the Fibonacci number for n+2
      (result, memo2.push result) -- return the result and update the memo array

def fib (n : Nat) : Nat := -- wrapper function to calculate the Fibonacci number
  (fib_memo n #[0, 1]).1
```

Now we can calculate the Fibonacci number for any given `n`:

```lean
#eval fib 10  -- 55
```

### Longest Common Subsequence

The longest common subsequence (LCS) problem is a classic dynamic programming problem. Given two sequences, the LCS problem is to find the longest subsequence that is common to both sequences. This problem has several practical applications, such as comparing DNA sequences, comparing files, and comparing version control histories.

We define a recursive function that takes two lists and returns the longest common subsequence. We have 3 cases to deal with:

1. If either of the lists is empty, the LCS is empty.
2. If the first elements of the lists are equal, the LCS is the first element followed by the LCS of the rest of the lists.
3. If the first elements of the lists are not equal, we calculate the LCS of the first list with the second list minus the first element and the first list minus the first element with the second list. We then return the LCS with the maximum length.

```lean
def lcs {α : Type} [BEq α] : List α → List α → List α
  | [],     _      => [] -- trivial case: if the first list is empty, return an empty list
  | _,      []     => [] -- trivial case: if the second list is empty, return an empty list
  | x::xs', y::ys' => -- for non-empty lists
      if x == y -- if the first elements are equal
      then x::(lcs xs' ys')   -- return the first element followed by the LCS of the rest of the lists
      else
        let l1 := lcs (x::xs') ys' -- calculate the LCS of the first list with the second list minus the first element
        let l2 := lcs xs' (y::ys') -- calculate the LCS of the first list minus the first element with the second list
        if l1.length ≥ l2.length then l1 else l2 -- return the LCS with the maximum length
```

We can now calculate the LCS of two sequences:

```lean
#eval lcs "ABCDGH".data "AEDFHR".data  -- ['A', 'D', 'H']
```

---

[Modules and projects](./Lean.other.html)
