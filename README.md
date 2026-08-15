# FingerTrees.jl

`FingerTrees.jl` provides a persistent sequence based on finger trees. Updating
either end, splitting, concatenating, or replacing an element returns a new
tree and leaves the original unchanged.

The package is being modernized and its internal representation is still
evolving. The core sequence operations are usable, but the API should be
considered experimental.

```julia
using FingerTrees

tree = FingerTree(1:5)
tree = conjl(0, tree)
tree = conjr(tree, 6)

tree[4]                 # 3
collect(tree[3:5])      # [2, 3, 4]

left, value, right = split(tree, 4)
updated = assoc(tree, 99, 4)
joined = concat(left, conjl(value, right))

collect(tree)           # [0, 1, 2, 3, 4, 5, 6]
collect(updated)        # [0, 1, 2, 99, 4, 5, 6]
```

Create a typed empty tree with `FingerTree(T)`:

```julia
empty_tree = FingerTree(String)
```

The main operations are:

- `conjl(value, tree)` and `conjr(tree, value)` for persistent end insertion;
- `splitl(tree)` and `splitr(tree)` for persistent end removal;
- `split(tree, index)` for splitting around an element;
- `concat(left, right)` for concatenation;
- `assoc(tree, value, index)` for persistent replacement;
- ordinary iteration, `length`, `first`, `last`, scalar indexing, and ranges.

Run the tests with:

```julia
using Pkg
Pkg.test()
```

Focused performance benchmarks live in `benchmark/`.
