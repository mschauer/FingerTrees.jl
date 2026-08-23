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
- `multiassoc(tree, indices, values)` and `multiupdate(tree, indices, f)` for
  batched replacements, particularly when updated paths overlap;
- ordinary iteration, `length`, `first`, `last`, scalar indexing, and ranges.

A tree can also own a measure operation:

```julia
measured = MeasuredFingerTree(1:100, LengthMeasure())
measure(measured)                                      # 100
left, value, right = split_measure(n -> n >= 40, measured)
```

Custom measures subtype `Measure` and implement `Base.identity`, `measure`,
and `combine`. Measures are cached throughout the tree, so `measure(tree)` is
constant-time and `split_measure` descends through cached summaries in
logarithmic time. Its predicate should be monotone over successive prefixes.

A persistent stable min-priority queue is built on this measured tree:

```julia
queue = PriorityQueue([:compile => 5, :respond => 1, :test => 3])
peek(queue)                         # :respond => 1
entry, remaining = dequeue(queue)  # queue itself is unchanged
queue = enqueue(queue, :urgent, 0)
```

Entries are written as `value => priority`. Equal priorities leave the queue
in insertion order.

Run the tests with:

```julia
using Pkg
Pkg.test()
```

Performance benchmarks live in `benchmark/`.
