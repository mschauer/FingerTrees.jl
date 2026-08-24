module FingerTrees
import Base: reduce, length, collect, split, eltype, isempty

export FingerTree, EmptyFT, MeasuredFingerTree
export Measure, LengthMeasure, measure, combine, split_measure
export assoc, multiassoc, multiupdate, multifold, concat, conjl, conjr, split, splitl, splitr
export PriorityQueue, enqueue, dequeue, peekpriority

# ---------------------------------------------------------------------------
# Internal representation
# ---------------------------------------------------------------------------

abstract type FingerTree{T} end
abstract type Tree23{T} end
abstract type Measure end

struct LengthMeasure <: Measure end
Base.identity(::LengthMeasure) = 0
measure(::LengthMeasure, _) = 1
combine(::LengthMeasure, left::Int, right::Int) = left + right

struct _NoMeasure end
const _NO_MEASURE = _NoMeasure()
const _MeasureOp = Union{Measure,_NoMeasure}
Base.identity(::_NoMeasure) = nothing
measure(::_NoMeasure, _) = nothing
combine(::_NoMeasure, ::Nothing, ::Nothing) = nothing

struct _Cache{V}
    len::Int
    value::V
end

@inline _combine_cache(op, left::_Cache, right::_Cache) =
    _Cache(left.len + right.len, combine(op, left.value, right.value))

@inline _cache(op, value) = _Cache(1, measure(op, value))
@inline _cache_many(op, value) = _cache(op, value)
@inline _cache_many(op, first, rest...) =
    _combine_cache(op, _cache(op, first), _cache_many(op, rest...))

# Internal builders preserve balance by construction and bypass the recursive
# checks performed by the public node constructors.

mutable struct Leaf23{T,V} <: Tree23{T}
    const a::T
    const b::T
    const c::Union{Nothing,T}
    const len::Int
    const value::V
end

struct Node23{T,V} <: Tree23{T}
    a::Union{Leaf23{T,V},Node23{T,V}}
    b::Union{Leaf23{T,V},Node23{T,V}}
    c::Union{Nothing,Leaf23{T,V},Node23{T,V}}
    len::Int
    value::V
end

const Tree23RepV{T,V} = Union{Leaf23{T,V},Node23{T,V}}
const Tree23Rep{T} = Union{Leaf23{T},Node23{T}}

@inline _cache(::Any, node::Tree23) = _Cache(node.len, node.value)

function _leaf23(op::_MeasureOp, a::T, b::T) where {T}
    cache = _cache_many(op, a, b)
    Leaf23{T,typeof(cache.value)}(a, b, nothing, cache.len, cache.value)
end
function _leaf23(op::_MeasureOp, a::T, b::T, c::T) where {T}
    cache = _cache_many(op, a, b, c)
    Leaf23{T,typeof(cache.value)}(a, b, c, cache.len, cache.value)
end

function _node23(op::_MeasureOp, a::Tree23{T}, b::Tree23{T}) where {T}
    cache = _cache_many(op, a, b)
    Node23{T,typeof(cache.value)}(a, b, nothing, cache.len, cache.value)
end
function _node23(op::_MeasureOp, a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T}
    cache = _cache_many(op, a, b, c)
    Node23{T,typeof(cache.value)}(a, b, c, cache.len, cache.value)
end

@inline function _node23_cached(op::_MeasureOp, a::Tree23RepV{T,V},
                                b::Tree23RepV{T,V})::Node23{T,V} where {T,V}
    cache = _cache_many(op, a, b)
    Node23{T,V}(a, b, nothing, cache.len, cache.value::V)
end
@inline function _node23_cached(op::_MeasureOp, a::Tree23RepV{T,V},
                                b::Tree23RepV{T,V},
                                c::Tree23RepV{T,V})::Node23{T,V} where {T,V}
    cache = _cache_many(op, a, b, c)
    Node23{T,V}(a, b, c, cache.len, cache.value::V)
end

function Leaf23(a::T, b::T) where {T}
    dep(a) == dep(b) || throw(ArgumentError("cannot construct an uneven 2-leaf"))
    _leaf23(_NO_MEASURE, a, b)
end
function Leaf23(a::T, b::T, c::T) where {T}
    dep(a) == dep(b) == dep(c) || throw(ArgumentError("cannot construct an uneven 3-leaf"))
    _leaf23(_NO_MEASURE, a, b, c)
end
function Node23(a::Tree23{T}, b::Tree23{T}) where {T}
    dep(a) == dep(b) || throw(ArgumentError("cannot construct an uneven 2-node"))
    _node23(_NO_MEASURE, a, b)
end
function Node23(a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T}
    dep(a) == dep(b) == dep(c) || throw(ArgumentError("cannot construct an uneven 3-node"))
    _node23(_NO_MEASURE, a, b, c)
end

Tree23(a, b) = Leaf23(a, b)
Tree23(a, b, c) = Leaf23(a, b, c)
Tree23(a::Tree23{T}, b::Tree23{T}) where {T} = Node23(a, b)
Tree23(a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T} = Node23(a, b, c)

_unchecked_tree23(op::_MeasureOp, a, b) = _leaf23(op, a, b)
_unchecked_tree23(op::_MeasureOp, a, b, c) = _leaf23(op, a, b, c)
_unchecked_tree23(op::_MeasureOp, a::Tree23{T}, b::Tree23{T}) where {T} = _node23(op, a, b)
_unchecked_tree23(op::_MeasureOp, a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T} = _node23(op, a, b, c)
_unchecked_tree23(a, b) = _unchecked_tree23(_NO_MEASURE, a, b)
_unchecked_tree23(a, b, c) = _unchecked_tree23(_NO_MEASURE, a, b, c)

abstract type DigitFT{T,N} end

# Digits have reference identity so reusing one in a path copy does not box its
# payload again. Const fields preserve the immutable semantics of the tree.
mutable struct DLeaf{T,N,V} <: DigitFT{T,N} # Constructors restrict N to 1:4.
    const child::NTuple{N,T}
    const len::Int
    const value::V
end

mutable struct DNode{T,N,V} <: DigitFT{T,N}
    const child::NTuple{N,Tree23RepV{T,V}}
    const len::Int
    const value::V
end

const DigitFTRepV{T,V} = Union{
    DLeaf{T,1,V}, DLeaf{T,2,V}, DLeaf{T,3,V}, DLeaf{T,4,V},
    DNode{T,1,V}, DNode{T,2,V}, DNode{T,3,V}, DNode{T,4,V},
}
const DigitFTRep{T} = Union{
    DLeaf{T,1},
    DLeaf{T,2},
    DLeaf{T,3},
    DLeaf{T,4},
    DNode{T,1},
    DNode{T,2},
    DNode{T,3},
    DNode{T,4},
}

const DigitFT1{T} = DigitFT{T,1}
const DigitFT2{T} = DigitFT{T,2}
const DigitFT3{T} = DigitFT{T,3}
const DigitFT4{T} = DigitFT{T,4}

@inline _cache(::Any, digit::DigitFT) = _Cache(digit.len, digit.value)

function _dleaf(op::_MeasureOp, children::NTuple{N,T}) where {N,T}
    cache = _cache_many(op, children...)
    DLeaf{T,N,typeof(cache.value)}(children, cache.len, cache.value)
end
function _dnode(op::_MeasureOp, children::NTuple{N,<:Tree23{T}}) where {N,T}
    cache = _cache_many(op, children...)
    DNode{T,N,typeof(cache.value)}(children, cache.len, cache.value)
end

@inline function _dnode_cached(op::_MeasureOp,
                               children::Tuple{Tree23RepV{T,V}})::DNode{T,1,V} where {T,V}
    cache = _cache_many(op, children...)
    DNode{T,1,V}(children, cache.len, cache.value::V)
end
@inline function _dnode_cached(op::_MeasureOp,
                               children::Tuple{Tree23RepV{T,V},Tree23RepV{T,V}})::DNode{T,2,V} where {T,V}
    cache = _cache_many(op, children...)
    DNode{T,2,V}(children, cache.len, cache.value::V)
end
@inline function _dnode_cached(op::_MeasureOp,
                               children::Tuple{Tree23RepV{T,V},Tree23RepV{T,V},
                                              Tree23RepV{T,V}})::DNode{T,3,V} where {T,V}
    cache = _cache_many(op, children...)
    DNode{T,3,V}(children, cache.len, cache.value::V)
end
@inline function _dnode_cached(op::_MeasureOp,
                               children::Tuple{Tree23RepV{T,V},Tree23RepV{T,V},
                                              Tree23RepV{T,V},Tree23RepV{T,V}})::DNode{T,4,V} where {T,V}
    cache = _cache_many(op, children...)
    DNode{T,4,V}(children, cache.len, cache.value::V)
end

DLeaf(values::T...) where {T} = _dleaf(_NO_MEASURE, values)
function DNode(values::Tree23{T}...) where {T}
    depths = map(dep, values)
    all(==(first(depths)), depths) || throw(ArgumentError("cannot construct an uneven digit"))
    _dnode(_NO_MEASURE, values)
end

DigitFT(values...) = _unchecked_digit(values...)

_unchecked_digit(op::_MeasureOp, values...) = _dleaf(op, values)
_unchecked_digit(op::_MeasureOp, values::Tree23{T}...) where {T} = _dnode(op, values)
_unchecked_digit(values...) = _unchecked_digit(_NO_MEASURE, values...)

function digit(op::_MeasureOp, n::Tree23{T}) where T
    if isnothing(n.c)
        _unchecked_digit(op, n.a, n.b)
    else
        _unchecked_digit(op, n.a, n.b, something(n.c))
    end
end
digit(n::Tree23) = digit(_NO_MEASURE, n)
digit(op::_MeasureOp, t::NTuple) = _unchecked_digit(op, t...)
digit(op::_MeasureOp, value) = _unchecked_digit(op, value)
digit(t::NTuple) = digit(_NO_MEASURE, t)
digit(value) = digit(_NO_MEASURE, value)

struct EmptyFT{T} <: FingerTree{T}
end

struct SingleFT{T,V} <: FingerTree{T}
    a::Union{T,Tree23RepV{T,V}}
    value::V
end

struct DeepFT{T,V} <: FingerTree{T}
    left::DigitFTRepV{T,V}
    succ::Union{EmptyFT{T},SingleFT{T,V},DeepFT{T,V}}
    right::DigitFTRepV{T,V}
    len::Int
    value::V
end

const FingerTreeRepV{T,V} = Union{EmptyFT{T},SingleFT{T,V},DeepFT{T,V}}
const FingerTreeRep{T} = Union{EmptyFT{T},SingleFT{T},DeepFT{T}}

@inline _cache(op, ::EmptyFT) = _Cache(0, Base.identity(op))
@inline _cache(::Any, single::SingleFT) = _Cache(len(single), single.value)
@inline _cache(::Any, deep::DeepFT) = _Cache(deep.len, deep.value)

function _single(op::_MeasureOp, value::T) where {T}
    cache = _cache(op, value)
    SingleFT{T,typeof(cache.value)}(value, cache.value)
end
function _single(op::_MeasureOp, node::Tree23{T}) where {T}
    cache = _cache(op, node)
    V = typeof(cache.value)
    SingleFT{T,V}(node, cache.value)
end
SingleFT(value) = _single(_NO_MEASURE, value)

function _deep(op::_MeasureOp, left::DigitFT{T}, middle::FingerTree{T}, right::DigitFT{T}) where {T}
    cache = _combine_cache(op, _combine_cache(op, _cache(op, left), _cache(op, middle)), _cache(op, right))
    V = typeof(cache.value)
    DeepFT{T,V}(left, middle, right, cache.len, cache.value)
end

function DeepFT(left::DigitFT{T}, middle::FingerTree{T}, right::DigitFT{T}) where {T}
    balanced = dep(left) == dep(middle) - 1 == dep(right) ||
        (isempty(middle) && dep(left) == dep(right))
    balanced || throw(ArgumentError("cannot construct an uneven finger tree"))
    _deep(_NO_MEASURE, left, middle, right)
end

"""A persistent sequence together with its measure operation and cached summary."""
struct MeasuredFingerTree{T,M,V}
    measureop::M
    root::FingerTreeRepV{T,V}
end
const SplitValue{T,V} = Union{T,Tree23RepV{T,V}}

# End views distinguish the public leaf level from recursive node levels.
# This lets pop avoid carrying SplitValue{T} through the recursive hot path.
struct LeafLeftView{T,V}
    value::T
    rest::FingerTreeRepV{T,V}
end

struct LeafRightView{T,V}
    rest::FingerTreeRepV{T,V}
    value::T
end

struct NodeLeftView{T,V}
    value::Tree23RepV{T,V}
    rest::FingerTreeRepV{T,V}
end

struct NodeRightView{T,V}
    rest::FingerTreeRepV{T,V}
    value::Tree23RepV{T,V}
end

const TraversalBranch{T,V} = Union{
    DeepFT{T,V},
    Node23{T,V},
    DNode{T,1,V},
    DNode{T,2,V},
    DNode{T,3,V},
    DNode{T,4,V},
}

mutable struct IterationState{T,V}
    branches::Vector{TraversalBranch{T,V}}
    next::Vector{Int}
    pending::Vector{T}
    pending_next::Int
end

DeepFT(l::T, s::FingerTree{T}, r::T) where {T} = DeepFT(digit(l), s, digit(r))
DeepFT(l::Tree23{T}, s::FingerTree{T}, r::Tree23{T}) where {T} = DeepFT(DigitFT(l), s, DigitFT(r))

DeepFT(l::T, r::T) where {T} = DeepFT(DigitFT(l), EmptyFT{T}(), DigitFT(r))
DeepFT(l::Tree23{T}, r::Tree23{T}) where {T} = DeepFT(DigitFT(l), EmptyFT{T}(), DigitFT(r))
DeepFT(l::DigitFT{T}, r::DigitFT{T}) where {T} = DeepFT(l, EmptyFT{T}(), r)

_unchecked_deep(op::_MeasureOp, l::DigitFT{T}, s::FingerTree{T}, r::DigitFT{T}) where {T} =
    _deep(op, l, s, r)
_unchecked_deep(op::_MeasureOp, l::T, s::FingerTree{T}, r::T) where {T} =
    _unchecked_deep(op, _unchecked_digit(op, l), s, _unchecked_digit(op, r))
_unchecked_deep(op::_MeasureOp, l::Tree23{T}, s::FingerTree{T}, r::Tree23{T}) where {T} =
    _unchecked_deep(op, _unchecked_digit(op, l), s, _unchecked_digit(op, r))
_unchecked_deep(op::_MeasureOp, l::T, r::T) where {T} =
    _unchecked_deep(op, _unchecked_digit(op, l), EmptyFT{T}(), _unchecked_digit(op, r))
_unchecked_deep(op::_MeasureOp, l::Tree23{T}, r::Tree23{T}) where {T} =
    _unchecked_deep(op, _unchecked_digit(op, l), EmptyFT{T}(), _unchecked_digit(op, r))
_unchecked_deep(op::_MeasureOp, l::DigitFT{T}, r::DigitFT{T}) where {T} =
    _unchecked_deep(op, l, EmptyFT{T}(), r)

_unchecked_deep(l::DigitFT{T}, s::FingerTree{T}, r::DigitFT{T}) where {T} =
    _unchecked_deep(_NO_MEASURE, l, s, r)
_unchecked_deep(l::T, s::FingerTree{T}, r::T) where {T} =
    _unchecked_deep(_unchecked_digit(l), s, _unchecked_digit(r))
_unchecked_deep(l::Tree23{T}, s::FingerTree{T}, r::Tree23{T}) where {T} =
    _unchecked_deep(_unchecked_digit(l), s, _unchecked_digit(r))
_unchecked_deep(l::T, r::T) where {T} =
    _unchecked_deep(_unchecked_digit(l), EmptyFT{T}(), _unchecked_digit(r))
_unchecked_deep(l::Tree23{T}, r::Tree23{T}) where {T} =
    _unchecked_deep(_unchecked_digit(l), EmptyFT{T}(), _unchecked_digit(r))
_unchecked_deep(l::DigitFT{T}, r::DigitFT{T}) where {T} =
    _unchecked_deep(l, EmptyFT{T}(), r)

# Structural depth is checked recursively and is not stored in persistent nodes.

# ---------------------------------------------------------------------------
# Cached measures and collection interface
# ---------------------------------------------------------------------------

dep(_) = 0
dep(n::Leaf23) = 1
dep(n::Node23) = dep(n.a) + 1
dep(::DLeaf) = 0
dep(d::DNode) = dep(d.child[1])
dep(s::SingleFT) = dep(s.a)
dep(_::EmptyFT) = 0
dep(ft::DeepFT) = dep(ft.left)

eltype(::FingerTree{T}) where {T} = T
eltype(::DigitFT{T}) where {T} = T
Base.eltype(::Type{<:FingerTree{T}}) where {T} = T
Base.IteratorEltype(::Type{<:FingerTree}) = Base.HasEltype()
Base.IteratorSize(::Type{<:FingerTree}) = Base.HasLength()


# `len` remains the built-in sequence measure used by indexing. Measured trees
# cache their user-supplied monoidal value alongside it.

len(a) = 1
len(n::NTuple{N,Leaf23}) where {N} = mapreduce(len, +, n)
len(_::Tuple{}) = 0
len(n::NTuple{N,Node23}) where {N} = mapreduce(len, +, n)

len(n::Tree23) = n.len
len(digit::DigitFT) = digit.len
len(_::EmptyFT) = 0

len(deep::DeepFT) = deep.len
len(n::SingleFT) = len(n.a)
length(ft::FingerTree) = len(ft)

isempty(_::EmptyFT) = true
isempty(_::FingerTree) = false

Base.firstindex(::FingerTree) = 1
Base.lastindex(ft::FingerTree) = length(ft)
Base.eachindex(ft::FingerTree) = Base.OneTo(length(ft))
Base.keys(ft::FingerTree) = Base.OneTo(length(ft))
Base.copy(ft::FingerTree) = ft
Base.empty(::FingerTree{T}) where {T} = EmptyFT{T}()
Base.first(ft::FingerTree) = ft[firstindex(ft)]
Base.last(ft::FingerTree) = ft[lastindex(ft)]

function Base.:(==)(left::FingerTree, right::FingerTree)
    length(left) == length(right) || return false
    all(a == b for (a, b) in zip(left, right))
end

width(digit::DigitFT{T,N}) where {T,N} = N
width(n::Tree23) = isnothing(n.c) ? 2 : 3

# ---------------------------------------------------------------------------
# Construction and small representation conversions
# ---------------------------------------------------------------------------

FingerTree(::Type{K}, ft::FingerTree{K}) where {K} = ft
FingerTree(::Type{K}, n::Tree23{K}) where {K} = fingertree(n)
FingerTree(::Type{T}) where {T} = EmptyFT{T}()

function FingerTree(::Type{T}, iterable) where {T}
    ft = EmptyFT{T}()
    for value in iterable
        ft = conjr(ft, convert(T, value))
    end
    ft
end
FingerTree(iterable) = FingerTree(eltype(iterable), iterable)

# Small trees used while rebalancing.

fingertree(_::Tuple{}) = throw(ArgumentError("cannot create an untyped empty finger tree"))
fingertree(a) = SingleFT(a)
fingertree(a, b) = _unchecked_deep(a, b)
fingertree(a, b, c) = _unchecked_deep(_unchecked_digit(a, b), _unchecked_digit(c))
fingertree(a, b, c, d) = _unchecked_deep(_unchecked_digit(a, b), _unchecked_digit(c, d))
fingertree(a, b, c, d, e) = _unchecked_deep(_unchecked_digit(a, b, c), _unchecked_digit(d, e))
fingertree(a, b, c, d, e, f) = _unchecked_deep(_unchecked_digit(a, b, c), _unchecked_digit(d, e, f))
fingertree(a, b, c, d, e, f, g) = _unchecked_deep(_unchecked_digit(a, b, c, d), _unchecked_digit(e, f, g))
fingertree(a, b, c, d, e, f, g, h) = _unchecked_deep(_unchecked_digit(a, b, c, d), _unchecked_digit(e, f, g, h))

toftree(d::FingerTree) = d
function toftree(d::DigitFT{T})::FingerTreeRep{T} where {T}
    fingertree(d.child...)
end
function toftree(d::DLeaf{T,N,Nothing})::FingerTreeRepV{T,Nothing} where {T,N}
    fingertree(d.child...)
end
function toftree(d::DNode{T,N,Nothing})::FingerTreeRepV{T,Nothing} where {T,N}
    fingertree(d.child...)
end
toftree(d::Tree23{T}) where {T} = fingertree(astuple(d)...)
toftree(d::NTuple{1,T}) where {T} = fingertree(d[1])
toftree(d::NTuple{2,T}) where {T} = fingertree(d[1], d[2])
toftree(d::NTuple{3,T}) where {T} = fingertree(d...)
toftree(d::NTuple{4,T}) where {T} = fingertree(d...)

astuple(n::Tree23) = isnothing(n.c) ? (n.a, n.b) : (n.a, n.b, something(n.c))
astuple(d::DigitFT) = d.child

# ---------------------------------------------------------------------------
# End operations
# ---------------------------------------------------------------------------

conjl(a, digit::DigitFT1{T}) where {T} = _unchecked_digit(a, digit.child[1])
conjl(a, digit::DigitFT2{T}) where {T} = _unchecked_digit(a, digit.child[1], digit.child[2])
conjl(a, digit::DigitFT3{T}) where {T} = _unchecked_digit(a, digit.child...)

conjr(digit::DigitFT1{T}, a) where {T} = _unchecked_digit(digit.child[1], a)
conjr(digit::DigitFT2{T}, a) where {T} = _unchecked_digit(digit.child[1], digit.child[2], a)
conjr(digit::DigitFT3{T}, a) where {T} = _unchecked_digit(digit.child..., a)

# Preserve the digit kind and cached-value parameter on the recursive hot path.
@inline conjl(a::T, d::DLeaf{T,1,Nothing}) where {T} = _dleaf(_NO_MEASURE, (a, d.child[1]))
@inline conjl(a::T, d::DLeaf{T,2,Nothing}) where {T} = _dleaf(_NO_MEASURE, (a, d.child[1], d.child[2]))
@inline conjl(a::T, d::DLeaf{T,3,Nothing}) where {T} = _dleaf(_NO_MEASURE, (a, d.child...))
@inline conjl(a::Tree23RepV{T,Nothing}, d::DNode{T,1,Nothing}) where {T} = _dnode_cached(_NO_MEASURE, (a, d.child[1]))
@inline conjl(a::Tree23RepV{T,Nothing}, d::DNode{T,2,Nothing}) where {T} = _dnode_cached(_NO_MEASURE, (a, d.child[1], d.child[2]))
@inline conjl(a::Tree23RepV{T,Nothing}, d::DNode{T,3,Nothing}) where {T} = _dnode_cached(_NO_MEASURE, (a, d.child...))

@inline conjr(d::DLeaf{T,1,Nothing}, a::T) where {T} = _dleaf(_NO_MEASURE, (d.child[1], a))
@inline conjr(d::DLeaf{T,2,Nothing}, a::T) where {T} = _dleaf(_NO_MEASURE, (d.child[1], d.child[2], a))
@inline conjr(d::DLeaf{T,3,Nothing}, a::T) where {T} = _dleaf(_NO_MEASURE, (d.child..., a))
@inline conjr(d::DNode{T,1,Nothing}, a::Tree23RepV{T,Nothing}) where {T} = _dnode_cached(_NO_MEASURE, (d.child[1], a))
@inline conjr(d::DNode{T,2,Nothing}, a::Tree23RepV{T,Nothing}) where {T} = _dnode_cached(_NO_MEASURE, (d.child[1], d.child[2], a))
@inline conjr(d::DNode{T,3,Nothing}, a::Tree23RepV{T,Nothing}) where {T} = _dnode_cached(_NO_MEASURE, (d.child..., a))


# Direct digit tails/inits avoid tuple slicing in the pop hot path.
@inline _tail_digit(d::DigitFT{T,2}) where {T} = _unchecked_digit(d.child[2])
@inline _tail_digit(d::DigitFT{T,3}) where {T} = _unchecked_digit(d.child[2], d.child[3])
@inline _tail_digit(d::DigitFT{T,4}) where {T} = _unchecked_digit(d.child[2], d.child[3], d.child[4])

@inline _init_digit(d::DigitFT{T,2}) where {T} = _unchecked_digit(d.child[1])
@inline _init_digit(d::DigitFT{T,3}) where {T} = _unchecked_digit(d.child[1], d.child[2])
@inline _init_digit(d::DigitFT{T,4}) where {T} = _unchecked_digit(d.child[1], d.child[2], d.child[3])

splitl(digit::DigitFT{T,2}) where {T} = digit.child[1], _tail_digit(digit)
splitl(digit::DigitFT{T,3}) where {T} = digit.child[1], _tail_digit(digit)
splitl(digit::DigitFT{T,4}) where {T} = digit.child[1], _tail_digit(digit)

splitr(digit::DigitFT{T,2}) where {T} = _init_digit(digit), digit.child[2]
splitr(digit::DigitFT{T,3}) where {T} = _init_digit(digit), digit.child[3]
splitr(digit::DigitFT{T,4}) where {T} = _init_digit(digit), digit.child[4]

# ---------------------------------------------------------------------------
# Indexing
# ---------------------------------------------------------------------------

# Indexing is read-only, so keep the recursive representation out of the call
# stack. Bounds are checked once at the public boundary; the internal descent
# then follows cached measures through the finger-tree and 2-3-tree spines.

@inline function _index_leaf(n::Leaf23{T,V}, i::Int)::T where {T,V}
    j = len(n.a)
    i <= j && return n.a
    i -= j

    j = len(n.b)
    i <= j && return n.b
    i -= j

    c = n.c
    !isnothing(c) && i <= len(something(c)) && return something(c)
    throw(BoundsError())
end

@inline function _index_tree23(node::Tree23RepV{T,V}, i::Int)::T where {T,V}
    while node isa Node23{T,V}
        n = node::Node23{T,V}

        j = len(n.a)
        if i <= j
            node = n.a
            continue
        end
        i -= j

        j = len(n.b)
        if i <= j
            node = n.b
            continue
        end
        i -= j

        c = n.c
        if !isnothing(c) && i <= len(something(c))
            node = something(c)
            continue
        end
        throw(BoundsError())
    end

    _index_leaf(node::Leaf23{T,V}, i)
end

@inline function _index_digit(d::DLeaf{T,N}, i::Int)::T where {T,N}
    # Leaf digits contain sequence elements directly. In the present measure,
    # each element has unit weight, so the local weighted index is its slot.
    @boundscheck 1 <= i <= N || throw(BoundsError())
    @inbounds d.child[i]
end

@inline function _index_digit(d::DNode{T,N}, i::Int)::T where {T,N}
    @inbounds for k in 1:N
        child = d.child[k]
        j = len(child)
        if i <= j
            return _index_tree23(child, i)
        end
        i -= j
    end
    throw(BoundsError())
end

@inline function _index_fingertree(ft::FingerTreeRepV{T,V}, i::Int)::T where {T,V}
    tree = ft
    while true
        if tree isa SingleFT{T,V}
            child = (tree::SingleFT{T,V}).a
            if child isa Tree23{T}
                return _index_tree23(child::Tree23RepV{T,V}, i)
            end
            i == 1 || throw(BoundsError())
            return child::T
        elseif tree isa DeepFT{T,V}
            deep = tree::DeepFT{T,V}

            j = len(deep.left)
            if i <= j
                return _index_digit(deep.left, i)
            end
            i -= j

            j = len(deep.succ)
            if i <= j
                tree = deep.succ
                continue
            end
            i -= j

            return _index_digit(deep.right, i)
        end

        throw(BoundsError())
    end
end

function Base.getindex(d::DigitFT{T}, i::Integer)::T where {T}
    index = Int(i)
    1 <= index <= len(d) || throw(BoundsError(d, i))
    _index_digit(d, index)
end

function Base.getindex(d::DLeaf{T,N,V}, i::Integer)::T where {T,N,V}
    index = Int(i)
    1 <= index <= len(d) || throw(BoundsError(d, i))
    _index_digit(d, index)
end
function Base.getindex(d::DNode{T,N,V}, i::Integer)::T where {T,N,V}
    index = Int(i)
    1 <= index <= len(d) || throw(BoundsError(d, i))
    _index_digit(d, index)
end

function Base.getindex(n::Tree23{T}, i::Integer)::T where {T}
    index = Int(i)
    1 <= index <= len(n) || throw(BoundsError(n, i))
    _index_tree23(n::Tree23Rep{T}, index)
end

function Base.getindex(n::Leaf23{T,V}, i::Integer)::T where {T,V}
    index = Int(i)
    1 <= index <= len(n) || throw(BoundsError(n, i))
    _index_tree23(n, index)
end
function Base.getindex(n::Node23{T,V}, i::Integer)::T where {T,V}
    index = Int(i)
    1 <= index <= len(n) || throw(BoundsError(n, i))
    _index_tree23(n, index)
end

function Base.getindex(ft::FingerTree{T}, i::Integer)::T where {T}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    _index_fingertree(ft::FingerTreeRep{T}, index)
end

function Base.getindex(ft::SingleFT{T,V}, i::Integer)::T where {T,V}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    _index_fingertree(ft, index)
end
function Base.getindex(ft::DeepFT{T,V}, i::Integer)::T where {T,V}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    _index_fingertree(ft, index)
end

conjl(a::T, _::EmptyFT{T}) where {T} = SingleFT(a)
conjr(_::EmptyFT{T}, a::T) where {T} = SingleFT(a)

conjl(a::Tree23{T}, _::EmptyFT{T}) where {T} = SingleFT(a)
conjr(_::EmptyFT{T}, a::Tree23{T}) where {T} = SingleFT(a)

conjl(a, single::SingleFT{K}) where {K} = _unchecked_deep(a, EmptyFT{K}(), single.a)
conjr(single::SingleFT{K}, a) where {K} = _unchecked_deep(single.a, EmptyFT{K}(), a)

# Public pops operate at the leaf level.  Recursive middle-tree pops operate on
# Tree23 values.  Keeping these paths separate avoids SplitValue union payloads
# and generic digit conversion during replenishment.

@inline function _viewl_leaf(single::SingleFT{T,Nothing})::LeafLeftView{T,Nothing} where {T}
    LeafLeftView{T,Nothing}(single.a::T, EmptyFT{T}())
end

@inline function _viewr_leaf(single::SingleFT{T,Nothing})::LeafRightView{T,Nothing} where {T}
    LeafRightView{T,Nothing}(EmptyFT{T}(), single.a::T)
end

function _viewl_node(single::SingleFT{T,Nothing})::NodeLeftView{T,Nothing} where {T}
    NodeLeftView{T,Nothing}(single.a::Tree23RepV{T,Nothing}, EmptyFT{T}())
end

function _viewr_node(single::SingleFT{T,Nothing})::NodeRightView{T,Nothing} where {T}
    NodeRightView{T,Nothing}(EmptyFT{T}(), single.a::Tree23RepV{T,Nothing})
end

function _conjl_deep(a::T, ft::DeepFT{T,Nothing}, left::DLeaf{T,N,Nothing})::DeepFT{T,Nothing} where {T,N}
    if N < 4
        _deep(_NO_MEASURE, conjl(a, left), ft.succ, ft.right)
    else
        f = _leaf23(_NO_MEASURE, left.child[2], left.child[3], left.child[4])
        newleft = _dleaf(_NO_MEASURE, (a, left.child[1]))
        _deep(_NO_MEASURE, newleft, conjl(f, ft.succ), ft.right)
    end
end

function _conjl_deep(a::Tree23RepV{T,Nothing}, ft::DeepFT{T,Nothing}, left::DNode{T,N,Nothing})::DeepFT{T,Nothing} where {T,N}
    if N < 4
        _deep(_NO_MEASURE, conjl(a, left), ft.succ, ft.right)
    else
        f = _node23_cached(_NO_MEASURE, left.child[2], left.child[3], left.child[4])
        newleft = _dnode_cached(_NO_MEASURE, (a, left.child[1]))
        _deep(_NO_MEASURE, newleft, conjl(f, ft.succ), ft.right)
    end
end

function conjl(a, ft::DeepFT{T,Nothing})::DeepFT{T,Nothing} where {T}
    left = ft.left
    left isa DLeaf{T} ? _conjl_deep(a::T, ft, left) :
        _conjl_deep(a::Tree23RepV{T,Nothing}, ft, left::DNode{T})
end

function _conjr_deep(ft::DeepFT{T,Nothing}, right::DLeaf{T,N,Nothing}, a::T)::DeepFT{T,Nothing} where {T,N}
    if N < 4
        _deep(_NO_MEASURE, ft.left, ft.succ, conjr(right, a))
    else
        f = _leaf23(_NO_MEASURE, right.child[1], right.child[2], right.child[3])
        newright = _dleaf(_NO_MEASURE, (right.child[4], a))
        _deep(_NO_MEASURE, ft.left, conjr(ft.succ, f), newright)
    end
end


function _conjr_deep(ft::DeepFT{T,Nothing}, right::DNode{T,N,Nothing}, a::Tree23RepV{T,Nothing})::DeepFT{T,Nothing} where {T,N}
    if N < 4
        _deep(_NO_MEASURE, ft.left, ft.succ, conjr(right, a))
    else
        f = _node23_cached(_NO_MEASURE, right.child[1], right.child[2], right.child[3])
        newright = _dnode_cached(_NO_MEASURE, (right.child[4], a))
        _deep(_NO_MEASURE, ft.left, conjr(ft.succ, f), newright)
    end
end

function conjr(ft::DeepFT{T,Nothing}, a)::DeepFT{T,Nothing} where {T}
    right = ft.right
    right isa DLeaf{T} ? _conjr_deep(ft, right, a::T) :
        _conjr_deep(ft, right::DNode{T}, a::Tree23RepV{T,Nothing})
end

function _viewl_leaf(ft::DeepFT{T,Nothing}, left::DLeaf{T,N,Nothing})::LeafLeftView{T,Nothing} where {T,N}
    a = left.child[1]
    if N > 1
        return LeafLeftView{T,Nothing}(a, _unchecked_deep(_tail_digit(left), ft.succ, ft.right))
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return LeafLeftView{T,Nothing}(a, toftree(ft.right))
    end

    s = _viewl_node(middle)
    # The first middle level of a leaf tree contains Leaf23 values.
    node = s.value::Leaf23{T,Nothing}
    return LeafLeftView{T,Nothing}(a, _unchecked_deep(digit(node), s.rest, ft.right))
end

function _viewr_leaf(ft::DeepFT{T,Nothing}, right::DLeaf{T,N,Nothing})::LeafRightView{T,Nothing} where {T,N}
    a = right.child[N]
    if N > 1
        return LeafRightView{T,Nothing}(_unchecked_deep(ft.left, ft.succ, _init_digit(right)), a)
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return LeafRightView{T,Nothing}(toftree(ft.left), a)
    end

    s = _viewr_node(middle)
    # The first middle level of a leaf tree contains Leaf23 values.
    node = s.value::Leaf23{T,Nothing}
    return LeafRightView{T,Nothing}(_unchecked_deep(ft.left, s.rest, digit(node)), a)
end

function _viewl_node(ft::DeepFT{T,Nothing}, left::DNode{T,N,Nothing})::NodeLeftView{T,Nothing} where {T,N}
    a = left.child[1]
    if N > 1
        return NodeLeftView{T,Nothing}(a, _unchecked_deep(_tail_digit(left), ft.succ, ft.right))
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return NodeLeftView{T,Nothing}(a, toftree(ft.right))
    end

    s = _viewl_node(middle)
    # A nonempty successor of a node-level tree is at least two levels deep,
    # so the borrowed value is necessarily a Node23 rather than a Leaf23.
    node = s.value::Node23{T,Nothing}
    return NodeLeftView{T,Nothing}(a, _unchecked_deep(digit(node), s.rest, ft.right))
end

function _viewr_node(ft::DeepFT{T,Nothing}, right::DNode{T,N,Nothing})::NodeRightView{T,Nothing} where {T,N}
    a = right.child[N]
    if N > 1
        return NodeRightView{T,Nothing}(_unchecked_deep(ft.left, ft.succ, _init_digit(right)), a)
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return NodeRightView{T,Nothing}(toftree(ft.left), a)
    end

    s = _viewr_node(middle)
    # Symmetric to _viewl_node: recursive borrowing here always yields Node23.
    node = s.value::Node23{T,Nothing}
    return NodeRightView{T,Nothing}(_unchecked_deep(ft.left, s.rest, digit(node)), a)
end

@inline function _viewl_leaf(ft::DeepFT{T,Nothing})::LeafLeftView{T,Nothing} where {T}
    _viewl_leaf(ft, ft.left)
end

@inline function _viewr_leaf(ft::DeepFT{T,Nothing})::LeafRightView{T,Nothing} where {T}
    _viewr_leaf(ft, ft.right)
end

function _viewl_node(ft::DeepFT{T,Nothing})::NodeLeftView{T,Nothing} where {T}
    _viewl_node(ft, ft.left)
end

function _viewr_node(ft::DeepFT{T,Nothing})::NodeRightView{T,Nothing} where {T}
    _viewr_node(ft, ft.right)
end

splitl(ft::EmptyFT) = throw(BoundsError(ft))
splitr(ft::EmptyFT) = throw(BoundsError(ft))

function splitl(single::SingleFT{T}) where {T}
    s = _viewl_leaf(single)
    s.value, s.rest
end

function splitr(single::SingleFT{T}) where {T}
    s = _viewr_leaf(single)
    s.rest, s.value
end

function splitl(ft::DeepFT{T}) where {T}
    s = _viewl_leaf(ft)
    s.value, s.rest
end

function splitr(ft::DeepFT{T}) where {T}
    s = _viewr_leaf(ft)
    s.rest, s.value
end

# ---------------------------------------------------------------------------
# Splitting and persistent update
# ---------------------------------------------------------------------------

const DigitFragment{T,V} = Union{Nothing,DigitFTRepV{T,V}}

struct DigitSplit{T,V}
    left::DigitFragment{T,V}
    value::SplitValue{T,V}
    right::DigitFragment{T,V}
end

struct TreeSplit{T,V}
    left::FingerTreeRepV{T,V}
    value::SplitValue{T,V}
    right::FingerTreeRepV{T,V}
end

struct Tree23Split{T,V}
    left::DigitFragment{T,V}
    value::SplitValue{T,V}
    right::DigitFragment{T,V}
end

# A split fragment has at most three children.  Represent nonempty fragments
# immediately as digits and package the result in one concrete return type.
function split(d::DigitFT{T,1}, i) where {T}
    a = d.child[1]
    i <= len(a) && return DigitSplit{T,Nothing}(nothing, a, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,2}, i) where {T}
    a, b = d.child
    j = len(a)
    i <= j && return DigitSplit{T,Nothing}(nothing, a, _unchecked_digit(b))
    i -= j
    i <= len(b) && return DigitSplit{T,Nothing}(_unchecked_digit(a), b, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,3}, i) where {T}
    a, b, c = d.child
    j = len(a)
    i <= j && return DigitSplit{T,Nothing}(nothing, a, _unchecked_digit(b, c))
    i -= j
    j = len(b)
    i <= j && return DigitSplit{T,Nothing}(_unchecked_digit(a), b, _unchecked_digit(c))
    i -= j
    i <= len(c) && return DigitSplit{T,Nothing}(_unchecked_digit(a, b), c, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,4}, i) where {T}
    a, b, c, e = d.child
    j = len(a)
    i <= j && return DigitSplit{T,Nothing}(nothing, a, _unchecked_digit(b, c, e))
    i -= j
    j = len(b)
    i <= j && return DigitSplit{T,Nothing}(_unchecked_digit(a), b, _unchecked_digit(c, e))
    i -= j
    j = len(c)
    i <= j && return DigitSplit{T,Nothing}(_unchecked_digit(a, b), c, _unchecked_digit(e))
    i -= j
    i <= len(e) && return DigitSplit{T,Nothing}(_unchecked_digit(a, b, c), e, nothing)
    throw(BoundsError())
end

function _split23(n::Leaf23{T,Nothing}, i::Int)::Tree23Split{T,Nothing} where {T}
    if isnothing(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T,Nothing}(nothing, n.a, _unchecked_digit(n.b))
        i -= j
        i <= len(n.b) && return Tree23Split{T,Nothing}(_unchecked_digit(n.a), n.b, nothing)
    else
        c = something(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T,Nothing}(nothing, n.a, _unchecked_digit(n.b, c))
        i -= j
        j = len(n.b)
        i <= j && return Tree23Split{T,Nothing}(_unchecked_digit(n.a), n.b, _unchecked_digit(c))
        i -= j
        i <= len(c) && return Tree23Split{T,Nothing}(_unchecked_digit(n.a, n.b), c, nothing)
    end
    throw(BoundsError())
end

function _split23(n::Node23{T,Nothing}, i::Int)::Tree23Split{T,Nothing} where {T}
    if isnothing(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T,Nothing}(nothing, n.a, _unchecked_digit(n.b))
        i -= j
        i <= len(n.b) && return Tree23Split{T,Nothing}(_unchecked_digit(n.a), n.b, nothing)
    else
        c = something(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T,Nothing}(nothing, n.a, _unchecked_digit(n.b, c))
        i -= j
        j = len(n.b)
        i <= j && return Tree23Split{T,Nothing}(_unchecked_digit(n.a), n.b, _unchecked_digit(c))
        i -= j
        i <= len(c) && return Tree23Split{T,Nothing}(_unchecked_digit(n.a, n.b), c, nothing)
    end
    throw(BoundsError())
end


function collect(tree::FingerTree)
    values = Vector{eltype(tree)}(undef, length(tree))
    i = 1
    for value in tree
        @inbounds values[i] = value
        i += 1
    end
    values
end

const NonEmptyFT{T,V} = Union{SingleFT{T,V},DeepFT{T,V}}

_deepl(::Nothing, ::EmptyFT{T}, right::DigitFTRepV{T,Nothing}) where {T} = toftree(right)
function _deepl(::Nothing, ft::NonEmptyFT{T,Nothing}, right::DigitFTRepV{T,Nothing}) where {T}
    s = _viewl_node(ft)
    _unchecked_deep(digit(s.value), s.rest, right)
end
_deepl(left::DigitFTRepV{T,Nothing}, ft::FingerTreeRepV{T,Nothing}, right::DigitFTRepV{T,Nothing}) where {T} =
    _unchecked_deep(left, ft, right)

function deepl(
    left::DigitFragment{T,Nothing},
    middle::FingerTreeRepV{T,Nothing},
    right::DigitFTRepV{T,Nothing},
)::FingerTreeRepV{T,Nothing} where {T}
    _deepl(left, middle, right)
end

_deepr(left::DigitFTRepV{T,Nothing}, ::EmptyFT{T}, ::Nothing) where {T} = toftree(left)
function _deepr(left::DigitFTRepV{T,Nothing}, ft::NonEmptyFT{T,Nothing}, ::Nothing) where {T}
    s = _viewr_node(ft)
    _unchecked_deep(left, s.rest, digit(s.value))
end
_deepr(left::DigitFTRepV{T,Nothing}, ft::FingerTreeRepV{T,Nothing}, right::DigitFTRepV{T,Nothing}) where {T} =
    _unchecked_deep(left, ft, right)

function deepr(
    left::DigitFTRepV{T,Nothing},
    middle::FingerTreeRepV{T,Nothing},
    right::DigitFragment{T,Nothing},
)::FingerTreeRepV{T,Nothing} where {T}
    _deepr(left, middle, right)
end

function _split(ft::EmptyFT{T}, i::Int)::TreeSplit{T,Nothing} where {T}
    throw(BoundsError(ft, i))
end

function _split(ft::SingleFT{T,Nothing}, i::Int)::TreeSplit{T,Nothing} where {T}
    empty = EmptyFT{T}()
    TreeSplit{T,Nothing}(empty, ft.a, empty)
end

function _split(ft::DeepFT{T,Nothing}, i::Int)::TreeSplit{T,Nothing} where {T}
    j = len(ft.left)
    if i <= j
        s = split(ft.left, i)
        left = isnothing(s.left) ? EmptyFT{T}() : toftree(something(s.left))
        return TreeSplit{T,Nothing}(left, s.value, deepl(s.right, ft.succ, ft.right))
    end
    i -= j
    j = len(ft.succ)
    if i <= j
        s = _split(ft.succ, i)
        ml = s.left
        xs = s.value
        mr = s.right
        i -= len(ml)
        ns = isa(xs, T) ? Tree23Split{T,Nothing}(nothing, xs, nothing) : _split23(xs, i)
        left = deepr(ft.left, ml, ns.left)
        right = deepl(ns.right, mr, ft.right)
        return TreeSplit{T,Nothing}(left, ns.value, right)
    end
    i -= j
    j = len(ft.right)
    if i <= j
        s = split(ft.right, i)
        right = isnothing(s.right) ? EmptyFT{T}() : toftree(something(s.right))
        return TreeSplit{T,Nothing}(deepr(ft.left, ft.succ, s.left), s.value, right)
    end
    throw(BoundsError())
end

function split(ft::FingerTree{T}, i::Integer) where {T}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    s = _split(ft, index)
    s.left, s.value::T, s.right
end

function _assoc(d::DLeaf{T,N}, value::T, i::Int) where {T,N}
    for k in 1:N
        j = len(d.child[k])
        if i <= j
            children = ntuple(m -> m == k ? value : d.child[m], Val(N))
            return DLeaf(children...)
        end
        i -= j
    end
    throw(BoundsError())
end

function _assoc(d::DNode{T,N}, value::T, i::Int) where {T,N}
    for k in 1:N
        j = len(d.child[k])
        if i <= j
            updated = _assoc(d.child[k], value, i)
            children = ntuple(m -> m == k ? updated : d.child[m], Val(N))
            return _unchecked_digit(children...)
        end
        i -= j
    end
    throw(BoundsError())
end

function _assoc(n::Leaf23{T}, value::T, i::Int) where {T}
    c = n.c

    j = len(n.a)
    if i <= j
        return isnothing(c) ? _unchecked_tree23(value, n.b) : _unchecked_tree23(value, n.b, something(c))
    end
    i -= j

    j = len(n.b)
    if i <= j
        return isnothing(c) ? _unchecked_tree23(n.a, value) : _unchecked_tree23(n.a, value, something(c))
    end

    if !isnothing(c)
        i -= j
        i <= len(something(c)) && return _unchecked_tree23(n.a, n.b, value)
    end

    throw(BoundsError())
end

function _assoc(n::Node23{T}, value::T, i::Int) where {T}
    c = n.c

    j = len(n.a)
    if i <= j
        updated = _assoc(n.a, value, i)
        return isnothing(c) ? _unchecked_tree23(updated, n.b) : _unchecked_tree23(updated, n.b, something(c))
    end
    i -= j

    j = len(n.b)
    if i <= j
        updated = _assoc(n.b, value, i)
        return isnothing(c) ? _unchecked_tree23(n.a, updated) : _unchecked_tree23(n.a, updated, something(c))
    end

    if !isnothing(c)
        i -= j
        child = something(c)
        if i <= len(child)
            return _unchecked_tree23(n.a, n.b, _assoc(child, value, i))
        end
    end

    throw(BoundsError())
end

_assoc(ft::EmptyFT{T}, ::T, i::Int) where {T} = throw(BoundsError(ft, i))

function _assoc(ft::SingleFT{T}, value::T, i::Int) where {T}
    child = ft.a
    if child isa Tree23{T}
        return SingleFT(_assoc(child::Tree23Rep{T}, value, i))
    end
    return SingleFT(value)
end

function _assoc(ft::DeepFT{T}, value::T, i::Int) where {T}
    j = len(ft.left)
    if i <= j
        return _unchecked_deep(_assoc(ft.left, value, i), ft.succ, ft.right)
    end
    i -= j

    j = len(ft.succ)
    if i <= j
        return _unchecked_deep(ft.left, _assoc(ft.succ, value, i), ft.right)
    end
    i -= j

    j = len(ft.right)
    if i <= j
        return _unchecked_deep(ft.left, ft.succ, _assoc(ft.right, value, i))
    end

    throw(BoundsError())
end

function assoc(ft::FingerTree{T}, value::T, i::Integer) where {T}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    _assoc(ft, value, index)
end

function Base.getindex(ft::FingerTree{T}, range::UnitRange{<:Integer}) where {T}
    isempty(range) && return EmptyFT{T}()

    first_index = Int(first(range))
    last_index = Int(last(range))
    1 <= first_index <= last_index <= length(ft) || throw(BoundsError(ft, range))

    _, first_value, suffix = split(ft, first_index)
    candidate = conjl(first_value, suffix)
    prefix, last_value, _ = split(candidate, last_index - first_index + 1)
    conjr(prefix, last_value)
end

# ---------------------------------------------------------------------------
# Reduction and traversal
# ---------------------------------------------------------------------------

_reduce(op::Function, v, a) = op(v, a)
_reduce(::Function, v, ::EmptyFT) = v
_reduce(op::Function, v, t::SingleFT) = _reduce(op, v, t.a)
function _reduce(op::Function, v, d::DigitFT)
    for k in 1:width(d)
        v = _reduce(op, v, d.child[k])
    end
    v
end
function _reduce(op::Function, v, n::Tree23)
    for x in astuple(n)
        v = _reduce(op, v, x)
    end
    v
end
function _reduce(op::Function, v, ft::DeepFT)
    v = _reduce(op, v, ft.left)
    v = _reduce(op, v, ft.succ)
    _reduce(op, v, ft.right)
end

function Base.reduce(op::Function, ft::FingerTree)
    if isempty(ft)
        return reduce(op, Vector{eltype(ft)}())
    end
    x, rest = splitl(ft)
    _reduce(op, x, rest)
end

traverse(op::Function, a, i) = (op(a, i); i + 1)
traverse(::Function, ::EmptyFT, i) = i
traverse(op::Function, ft::SingleFT, i) = traverse(op, ft.a, i)

function traverse(op::Function, n::DigitFT, i)
    for k in 1:width(n)
        i = traverse(op, n.child[k], i)
    end
    i
end
function traverse(op::Function, n::Tree23, i)
    i = traverse(op, n.a, i)
    i = traverse(op, n.b, i)
    !isnothing(n.c) && (i = traverse(op, something(n.c), i))
    i
end
function traverse(op::Function, ft::DeepFT, i)
    i = traverse(op, ft.left, i)
    i = traverse(op, ft.succ, i)
    traverse(op, ft.right, i)
end
traverse(op, ft) = (traverse(op, ft, 1);)

# ---------------------------------------------------------------------------
# Iteration
# ---------------------------------------------------------------------------

Base.iterate(::EmptyFT) = nothing
@inline function Base.iterate(ft::SingleFT{T,V}) where {T,V}
    state = IterationState{T,V}(TraversalBranch{T,V}[], Int[], T[], 1)
    sizehint!(state.branches, 16)
    sizehint!(state.next, 16)
    sizehint!(state.pending, 4)
    _descend!(state, ft)
    _iterate(state)
end
@inline function Base.iterate(ft::DeepFT{T,V}) where {T,V}
    state = IterationState{T,V}(TraversalBranch{T,V}[], Int[], T[], 1)
    sizehint!(state.branches, 16)
    sizehint!(state.next, 16)
    sizehint!(state.pending, 4)
    _descend!(state, ft)
    _iterate(state)
end

@inline Base.iterate(::FingerTree{T}, state::IterationState{T,V}) where {T,V} = _iterate(state)

_descend!(::IterationState, ::EmptyFT) = nothing

function _descend!(state::IterationState{T,V}, branch::TraversalBranch{T,V}) where {T,V}
    push!(state.branches, branch)
    push!(state.next, 1)
    nothing
end

function _descend!(state::IterationState{T,V}, single::SingleFT{T,V}) where {T,V}
    child = single.a
    if child isa Tree23{T}
        _descend!(state, child::Tree23RepV{T,V})
    else
        _descend!(state, child::T)
    end
end

function _descend!(state::IterationState{T,V}, leaf::DLeaf{T,N,V}) where {T,N,V}
    empty!(state.pending)
    for child in leaf.child
        push!(state.pending, child)
    end
    state.pending_next = 1
    nothing
end

function _descend!(state::IterationState{T,V}, leaf::Leaf23{T,V}) where {T,V}
    empty!(state.pending)
    push!(state.pending, leaf.a)
    push!(state.pending, leaf.b)
    !isnothing(leaf.c) && push!(state.pending, something(leaf.c))
    state.pending_next = 1
    nothing
end

function _descend!(state::IterationState{T,V}, value::T) where {T,V}
    empty!(state.pending)
    push!(state.pending, value)
    state.pending_next = 1
    nothing
end

@inline function _iterate(state::IterationState{T,V}) where {T,V}
    while true
        if state.pending_next <= length(state.pending)
            value = state.pending[state.pending_next]
            state.pending_next += 1
            return value, state
        end

        isempty(state.branches) && return nothing

        branch = state.branches[end]
        next = state.next[end]

        if branch isa DeepFT{T,V}
            if next == 1
                state.next[end] = 2
                child = branch.left
                child isa DLeaf{T} ? _descend!(state, child) :
                    _descend!(state, child::DNode{T})
            elseif next == 2
                state.next[end] = 3
                child = branch.succ
                if child isa EmptyFT{T}
                    nothing
                elseif child isa SingleFT{T,V}
                    _descend!(state, child)
                else
                    _descend!(state, child::DeepFT{T,V})
                end
            else
                pop!(state.branches)
                pop!(state.next)
                child = branch.right
                child isa DLeaf{T} ? _descend!(state, child) :
                    _descend!(state, child::DNode{T})
            end
        elseif branch isa DNode
            if next == width(branch)
                pop!(state.branches)
                pop!(state.next)
            else
                state.next[end] = next + 1
            end
            child = branch.child[next]
            child isa Leaf23{T,V} ? _descend!(state, child) :
                _descend!(state, child::Node23{T,V})
        else
            if next == width(branch)
                pop!(state.branches)
                pop!(state.next)
            else
                state.next[end] = next + 1
            end
            child = next == 1 ? branch.a : next == 2 ? branch.b : something(branch.c)
            child isa Leaf23{T,V} ? _descend!(state, child) :
                _descend!(state, child::Node23{T,V})
        end
    end
end

# Traverse the representation itself while reporting structural depth.
travstruct(op::Function, a, d) = (op(a, d); d)
travstruct(::Function, ::EmptyFT, d) = d
travstruct(op::Function, ft::SingleFT, d) = travstruct(op, ft.a, d)
function travstruct(op::Function, n::DigitFT{T}, d) where {T}
    d2 = travstruct(op, n.child[1], d)
    for k in 2:width(n)
        @assert d2 == travstruct(op, n.child[k], d)
    end
    d2
end
function travstruct(op::Function, ft::DeepFT, d)
    d2 = travstruct(op, ft.left, d)
    @assert d2 == travstruct(op, ft.succ, d + 1) - 1 == travstruct(op, ft.right, d)
    d2
end
travstruct(op, ft) = travstruct(op, ft, 1)

function conjlall(t)
    ft = t[end]
    for i in length(t)-1:-1:1
        ft = conjl(t[i], ft)
    end
    ft
end
function conjrall(t)
    ft = t[1]
    for x in t[2:end]
        ft = conjr(ft, x)
    end
    ft
end

# ---------------------------------------------------------------------------
# Concatenation
# ---------------------------------------------------------------------------

app3(l::EmptyFT{T}, ::Tuple{}, ::EmptyFT{T}) where {T} = l
app3(::EmptyFT{T}, ::Tuple{}, r::SingleFT{T}) where {T} = r
app3(::EmptyFT{T}, ::Tuple{}, r::DeepFT{T}) where {T} = r
app3(l::SingleFT{T}, ::Tuple{}, ::EmptyFT{T}) where {T} = l
app3(l::DeepFT{T}, ::Tuple{}, ::EmptyFT{T}) where {T} = l
app3(l::SingleFT, ts, r::SingleFT) = fingertree(l.a, ts..., r.a)
app3(::EmptyFT, ts, r::EmptyFT) = fingertree(ts...)
app3(::EmptyFT, ts, r::SingleFT) = fingertree(ts..., r.a)
app3(l::SingleFT, ts, ::EmptyFT) = fingertree(l.a, ts...)
app3(::EmptyFT, ts, r) = conjlall(tuple(ts..., r))
app3(l, ts, ::EmptyFT) = conjrall(tuple(l, ts...))
app3(x::SingleFT, ts, r) = conjl(x.a, conjlall(tuple(ts..., r)))
app3(l, ts, x::SingleFT) = conjr(conjrall(tuple(l, ts...)), x.a)


nodes(a,b) = (_unchecked_tree23(a, b),)
nodes(a,b,c) = (_unchecked_tree23(a,b,c),)
nodes(a,b,c,d) = (_unchecked_tree23(a, b), _unchecked_tree23(c,d))
nodes(a,b,c,xs...) = tuple(_unchecked_tree23(a,b,c), nodes(xs...)...)

app3(l::DeepFT, ts, r::DeepFT) =
    _unchecked_deep(l.left, app3(l.succ, nodes(l.right.child..., ts..., r.left.child...), r.succ), r.right)
concat(l::FingerTree{T}, r::FingerTree{T}) where {T} =
    app3(l, (), r)::FingerTreeRep{T}
concat(l::FingerTree{T}, x, r::FingerTree{T}) where {T} =
    app3(l, (x,), r)::FingerTreeRep{T}

# ---------------------------------------------------------------------------
# Measured wrapper
# ---------------------------------------------------------------------------

const _MeasuredValue{T,V} = Union{T,Tree23RepV{T,V}}
const _MeasuredDigitFragment{T,V} = Union{Nothing,DigitFTRepV{T,V}}

struct _MeasuredSplit{T,V}
    left::FingerTreeRepV{T,V}
    value::_MeasuredValue{T,V}
    right::FingerTreeRepV{T,V}
end

struct _MeasuredNodeSplit{T,V}
    left::_MeasuredDigitFragment{T,V}
    value::_MeasuredValue{T,V}
    right::_MeasuredDigitFragment{T,V}
end

@inline _measured(op::M, root::SingleFT{T,V}) where {T,M,V} =
    MeasuredFingerTree{T,M,V}(op, root)
@inline _measured(op::M, root::DeepFT{T,V}) where {T,M,V} =
    MeasuredFingerTree{T,M,V}(op, root)
@inline _measured(op::M, root::EmptyFT{T}, ::Type{V}) where {T,M,V} =
    MeasuredFingerTree{T,M,V}(op, root)
@inline _measured(op::M, root::FingerTreeRepV{T,V}, ::Type{V}) where {T,M,V} =
    MeasuredFingerTree{T,M,V}(op, root)

_mfingertree(op::_MeasureOp, value) = _single(op, value)
_mfingertree(op::_MeasureOp, a, b) = _unchecked_deep(op, a, b)
_mfingertree(op::_MeasureOp, a, b, c) =
    _unchecked_deep(op, _unchecked_digit(op, a, b), _unchecked_digit(op, c))
_mfingertree(op::_MeasureOp, a, b, c, d) =
    _unchecked_deep(op, _unchecked_digit(op, a, b), _unchecked_digit(op, c, d))

function _mtoftree(op::_MeasureOp, digit::DigitFT)
    _mfingertree(op, digit.child...)
end

@inline _mconjl(op::_MeasureOp, value, ::EmptyFT{T}) where {T} = _single(op, value)
@inline _mconjr(op::_MeasureOp, ::EmptyFT{T}, value) where {T} = _single(op, value)
@inline _mconjl(op::_MeasureOp, value, single::SingleFT{T}) where {T} =
    _unchecked_deep(op, value, EmptyFT{T}(), single.a)
@inline _mconjr(op::_MeasureOp, single::SingleFT{T}, value) where {T} =
    _unchecked_deep(op, single.a, EmptyFT{T}(), value)

function _mconjl(op::_MeasureOp, value, tree::DeepFT{T}) where {T}
    left = tree.left
    if width(left) < 4
        return _unchecked_deep(op, _unchecked_digit(op, value, left.child...), tree.succ, tree.right)
    end
    node = _unchecked_tree23(op, left.child[2], left.child[3], left.child[4])
    _unchecked_deep(
        op,
        _unchecked_digit(op, value, left.child[1]),
        _mconjl(op, node, tree.succ),
        tree.right,
    )
end

function _mconjr(op::_MeasureOp, tree::DeepFT{T}, value) where {T}
    right = tree.right
    if width(right) < 4
        return _unchecked_deep(op, tree.left, tree.succ, _unchecked_digit(op, right.child..., value))
    end
    node = _unchecked_tree23(op, right.child[1], right.child[2], right.child[3])
    _unchecked_deep(
        op,
        tree.left,
        _mconjr(op, tree.succ, node),
        _unchecked_digit(op, right.child[4], value),
    )
end

@inline function _mfragment(op::_MeasureOp, children::Tuple, first::Int, last::Int)
    first > last && return nothing
    values = ntuple(i -> children[first + i - 1], last - first + 1)
    _unchecked_digit(op, values...)
end

function _msplit_digit(op::_MeasureOp, digit::DigitFT{T,N}, i::Int) where {T,N}
    for k in 1:N
        child = digit.child[k]
        if i <= len(child)
            V = typeof(digit.value)
            return _MeasuredNodeSplit{T,V}(
                _mfragment(op, digit.child, 1, k - 1),
                child,
                _mfragment(op, digit.child, k + 1, N),
            )
        end
        i -= len(child)
    end
    throw(BoundsError())
end

function _msplit23(op::_MeasureOp, node::Tree23{T}, i::Int) where {T}
    children = astuple(node)
    N = length(children)
    for k in 1:N
        child = children[k]
        if i <= len(child)
            V = typeof(node.value)
            return _MeasuredNodeSplit{T,V}(
                _mfragment(op, children, 1, k - 1),
                child,
                _mfragment(op, children, k + 1, N),
            )
        end
        i -= len(child)
    end
    throw(BoundsError())
end

function _mviewl_node(op::_MeasureOp, single::SingleFT{T,V}) where {T,V}
    (value=single.a::Tree23RepV{T,V}, rest=EmptyFT{T}())
end

function _mviewl_node(op::_MeasureOp, tree::DeepFT{T,V}) where {T,V}
    left = tree.left::DNode{T}
    value = left.child[1]
    if width(left) > 1
        rest = _unchecked_deep(op, _mfragment(op, left.child, 2, width(left)), tree.succ, tree.right)
        return (value=value, rest=rest)
    end
    if tree.succ isa EmptyFT
        return (value=value, rest=_mtoftree(op, tree.right))
    end
    borrowed = _mviewl_node(op, tree.succ)
    (value=value, rest=_unchecked_deep(op, digit(op, borrowed.value), borrowed.rest, tree.right))
end

function _mviewr_node(op::_MeasureOp, single::SingleFT{T,V}) where {T,V}
    (rest=EmptyFT{T}(), value=single.a::Tree23RepV{T,V})
end

function _mviewr_node(op::_MeasureOp, tree::DeepFT{T,V}) where {T,V}
    right = tree.right::DNode{T}
    N = width(right)
    value = right.child[N]
    if N > 1
        rest = _unchecked_deep(op, tree.left, tree.succ, _mfragment(op, right.child, 1, N - 1))
        return (rest=rest, value=value)
    end
    if tree.succ isa EmptyFT
        return (rest=_mtoftree(op, tree.left), value=value)
    end
    borrowed = _mviewr_node(op, tree.succ)
    (rest=_unchecked_deep(op, tree.left, borrowed.rest, digit(op, borrowed.value)), value=value)
end

function _mdeepl(op::_MeasureOp, left, middle::FingerTree, right::DigitFT)
    if !isnothing(left)
        return _unchecked_deep(op, left, middle, right)
    elseif middle isa EmptyFT
        return _mtoftree(op, right)
    end
    borrowed = _mviewl_node(op, middle)
    _unchecked_deep(op, digit(op, borrowed.value), borrowed.rest, right)
end

function _mdeepr(op::_MeasureOp, left::DigitFT, middle::FingerTree, right)
    if !isnothing(right)
        return _unchecked_deep(op, left, middle, right)
    elseif middle isa EmptyFT
        return _mtoftree(op, left)
    end
    borrowed = _mviewr_node(op, middle)
    _unchecked_deep(op, left, borrowed.rest, digit(op, borrowed.value))
end

function _msplit(op::_MeasureOp, single::SingleFT{T,V}, ::Int) where {T,V}
    empty = EmptyFT{T}()
    _MeasuredSplit{T,V}(empty, single.a, empty)
end

function _msplit(op::_MeasureOp, tree::DeepFT{T,V}, i::Int) where {T,V}
    j = len(tree.left)
    if i <= j
        split = _msplit_digit(op, tree.left, i)
        left = isnothing(split.left) ? EmptyFT{T}() : _mtoftree(op, something(split.left))
        return _MeasuredSplit{T,V}(
            left,
            split.value,
            _mdeepl(op, split.right, tree.succ, tree.right),
        )
    end

    i -= j
    j = len(tree.succ)
    if i <= j
        split = _msplit(op, tree.succ, i)
        i -= len(split.left)
        node_split = split.value isa T ?
            _MeasuredNodeSplit{T,V}(nothing, split.value, nothing) :
            _msplit23(op, split.value, i)
        return _MeasuredSplit{T,V}(
            _mdeepr(op, tree.left, split.left, node_split.left),
            node_split.value,
            _mdeepl(op, node_split.right, split.right, tree.right),
        )
    end

    i -= j
    split = _msplit_digit(op, tree.right, i)
    right = isnothing(split.right) ? EmptyFT{T}() : _mtoftree(op, something(split.right))
    _MeasuredSplit{T,V}(
        _mdeepr(op, tree.left, tree.succ, split.left),
        split.value,
        right,
    )
end

function _massoc(op::_MeasureOp, digit::DLeaf{T,N,V}, value::T, i::Int)::DLeaf{T,N,V} where {T,N,V}
    children = ntuple(k -> k == i ? value : digit.child[k], Val(N))
    _unchecked_digit(op, children...)
end

function _massoc(op::_MeasureOp, digit::DNode{T,N,V}, value::T, i::Int)::DNode{T,N,V} where {T,N,V}
    for k in 1:N
        child = digit.child[k]
        if i <= len(child)
            updated = _massoc(op, child, value, i)::Tree23RepV{T,V}
            children = ntuple(j -> j == k ? updated : digit.child[j], Val(N))
            return _dnode_cached(op, children)
        end
        i -= len(child)
    end
    throw(BoundsError())
end

function _massoc(op::_MeasureOp, node::Leaf23{T,V}, value::T, i::Int)::Leaf23{T,V} where {T,V}
    c = node.c
    i <= len(node.a) && return isnothing(c) ?
        _unchecked_tree23(op, value, node.b) :
        _unchecked_tree23(op, value, node.b, something(c))
    i -= len(node.a)
    i <= len(node.b) && return isnothing(c) ?
        _unchecked_tree23(op, node.a, value) :
        _unchecked_tree23(op, node.a, value, something(c))
    if !isnothing(c)
        i -= len(node.b)
        i <= len(something(c)) && return _unchecked_tree23(op, node.a, node.b, value)
    end
    throw(BoundsError())
end

function _massoc(op::_MeasureOp, node::Node23{T,V}, value::T, i::Int)::Node23{T,V} where {T,V}
    c = node.c
    if i <= len(node.a)
        replacement = _massoc(op, node.a, value, i)::Tree23RepV{T,V}
        return isnothing(c) ? _unchecked_tree23(op, replacement, node.b) :
            _unchecked_tree23(op, replacement, node.b, something(c))
    end
    i -= len(node.a)
    if i <= len(node.b)
        replacement = _massoc(op, node.b, value, i)::Tree23RepV{T,V}
        return isnothing(c) ? _unchecked_tree23(op, node.a, replacement) :
            _unchecked_tree23(op, node.a, replacement, something(c))
    end
    if !isnothing(c)
        i -= len(node.b)
        child = something(c)
        i <= len(child) && return _unchecked_tree23(
            op, node.a, node.b, _massoc(op, child, value, i)::Tree23RepV{T,V})
    end
    throw(BoundsError())
end

function _massoc(op::_MeasureOp, single::SingleFT{T,V}, value::T, i::Int)::SingleFT{T,V} where {T,V}
    child = single.a
    child isa Tree23{T} ?
        _single(op, _massoc(op, child::Tree23RepV{T,V}, value, i)) :
        _single(op, value)
end

function _massoc(op::_MeasureOp, tree::DeepFT{T,V}, value::T, i::Int)::DeepFT{T,V} where {T,V}
    j = len(tree.left)
    i <= j && return _unchecked_deep(
        op, _massoc(op, tree.left, value, i)::DigitFTRepV{T,V}, tree.succ, tree.right)
    i -= j
    j = len(tree.succ)
    i <= j && return _unchecked_deep(
        op, tree.left, _massoc(op, tree.succ, value, i)::FingerTreeRepV{T,V}, tree.right)
    i -= j
    _unchecked_deep(
        op, tree.left, tree.succ, _massoc(op, tree.right, value, i)::DigitFTRepV{T,V})
end

@inline _prefix_cache(op::_MeasureOp, prefix::V, child) where {V} =
    combine(op, prefix, _cache(op, child).value)

function _find_measure(op::_MeasureOp, predicate, digit::DigitFT, prefix, offset::Int)::Int
    for child in digit.child
        next = _prefix_cache(op, prefix, child)
        predicate(next) && return _find_measure(op, predicate, child, prefix, offset)
        prefix = next
        offset += len(child)
    end
    throw(BoundsError())
end

function _find_measure(op::_MeasureOp, predicate, node::Tree23, prefix, offset::Int)::Int
    for child in astuple(node)
        next = _prefix_cache(op, prefix, child)
        predicate(next) && return _find_measure(op, predicate, child, prefix, offset)
        prefix = next
        offset += len(child)
    end
    throw(BoundsError())
end

function _find_measure(op::_MeasureOp, predicate, tree::SingleFT, prefix, offset::Int)::Int
    _find_measure(op, predicate, tree.a, prefix, offset)
end

function _find_measure(op::_MeasureOp, predicate, tree::DeepFT, prefix, offset::Int)::Int
    for child in (tree.left, tree.succ, tree.right)
        next = _prefix_cache(op, prefix, child)
        predicate(next) && return _find_measure(op, predicate, child, prefix, offset)
        prefix = next
        offset += len(child)
    end
    throw(BoundsError())
end

function _find_measure(op::_MeasureOp, predicate, value, prefix, offset::Int)::Int
    predicate(combine(op, prefix, measure(op, value))) || throw(BoundsError())
    offset + 1
end

function MeasuredFingerTree(::Type{T}, op::M) where {T,M<:Measure}
    V = typeof(Base.identity(op))
    _measured(op, EmptyFT{T}(), V)
end

function MeasuredFingerTree(::Type{T}, values, op::M) where {T,M<:Measure}
    tree = MeasuredFingerTree(T, op)
    for value in values
        tree = conjr(tree, convert(T, value))
    end
    tree
end

MeasuredFingerTree(values, op::Measure) = MeasuredFingerTree(eltype(values), values, op)
MeasuredFingerTree(root::FingerTree{T}, op::Measure) where {T} = MeasuredFingerTree(T, root, op)
FingerTree(ft::MeasuredFingerTree{T}) where {T} = FingerTree(T, ft)

measure(ft::MeasuredFingerTree) =
    ft.root isa EmptyFT ? Base.identity(ft.measureop) : ft.root.value

eltype(::MeasuredFingerTree{T}) where {T} = T
Base.eltype(::Type{<:MeasuredFingerTree{T}}) where {T} = T
Base.IteratorEltype(::Type{<:MeasuredFingerTree}) = Base.HasEltype()
Base.IteratorSize(::Type{<:MeasuredFingerTree}) = Base.HasLength()
length(ft::MeasuredFingerTree) = length(ft.root)
isempty(ft::MeasuredFingerTree) = isempty(ft.root)
Base.firstindex(ft::MeasuredFingerTree) = firstindex(ft.root)
Base.lastindex(ft::MeasuredFingerTree) = lastindex(ft.root)
Base.eachindex(ft::MeasuredFingerTree) = eachindex(ft.root)
Base.keys(ft::MeasuredFingerTree) = keys(ft.root)
Base.copy(ft::MeasuredFingerTree) = ft
Base.empty(ft::MeasuredFingerTree{T}) where {T} = MeasuredFingerTree(T, ft.measureop)
Base.first(ft::MeasuredFingerTree) = first(ft.root)
Base.last(ft::MeasuredFingerTree) = last(ft.root)
Base.iterate(ft::MeasuredFingerTree) = iterate(ft.root)
Base.iterate(ft::MeasuredFingerTree, state) = iterate(ft.root, state)
collect(ft::MeasuredFingerTree) = collect(ft.root)
Base.reduce(op::Function, ft::MeasuredFingerTree) = reduce(op, ft.root)

Base.getindex(ft::MeasuredFingerTree, i::Integer) = ft.root[i]
function Base.getindex(ft::MeasuredFingerTree, range::UnitRange{<:Integer})
    isempty(range) && return empty(ft)
    first_index = Int(first(range))
    last_index = Int(last(range))
    1 <= first_index <= last_index <= length(ft) || throw(BoundsError(ft, range))
    _, first_value, suffix = split(ft, first_index)
    candidate = conjl(first_value, suffix)
    prefix, last_value, _ = split(candidate, last_index - first_index + 1)
    conjr(prefix, last_value)
end

function conjl(value::T, ft::MeasuredFingerTree{T,M,V}) where {T,M,V}
    _measured(ft.measureop, _mconjl(ft.measureop, value, ft.root)::FingerTreeRepV{T,V})
end

function conjr(ft::MeasuredFingerTree{T,M,V}, value::T) where {T,M,V}
    _measured(ft.measureop, _mconjr(ft.measureop, ft.root, value)::FingerTreeRepV{T,V})
end

function splitl(ft::MeasuredFingerTree)
    left, value, right = split(ft, 1)
    @assert isempty(left)
    value, right
end

function splitr(ft::MeasuredFingerTree)
    left, value, right = split(ft, length(ft))
    @assert isempty(right)
    left, value
end

function split(ft::MeasuredFingerTree{T,M,V}, i::Integer) where {T,M,V}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    result = _msplit(ft.measureop, ft.root, index)
    value = result.value::T
    _measured(ft.measureop, result.left, V), value, _measured(ft.measureop, result.right, V)
end

function assoc(ft::MeasuredFingerTree{T,M,V}, value::T, i::Integer) where {T,M,V}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    _measured(ft.measureop, _massoc(ft.measureop, ft.root, value, index)::FingerTreeRepV{T,V})
end

# ---------------------------------------------------------------------------
# Batched persistent updates
# ---------------------------------------------------------------------------

# Descend through the union of the affected root-to-leaf paths. Each affected
# structural node is rebuilt once, while unaffected children are shared.

struct _MultiReplace{A}
    values::A
end

struct _MultiTransform{F}
    f::F
end

struct _DigitEditResult{T,V}
    digit::DigitFTRepV{T,V}
    next::Int
    stop::Int
end


@inline _multiedit_value(edit::_MultiReplace, _, update_index::Int, ::Int) =
    @inbounds edit.values[update_index]
@inline _multiedit_value(edit::_MultiTransform, old, ::Int, position::Int) =
    edit.f(position, old)

@inline function _mmultiedit(::_MeasureOp, value::T, indices, edit,
                             lo::Int, hi::Int, offset::Int) where {T}
    lo == hi || throw(ArgumentError("multiple batched updates reached one leaf"))
    position = offset + 1
    @inbounds indices[lo] == position || throw(BoundsError())
    convert(T, _multiedit_value(edit, value, lo, position))
end

@inline function _first_update_after(indices, bound::Int, lo::Int, hi::Int)
    # `indices` is strictly increasing. Locate the first update beyond this
    # child's span without rescanning every update at each tree level.
    first = lo
    last = hi
    @inbounds while first <= last
        middle = first + ((last - first) >>> 1)
        if indices[middle] <= bound
            first = middle + 1
        else
            last = middle - 1
        end
    end
    first
end

@inline function _mmultiedit_child_impl(op::_MeasureOp, child, indices, edit,
                                        lo::Int, hi::Int, offset::Int)
    stop = offset + len(child)
    next = _first_update_after(indices, stop, lo, hi)
    updated = next == lo ? child :
        _mmultiedit(op, child, indices, edit, lo, next - 1, offset)
    updated, next, stop
end

@inline _mmultiedit_child(op::_MeasureOp, child, indices, edit,
                          lo::Int, hi::Int, offset::Int) =
    _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)

@inline function _mmultiedit_child(op::_MeasureOp, child::DLeaf{T,N,V}, indices,
                                   edit, lo::Int, hi::Int, offset::Int) where {T,N,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::DLeaf{T,N,V}, next, stop
end

@inline function _mmultiedit_child(op::_MeasureOp, child::DNode{T,N,V}, indices,
                                   edit, lo::Int, hi::Int, offset::Int) where {T,N,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::DNode{T,N,V}, next, stop
end

@inline function _mmultiedit_child(op::_MeasureOp, child::Leaf23{T,V}, indices,
                                   edit, lo::Int, hi::Int, offset::Int) where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::Leaf23{T,V}, next, stop
end

@inline function _mmultiedit_child(op::_MeasureOp, child::Node23{T,V}, indices,
                                   edit, lo::Int, hi::Int, offset::Int) where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::Node23{T,V}, next, stop
end

@inline function _mmultiedit_child(op::_MeasureOp, child::SingleFT{T,V}, indices,
                                   edit, lo::Int, hi::Int, offset::Int) where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::SingleFT{T,V}, next, stop
end

@inline function _mmultiedit_child(op::_MeasureOp, child::DeepFT{T,V}, indices,
                                   edit, lo::Int, hi::Int, offset::Int) where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::DeepFT{T,V}, next, stop
end

@inline _mmultiedit_child(op::_MeasureOp, child::EmptyFT, indices, edit,
                          lo::Int, hi::Int, offset::Int) =
    (child, lo, offset)

@inline function _mmultiedit_digit_child(op::_MeasureOp,
                                         child::DigitFTRepV{T,V}, indices, edit,
                                         lo::Int, hi::Int, offset::Int)::
                                         _DigitEditResult{T,V} where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    _DigitEditResult{T,V}(updated::DigitFTRepV{T,V}, next, stop)
end

@inline _mmultiedit_finger_child(::_MeasureOp, child::EmptyFT, ::Any, ::Any,
                                 lo::Int, ::Int, offset::Int) =
    (child, lo, offset)

@inline function _mmultiedit_finger_child(op::_MeasureOp,
                                          child::SingleFT{T,V}, indices, edit,
                                          lo::Int, hi::Int, offset::Int) where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::SingleFT{T,V}, next, stop
end

@inline function _mmultiedit_finger_child(op::_MeasureOp,
                                          child::DeepFT{T,V}, indices, edit,
                                          lo::Int, hi::Int, offset::Int) where {T,V}
    updated, next, stop = _mmultiedit_child_impl(op, child, indices, edit, lo, hi, offset)
    updated::DeepFT{T,V}, next, stop
end

@inline function _mmultiedit_children(op::_MeasureOp, children::Tuple{A}, indices,
                                      edit, lo::Int, hi::Int, offset::Int) where {A}
    a, next, stop = _mmultiedit_child(op, children[1], indices, edit, lo, hi, offset)
    (a,), next, stop
end


@inline function _mmultiedit_children(op::_MeasureOp, children::Tuple{A,B}, indices,
                                      edit, lo::Int, hi::Int, offset::Int) where {A,B}
    a, next, stop = _mmultiedit_child(op, children[1], indices, edit, lo, hi, offset)
    b, next, stop = _mmultiedit_child(op, children[2], indices, edit, next, hi, stop)
    (a, b), next, stop
end


@inline function _mmultiedit_children(op::_MeasureOp, children::Tuple{A,B,C}, indices,
                                      edit, lo::Int, hi::Int, offset::Int) where {A,B,C}
    a, next, stop = _mmultiedit_child(op, children[1], indices, edit, lo, hi, offset)
    b, next, stop = _mmultiedit_child(op, children[2], indices, edit, next, hi, stop)
    c, next, stop = _mmultiedit_child(op, children[3], indices, edit, next, hi, stop)
    (a, b, c), next, stop
end


@inline function _mmultiedit_children(op::_MeasureOp, children::Tuple{A,B,C,D}, indices,
                                      edit, lo::Int, hi::Int, offset::Int) where {A,B,C,D}
    a, next, stop = _mmultiedit_child(op, children[1], indices, edit, lo, hi, offset)
    b, next, stop = _mmultiedit_child(op, children[2], indices, edit, next, hi, stop)
    c, next, stop = _mmultiedit_child(op, children[3], indices, edit, next, hi, stop)
    d, next, stop = _mmultiedit_child(op, children[4], indices, edit, next, hi, stop)
    (a, b, c, d), next, stop
end

function _mmultiedit_digit(op::_MeasureOp, digit::DigitFT, indices, edit,
                           lo::Int, hi::Int, offset::Int)
    children, next, _ =
        _mmultiedit_children(op, digit.child, indices, edit, lo, hi, offset)
    next == hi + 1 || throw(BoundsError())
    _unchecked_digit(op, children...)
end

function _mmultiedit(op::_MeasureOp, digit::DLeaf{T,N,V}, indices, edit,
                     lo::Int, hi::Int, offset::Int)::DLeaf{T,N,V} where {T,N,V}
    _mmultiedit_digit(op, digit, indices, edit, lo, hi, offset)
end

function _mmultiedit(op::_MeasureOp, digit::DNode{T,N,V}, indices, edit,
                     lo::Int, hi::Int, offset::Int)::DNode{T,N,V} where {T,N,V}
    children, next, _ =
        _mmultiedit_children(op, digit.child, indices, edit, lo, hi, offset)
    next == hi + 1 || throw(BoundsError())
    _dnode_cached(op, children)
end

function _mmultiedit_tree23(op::_MeasureOp, node::Tree23, indices, edit,
                            lo::Int, hi::Int, offset::Int)
    children, next, _ =
        _mmultiedit_children(op, astuple(node), indices, edit, lo, hi, offset)
    next == hi + 1 || throw(BoundsError())
    _unchecked_tree23(op, children...)
end


function _mmultiedit(op::_MeasureOp, node::Leaf23{T,V}, indices, edit,
                     lo::Int, hi::Int, offset::Int)::Leaf23{T,V} where {T,V}
    _mmultiedit_tree23(op, node, indices, edit, lo, hi, offset)
end

function _mmultiedit(op::_MeasureOp, node::Node23{T,V}, indices, edit,
                     lo::Int, hi::Int, offset::Int)::Node23{T,V} where {T,V}
    _mmultiedit_tree23(op, node, indices, edit, lo, hi, offset)
end

function _mmultiedit(op::_MeasureOp, single::SingleFT{T,V}, indices, edit,
                     lo::Int, hi::Int, offset::Int)::SingleFT{T,V} where {T,V}
    child = single.a
    child isa Tree23{T} ?
        _single(op, _mmultiedit(
            op, child::Tree23RepV{T,V}, indices, edit, lo, hi, offset)) :
        _single(op, _mmultiedit(op, child::T, indices, edit, lo, hi, offset))
end

function _mmultiedit(op::_MeasureOp, tree::DeepFT{T,V}, indices, edit,
                     lo::Int, hi::Int, offset::Int)::DeepFT{T,V} where {T,V}
    left_result =
        _mmultiedit_digit_child(op, tree.left, indices, edit, lo, hi, offset)
    middle, next, stop =
        _mmultiedit_finger_child(op, tree.succ, indices, edit,
                                 left_result.next, hi, left_result.stop)
    right_result =
        _mmultiedit_digit_child(op, tree.right, indices, edit, next, hi, stop)
    right_result.next == hi + 1 || throw(BoundsError())
    _deep(op, left_result.digit, middle::FingerTreeRepV{T,V}, right_result.digit)
end

_mmultiedit(::Any, tree::EmptyFT, ::Any, ::Any, ::Int, ::Int, ::Int) =
    throw(BoundsError(tree))

function _check_sorted_indices(indices, n::Int)
    previous = 0
    @inbounds for k in eachindex(indices)
        index = Int(indices[k])
        1 <= index <= n || throw(BoundsError(1:n, index))
        index > previous ||
            throw(ArgumentError("indices must be distinct and strictly increasing"))
        previous = index
    end
    nothing
end

function _sort_updates(indices, values, ::Type{T}) where {T}
    length(indices) == length(values) ||
        throw(DimensionMismatch("indices and values must have equal length"))
    order = sortperm(indices)
    sorted_indices = Vector{Int}(undef, length(order))
    sorted_values = Vector{T}(undef, length(order))
    @inbounds for k in eachindex(order)
        source = order[k]
        sorted_indices[k] = Int(indices[source])
        sorted_values[k] = convert(T, values[source])
    end
    sorted_indices, sorted_values
end

"""
    multiassoc(tree, indices, values; presorted=false)

Persistently replace several elements in one structural descent. With
`presorted=true`, indices must be distinct and strictly increasing; otherwise
the index/value pairs are sorted first.
"""
function multiassoc(ft::MeasuredFingerTree{T,M,V}, indices::AbstractVector{<:Integer},
                    values::AbstractVector; presorted::Bool=false) where {T,M,V}
    length(indices) == length(values) ||
        throw(DimensionMismatch("indices and values must have equal length"))
    isempty(indices) && return ft

    if presorted
        _check_sorted_indices(indices, length(ft))
        root = _mmultiedit(ft.measureop, ft.root, indices, _MultiReplace(values),
                           firstindex(indices), lastindex(indices), 0)
    else
        sorted_indices, sorted_values = _sort_updates(indices, values, T)
        _check_sorted_indices(sorted_indices, length(ft))
        root = _mmultiedit(ft.measureop, ft.root, sorted_indices,
                           _MultiReplace(sorted_values), 1,
                           length(sorted_indices), 0)
    end
    _measured(ft.measureop, root::FingerTreeRepV{T,V}, V)
end

function multiassoc(ft::FingerTree{T}, indices::AbstractVector{<:Integer},
                    values::AbstractVector; presorted::Bool=false) where {T}
    length(indices) == length(values) ||
        throw(DimensionMismatch("indices and values must have equal length"))
    isempty(indices) && return ft

    if presorted
        _check_sorted_indices(indices, length(ft))
        _mmultiedit(_NO_MEASURE, ft, indices, _MultiReplace(values),
                    firstindex(indices), lastindex(indices), 0)::FingerTreeRep{T}
    else
        sorted_indices, sorted_values = _sort_updates(indices, values, T)
        _check_sorted_indices(sorted_indices, length(ft))
        _mmultiedit(_NO_MEASURE, ft, sorted_indices, _MultiReplace(sorted_values),
                    1, length(sorted_indices), 0)::FingerTreeRep{T}
    end
end

"""
    multiupdate(tree, indices, f; presorted=false)

Persistently transform several leaves in one structural descent. The callback
is invoked as `f(index, old_value)` once for each selected element.
"""
function multiupdate(ft::MeasuredFingerTree{T,M,V}, indices::AbstractVector{<:Integer},
                     f::F; presorted::Bool=false) where {T,M,V,F}
    isempty(indices) && return ft
    sorted_indices = presorted ? indices : sort!(Int[Int(index) for index in indices])
    _check_sorted_indices(sorted_indices, length(ft))
    lo, hi = firstindex(sorted_indices), lastindex(sorted_indices)
    root = _mmultiedit(ft.measureop, ft.root, sorted_indices, _MultiTransform(f),
                       lo, hi, 0)
    _measured(ft.measureop, root::FingerTreeRepV{T,V}, V)
end

function multiupdate(ft::FingerTree{T}, indices::AbstractVector{<:Integer},
                     f::F; presorted::Bool=false) where {T,F}
    isempty(indices) && return ft
    sorted_indices = presorted ? indices : sort!(Int[Int(index) for index in indices])
    _check_sorted_indices(sorted_indices, length(ft))
    lo, hi = firstindex(sorted_indices), lastindex(sorted_indices)
    _mmultiedit(_NO_MEASURE, ft, sorted_indices, _MultiTransform(f), lo, hi, 0)::FingerTreeRep{T}
end

# Do-block-friendly forms.
multiupdate(f::F, ft::MeasuredFingerTree, indices::AbstractVector{<:Integer};
            presorted::Bool=false) where {F} =
    multiupdate(ft, indices, f; presorted)
multiupdate(f::F, ft::FingerTree, indices::AbstractVector{<:Integer};
            presorted::Bool=false) where {F} =
    multiupdate(ft, indices, f; presorted)

# ---------------------------------------------------------------------------
# Sparse read-only folds
# ---------------------------------------------------------------------------

struct _MultiFoldOp{R,C,U,S}
    identity::R
    combine::C
    untouched::U
    selected::S
end

struct _MultiFoldResult{R}
    value::R
    next::Int
    stop::Int
end

@inline function _mmultifold_child(op::_MeasureOp, child, indices, fold::_MultiFoldOp{R},
                                   lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {R}
    stop = offset + len(child)
    len(child) == 0 && return _MultiFoldResult(fold.identity, lo, stop)
    next = _first_update_after(indices, stop, lo, hi)
    value = if next == lo
        convert(R, fold.untouched(offset + 1, stop, _cache(op, child).value))
    else
        (_mmultifold(op, child, indices, fold, lo, next - 1, offset)::_MultiFoldResult{R}).value
    end
    _MultiFoldResult{R}(value, next, stop)
end

@inline function _fold_combine(fold::_MultiFoldOp{R}, left::R, right)::R where {R}
    convert(R, fold.combine(left, right))
end

@inline function _mmultifold_children(op::_MeasureOp, children::Tuple{A}, indices,
                                      fold::_MultiFoldOp{R}, lo::Int, hi::Int,
                                      offset::Int)::_MultiFoldResult{R} where {A,R}
    a = _mmultifold_child(op, children[1], indices, fold, lo, hi, offset)
    _MultiFoldResult{R}(_fold_combine(fold, fold.identity, a.value), a.next, a.stop)
end

@inline function _mmultifold_children(op::_MeasureOp, children::Tuple{A,B}, indices,
                                      fold::_MultiFoldOp{R}, lo::Int, hi::Int,
                                      offset::Int)::_MultiFoldResult{R} where {A,B,R}
    a = _mmultifold_child(op, children[1], indices, fold, lo, hi, offset)
    b = _mmultifold_child(op, children[2], indices, fold, a.next, hi, a.stop)
    value = _fold_combine(fold, fold.identity, a.value)
    _MultiFoldResult{R}(_fold_combine(fold, value, b.value), b.next, b.stop)
end

@inline function _mmultifold_children(op::_MeasureOp, children::Tuple{A,B,C}, indices,
                                      fold::_MultiFoldOp{R}, lo::Int, hi::Int,
                                      offset::Int)::_MultiFoldResult{R} where {A,B,C,R}
    a = _mmultifold_child(op, children[1], indices, fold, lo, hi, offset)
    b = _mmultifold_child(op, children[2], indices, fold, a.next, hi, a.stop)
    c = _mmultifold_child(op, children[3], indices, fold, b.next, hi, b.stop)
    value = fold.identity
    value = _fold_combine(fold, value, a.value)
    value = _fold_combine(fold, value, b.value)
    _MultiFoldResult{R}(_fold_combine(fold, value, c.value), c.next, c.stop)
end

@inline function _mmultifold_children(op::_MeasureOp, children::Tuple{A,B,C,D}, indices,
                                      fold::_MultiFoldOp{R}, lo::Int, hi::Int,
                                      offset::Int)::_MultiFoldResult{R} where {A,B,C,D,R}
    a = _mmultifold_child(op, children[1], indices, fold, lo, hi, offset)
    b = _mmultifold_child(op, children[2], indices, fold, a.next, hi, a.stop)
    c = _mmultifold_child(op, children[3], indices, fold, b.next, hi, b.stop)
    d = _mmultifold_child(op, children[4], indices, fold, c.next, hi, c.stop)
    value = fold.identity
    value = _fold_combine(fold, value, a.value)
    value = _fold_combine(fold, value, b.value)
    value = _fold_combine(fold, value, c.value)
    _MultiFoldResult{R}(_fold_combine(fold, value, d.value), d.next, d.stop)
end

@inline function _mmultifold(::_MeasureOp, value::T, indices, fold::_MultiFoldOp{R},
                             lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,R}
    lo == hi || throw(ArgumentError("multiple selected indices reached one leaf"))
    position = offset + 1
    @inbounds indices[lo] == position || throw(BoundsError())
    _MultiFoldResult{R}(convert(R, fold.selected(position, value)), lo + 1, position)
end

function _mmultifold(op::_MeasureOp, digit::DLeaf{T,N,V}, indices, fold::_MultiFoldOp{R},
                     lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,N,V,R}
    _mmultifold_children(op, digit.child, indices, fold, lo, hi, offset)
end

function _mmultifold(op::_MeasureOp, digit::DNode{T,N,V}, indices, fold::_MultiFoldOp{R},
                     lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,N,V,R}
    _mmultifold_children(op, digit.child, indices, fold, lo, hi, offset)
end

function _mmultifold(op::_MeasureOp, node::Leaf23{T,V}, indices, fold::_MultiFoldOp{R},
                     lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,V,R}
    c = node.c
    isnothing(c) ?
        _mmultifold_children(op, (node.a, node.b), indices, fold, lo, hi, offset) :
        _mmultifold_children(op, (node.a, node.b, something(c)), indices, fold, lo, hi, offset)
end

function _mmultifold(op::_MeasureOp, node::Node23{T,V}, indices, fold::_MultiFoldOp{R},
                     lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,V,R}
    c = node.c
    isnothing(c) ?
        _mmultifold_children(op, (node.a, node.b), indices, fold, lo, hi, offset) :
        _mmultifold_children(op, (node.a, node.b, something(c)), indices, fold, lo, hi, offset)
end

function _mmultifold(op::_MeasureOp, tree::SingleFT{T,V}, indices, fold::_MultiFoldOp{R},
                     lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,V,R}
    child = tree.a
    child isa Tree23{T} ?
        _mmultifold(op, child::Tree23RepV{T,V}, indices, fold, lo, hi, offset) :
        _mmultifold(op, child::T, indices, fold, lo, hi, offset)
end

function _mmultifold(op::_MeasureOp, tree::DeepFT{T,V}, indices, fold::_MultiFoldOp{R},
                     lo::Int, hi::Int, offset::Int)::_MultiFoldResult{R} where {T,V,R}
    _mmultifold_children(op, (tree.left, tree.succ, tree.right), indices,
                         fold, lo, hi, offset)
end

"""
    multifold(tree, indices; identity, combine, untouched, selected,
              presorted=false)

Fold a measured finger tree while descending only through the union of paths to
`indices`. `selected(index, value)` transforms each selected leaf.
`untouched(first, last, cached_measure)` transforms a maximal untouched subtree
without visiting its leaves. Results are composed from left to right with
`combine`, beginning with `identity`.

With `presorted=true`, indices must be distinct and strictly increasing;
otherwise they are sorted first. An empty index set folds the whole nonempty
tree through one `untouched` call and returns `identity` for an empty tree.
"""
function multifold(ft::MeasuredFingerTree, indices::AbstractVector{<:Integer};
                   identity, combine, untouched, selected,
                   presorted::Bool=false)
    if isempty(indices)
        isempty(ft) && return identity
        return untouched(1, length(ft), measure(ft))
    end

    sorted_indices = presorted ? indices : sort!(Int[Int(index) for index in indices])
    _check_sorted_indices(sorted_indices, length(ft))
    fold = _MultiFoldOp(identity, combine, untouched, selected)
    lo, hi = firstindex(sorted_indices), lastindex(sorted_indices)
    result = _mmultifold(ft.measureop, ft.root, sorted_indices, fold, lo, hi, 0)
    result.next == hi + 1 || throw(BoundsError())
    result.stop == length(ft) || throw(BoundsError())
    result.value
end

function _mnodes(op::_MeasureOp, values::Tuple)
    n = length(values)
    n == 2 && return (_unchecked_tree23(op, values...),)
    n == 3 && return (_unchecked_tree23(op, values...),)
    n == 4 && return (
        _unchecked_tree23(op, values[1], values[2]),
        _unchecked_tree23(op, values[3], values[4]),
    )
    (_unchecked_tree23(op, values[1], values[2], values[3]),
     _mnodes(op, Base.tail(Base.tail(Base.tail(values))))...)
end

function _mapp3(op::_MeasureOp, left::EmptyFT, middle::Tuple, right::FingerTree)
    result = right
    for value in Iterators.reverse(middle)
        result = _mconjl(op, value, result)
    end
    result
end

function _mapp3(op::_MeasureOp, left::FingerTree, middle::Tuple, right::EmptyFT)
    result = left
    for value in middle
        result = _mconjr(op, result, value)
    end
    result
end

function _mapp3(op::_MeasureOp, left::EmptyFT{T}, middle::Tuple, right::EmptyFT{T}) where {T}
    result = left
    for value in middle
        result = _mconjr(op, result, value)
    end
    result
end

function _mapp3(op::_MeasureOp, left::EmptyFT, middle::Tuple, right::SingleFT)
    result = right
    for value in Iterators.reverse(middle)
        result = _mconjl(op, value, result)
    end
    result
end

function _mapp3(op::_MeasureOp, left::SingleFT, middle::Tuple, right::EmptyFT)
    result = left
    for value in middle
        result = _mconjr(op, result, value)
    end
    result
end

function _mapp3(op::_MeasureOp, left::SingleFT, middle::Tuple, right::SingleFT)
    result = left
    for value in middle
        result = _mconjr(op, result, value)
    end
    _mconjr(op, result, right.a)
end

function _mapp3(op::_MeasureOp, left::SingleFT, middle::Tuple, right::FingerTree)
    _mapp3(op, EmptyFT{eltype(left)}(), (left.a, middle...), right)
end

function _mapp3(op::_MeasureOp, left::FingerTree, middle::Tuple, right::SingleFT)
    _mapp3(op, left, (middle..., right.a), EmptyFT{eltype(right)}())
end

function _mapp3(op::_MeasureOp, left::DeepFT, middle::Tuple, right::DeepFT)
    bridge = (left.right.child..., middle..., right.left.child...)
    _unchecked_deep(
        op,
        left.left,
        _mapp3(op, left.succ, _mnodes(op, bridge), right.succ),
        right.right,
    )
end

function concat(left::MeasuredFingerTree{T,M,V}, right::MeasuredFingerTree{T,M,V}) where {T,M,V}
    isequal(left.measureop, right.measureop) ||
        throw(ArgumentError("cannot concatenate trees with different measure operations"))
    root = _mapp3(left.measureop, left.root, (), right.root)::FingerTreeRepV{T,V}
    _measured(left.measureop, root, V)
end

function split_measure(predicate, ft::MeasuredFingerTree{T,M,V}) where {T,M,V}
    isempty(ft) && throw(BoundsError(ft))
    prefix = convert(V, Base.identity(ft.measureop))
    predicate(measure(ft)) || throw(BoundsError(ft))
    index::Int = _find_measure(ft.measureop, predicate, ft.root, prefix, 0)
    split(ft, index)
end

function Base.:(==)(left::MeasuredFingerTree, right::MeasuredFingerTree)
    isequal(left.measureop, right.measureop) && left.root == right.root
end

include("PriorityQueue.jl")

# ---------------------------------------------------------------------------
# Display
# ---------------------------------------------------------------------------

Base.show(io::IO, d::DigitFT) = print(io, join(d.child, " "))
function Base.show(io::IO, node::Tree23)
    len(node) >= 20 && return print(io, "…")
    print(io, node.a, " ", node.b)
    !isnothing(node.c) && print(io, " ", something(node.c))
end

function Base.show(io::IO, tree::FingerTree{T}) where {T}
    print(io, "FingerTree{")
    show(io, T)
    print(io, "}([")

    for (i, value) in enumerate(tree)
        if i > 10
            print(io, ", …")
            break
        end
        i > 1 && print(io, ", ")
        show(io, value)
    end

    print(io, "])")
end

function Base.show(io::IO, tree::MeasuredFingerTree{T,M}) where {T,M}
    print(io, "MeasuredFingerTree{")
    show(io, T)
    print(io, ", ")
    show(io, M)
    print(io, "}(")
    show(io, tree.root)
    print(io, ")")
end

end
