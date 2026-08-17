module FingerTrees
import Base: reduce, length, collect, split, eltype, isempty

export FingerTree, EmptyFT
export assoc, concat, conjl, conjr, split, splitl, splitr

# ---------------------------------------------------------------------------
# Internal representation
# ---------------------------------------------------------------------------

abstract type FingerTree{T} end
abstract type Tree23{T} end

# Internal algorithms preserve the structural invariants by construction.  The
# trusted tag lets them bypass repeated balance checks while direct constructors
# remain checked.
struct _TrustedConstruction end
const _TRUSTED = _TrustedConstruction()

mutable struct Leaf23{T} <: Tree23{T}
    const a::T
    const b::T
    const c::Union{Nothing,T}
    const len::Int
    const depth::Int
    function Leaf23(a::T, b::T) where {T}
        dep(a) == dep(b) || throw(ArgumentError("cannot construct an uneven 2-leaf"))
        new{T}(a, b, nothing, len(a) + len(b), dep(a) + 1)
    end
    function Leaf23(a::T, b::T, c::T) where {T}
        dep(a) == dep(b) == dep(c) || throw(ArgumentError("cannot construct an uneven 3-leaf"))
        new{T}(a, b, c, len(a) + len(b) + len(c), dep(a) + 1)
    end
    Leaf23(::_TrustedConstruction, a::T, b::T) where {T} =
        new{T}(a, b, nothing, len(a) + len(b), dep(a) + 1)
    Leaf23(::_TrustedConstruction, a::T, b::T, c::T) where {T} =
        new{T}(a, b, c, len(a) + len(b) + len(c), dep(a) + 1)
end

struct Node23{T} <: Tree23{T}
    a::Union{Leaf23{T},Node23{T}}
    b::Union{Leaf23{T},Node23{T}}
    c::Union{Nothing,Leaf23{T},Node23{T}}
    len::Int
    depth::Int
    function Node23(a::Tree23{T}, b::Tree23{T}) where {T}
        dep(a) == dep(b) || throw(ArgumentError("cannot construct an uneven 2-node"))
        new{T}(a, b, nothing, len(a) + len(b), dep(a) + 1)
    end
    function Node23(a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T}
        dep(a) == dep(b) == dep(c) || throw(ArgumentError("cannot construct an uneven 3-node"))
        new{T}(a, b, c, len(a) + len(b) + len(c), dep(a) + 1)
    end
    Node23(::_TrustedConstruction, a::Tree23{T}, b::Tree23{T}) where {T} =
        new{T}(a, b, nothing, len(a) + len(b), dep(a) + 1)
    Node23(::_TrustedConstruction, a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T} =
        new{T}(a, b, c, len(a) + len(b) + len(c), dep(a) + 1)
end

const Tree23Rep{T} = Union{Leaf23{T},Node23{T}}

Tree23(a,b,c) = Leaf23(a,b,c)
Tree23(a,b) = Leaf23(a,b)
Tree23(a::Tree23{T},b::Tree23{T},c::Tree23{T}) where {T} = Node23(a,b,c)
Tree23(a::Tree23{T},b::Tree23{T}) where {T} = Node23(a,b)

_unchecked_tree23(a, b) = Leaf23(_TRUSTED, a, b)
_unchecked_tree23(a, b, c) = Leaf23(_TRUSTED, a, b, c)
_unchecked_tree23(a::Tree23{T}, b::Tree23{T}) where {T} = Node23(_TRUSTED, a, b)
_unchecked_tree23(a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T} =
    Node23(_TRUSTED, a, b, c)

abstract type DigitFT{T,N} end

# Digits have reference identity so reusing one in a path copy does not box its
# payload again. Const fields preserve the immutable semantics of the tree.
mutable struct DLeaf{T,N} <: DigitFT{T,N} # Constructors restrict N to 1:4.
    const child::NTuple{N,T}
    const len::Int
    const depth::Int
    DLeaf(a::T) where {T} = new{T,1}((a,), len(a), 0)
    function DLeaf(a::T,b::T) where {T}
        new{T,2}((a, b), len(a) + len(b), 0)
    end
    function DLeaf(a::T,b::T,c::T) where {T}
        new{T,3}((a, b, c), len(a) + len(b) + len(c), 0)
    end
    function DLeaf(a::T,b::T,c::T,d::T) where {T}
        new{T,4}((a, b, c, d), +(len(a), len(b), len(c), len(d)), 0)
    end
end

mutable struct DNode{T,N} <: DigitFT{T,N}
    const child::NTuple{N,Tree23Rep{T}}
    const len::Int
    const depth::Int
    DNode(a::Tree23{T}) where {T} = new{T,1}((a,), len(a), dep(a))
    function DNode(a::Tree23{T},b::Tree23{T}) where {T}
        dep(a) == dep(b) || throw(ArgumentError("cannot construct an uneven digit"))
        new{T,2}((a, b), len(a) + len(b), dep(a))
    end
    function DNode(a::Tree23{T},b::Tree23{T},c::Tree23{T}) where {T}
        dep(a) == dep(b) == dep(c) || throw(ArgumentError("cannot construct an uneven digit"))
        new{T,3}((a, b, c), len(a) + len(b) + len(c), dep(a))
    end
    function DNode(a::Tree23{T},b::Tree23{T},c::Tree23{T},d::Tree23{T}) where {T}
        dep(a) == dep(b) == dep(c) == dep(d) ||
            throw(ArgumentError("cannot construct an uneven digit"))
        new{T,4}((a, b, c, d), +(len(a), len(b), len(c), len(d)), dep(a))
    end
    DNode(::_TrustedConstruction, a::Tree23{T}) where {T} =
        new{T,1}((a,), len(a), dep(a))
    DNode(::_TrustedConstruction, a::Tree23{T}, b::Tree23{T}) where {T} =
        new{T,2}((a, b), len(a) + len(b), dep(a))
    DNode(::_TrustedConstruction, a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T} =
        new{T,3}((a, b, c), len(a) + len(b) + len(c), dep(a))
    DNode(::_TrustedConstruction, a::Tree23{T}, b::Tree23{T}, c::Tree23{T}, d::Tree23{T}) where {T} =
        new{T,4}((a, b, c, d), +(len(a), len(b), len(c), len(d)), dep(a))
end

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

DigitFT(a) = DLeaf(a)
DigitFT(a,b) = DLeaf(a,b)
DigitFT(a,b,c) = DLeaf(a,b,c)
DigitFT(a,b,c,d)  = DLeaf(a,b,c,d)
DigitFT(a::Tree23{T}) where {T} = DNode(a)
DigitFT(a::Tree23{T},b::Tree23{T}) where {T} = DNode(a,b)
DigitFT(a::Tree23{T},b::Tree23{T},c::Tree23{T}) where {T} = DNode(a,b,c)
DigitFT(a::Tree23{T},b::Tree23{T},c::Tree23{T},d::Tree23{T}) where {T} = DNode(a,b,c,d)

_unchecked_digit(a) = DLeaf(a)
_unchecked_digit(a, b) = DLeaf(a, b)
_unchecked_digit(a, b, c) = DLeaf(a, b, c)
_unchecked_digit(a, b, c, d) = DLeaf(a, b, c, d)
_unchecked_digit(a::Tree23{T}) where {T} = DNode(_TRUSTED, a)
_unchecked_digit(a::Tree23{T}, b::Tree23{T}) where {T} = DNode(_TRUSTED, a, b)
_unchecked_digit(a::Tree23{T}, b::Tree23{T}, c::Tree23{T}) where {T} = DNode(_TRUSTED, a, b, c)
_unchecked_digit(a::Tree23{T}, b::Tree23{T}, c::Tree23{T}, d::Tree23{T}) where {T} =
    DNode(_TRUSTED, a, b, c, d)

function digit(n::Tree23{T}) where T
    if isnothing(n.c)
        _unchecked_digit(n.a, n.b)
    else
        _unchecked_digit(n.a, n.b, something(n.c))
    end
end
digit(t::NTuple{N,T}) where {N, T} = _unchecked_digit(t...)
digit(t::T) where {T} = _unchecked_digit(t)

struct EmptyFT{T} <: FingerTree{T}
end

struct SingleFT{T} <: FingerTree{T}
    a::Union{T,Tree23Rep{T}}
    SingleFT(a::T) where {T} = new{T}(a)
    SingleFT(a::Tree23{T}) where {T} = new{T}(a)
end


struct DeepFT{T} <: FingerTree{T}
    left::DigitFTRep{T}
    succ::Union{EmptyFT{T},SingleFT{T},DeepFT{T}}
    right::DigitFTRep{T}
    len::Int
    depth::Int
    function DeepFT(l::DigitFT{T,N}, s::FingerTree{T}, r::DigitFT{T,M}) where {T,N,M}
        balanced = dep(l) == dep(s) - 1 == dep(r) || (isempty(s) && dep(l) == dep(r))
        balanced || throw(ArgumentError("cannot construct an uneven finger tree"))
        new{T}(l, s, r, len(l) + len(s) + len(r), dep(l))
    end
    DeepFT(::_TrustedConstruction, l::DigitFT{T,N}, s::FingerTree{T}, r::DigitFT{T,M}) where {T,N,M} =
        new{T}(l, s, r, len(l) + len(s) + len(r), dep(l))
end

const FingerTreeRep{T} = Union{EmptyFT{T}, SingleFT{T}, DeepFT{T}}
const SplitValue{T} = Union{T,Tree23Rep{T}}

# End views distinguish the public leaf level from recursive node levels.
# This lets pop avoid carrying SplitValue{T} through the recursive hot path.
struct LeafLeftView{T}
    value::T
    rest::FingerTreeRep{T}
end

struct LeafRightView{T}
    rest::FingerTreeRep{T}
    value::T
end

struct NodeLeftView{T}
    value::Tree23Rep{T}
    rest::FingerTreeRep{T}
end

struct NodeRightView{T}
    rest::FingerTreeRep{T}
    value::Tree23Rep{T}
end

const TraversalBranch{T} = Union{
    DeepFT{T},
    Node23{T},
    DNode{T,1},
    DNode{T,2},
    DNode{T,3},
    DNode{T,4},
}

mutable struct IterationState{T}
    branches::Vector{TraversalBranch{T}}
    next::Vector{Int}
    pending::Vector{T}
    pending_next::Int
end

DeepFT(l::T, s::FingerTree{T}, r::T) where {T} = DeepFT(digit(l), s, digit(r))
DeepFT(l::Tree23{T}, s::FingerTree{T}, r::Tree23{T}) where {T} = DeepFT(DigitFT(l), s, DigitFT(r))

DeepFT(l::T, r::T) where {T} = DeepFT(DigitFT(l), EmptyFT{T}(), DigitFT(r))
DeepFT(l::Tree23{T}, r::Tree23{T}) where {T} = DeepFT(DigitFT(l), EmptyFT{T}(), DigitFT(r))
DeepFT(l::DigitFT{T}, r::DigitFT{T}) where {T} = DeepFT(l, EmptyFT{T}(), r)

_unchecked_deep(l::DigitFT{T}, s::FingerTree{T}, r::DigitFT{T}) where {T} =
    DeepFT(_TRUSTED, l, s, r)
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

# Depth is cached as data rather than encoded recursively in the Julia type.

# ---------------------------------------------------------------------------
# Cached measures and collection interface
# ---------------------------------------------------------------------------

dep(_) = 0
dep(n::Tree23) = n.depth
dep(d::DigitFT) = d.depth
dep(s::SingleFT) = dep(s.a)
dep(_::EmptyFT) = 0
dep(ft::DeepFT) = ft.depth

eltype(::FingerTree{T}) where {T} = T
eltype(::DigitFT{T}) where {T} = T
Base.eltype(::Type{<:FingerTree{T}}) where {T} = T
Base.IteratorEltype(::Type{<:FingerTree}) = Base.HasEltype()
Base.IteratorSize(::Type{<:FingerTree}) = Base.HasLength()


# `len` is the cached sequence measure. A future measured-tree API can
# generalize this beyond element counts.

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

@inline function _index_leaf(n::Leaf23{T}, i::Int)::T where {T}
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

@inline function _index_tree23(node::Tree23Rep{T}, i::Int)::T where {T}
    while node isa Node23{T}
        n = node::Node23{T}

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

    _index_leaf(node::Leaf23{T}, i)
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

@inline function _index_fingertree(ft::FingerTreeRep{T}, i::Int)::T where {T}
    tree = ft
    while true
        if tree isa SingleFT{T}
            child = (tree::SingleFT{T}).a
            if child isa Tree23{T}
                return _index_tree23(child::Tree23Rep{T}, i)
            end
            i == 1 || throw(BoundsError())
            return child::T
        elseif tree isa DeepFT{T}
            deep = tree::DeepFT{T}

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

function Base.getindex(n::Tree23{T}, i::Integer)::T where {T}
    index = Int(i)
    1 <= index <= len(n) || throw(BoundsError(n, i))
    _index_tree23(n::Tree23Rep{T}, index)
end

function Base.getindex(ft::FingerTree{T}, i::Integer)::T where {T}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    _index_fingertree(ft::FingerTreeRep{T}, index)
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

@inline function _viewl_leaf(single::SingleFT{T})::LeafLeftView{T} where {T}
    LeafLeftView{T}(single.a::T, EmptyFT{T}())
end

@inline function _viewr_leaf(single::SingleFT{T})::LeafRightView{T} where {T}
    LeafRightView{T}(EmptyFT{T}(), single.a::T)
end

function _viewl_node(single::SingleFT{T})::NodeLeftView{T} where {T}
    NodeLeftView{T}(single.a::Tree23Rep{T}, EmptyFT{T}())
end

function _viewr_node(single::SingleFT{T})::NodeRightView{T} where {T}
    NodeRightView{T}(EmptyFT{T}(), single.a::Tree23Rep{T})
end

function conjl(a, ft::DeepFT{T}) where {T}
    if width(ft.left) < 4
        _unchecked_deep(conjl(a, ft.left), ft.succ, ft.right)
    else
        f = _unchecked_tree23(ft.left.child[2], ft.left.child[3], ft.left.child[4])
        _unchecked_deep(_unchecked_digit(a, ft.left.child[1]), conjl(f, ft.succ), ft.right)
    end
end

function conjr(ft::DeepFT, a)
    if width(ft.right) < 4
        _unchecked_deep(ft.left, ft.succ, conjr(ft.right, a))
    else
        f = _unchecked_tree23(ft.right.child[1:3]...)
        _unchecked_deep(ft.left, conjr(ft.succ, f), _unchecked_digit(ft.right.child[4], a))
    end
end

function _viewl_leaf(ft::DeepFT{T}, left::DLeaf{T,N})::LeafLeftView{T} where {T,N}
    a = left.child[1]
    if N > 1
        return LeafLeftView{T}(a, _unchecked_deep(_tail_digit(left), ft.succ, ft.right))
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return LeafLeftView{T}(a, toftree(ft.right))
    end

    s = _viewl_node(middle)
    # The first middle level of a leaf tree contains Leaf23 values.
    node = s.value::Leaf23{T}
    return LeafLeftView{T}(a, _unchecked_deep(digit(node), s.rest, ft.right))
end

function _viewr_leaf(ft::DeepFT{T}, right::DLeaf{T,N})::LeafRightView{T} where {T,N}
    a = right.child[N]
    if N > 1
        return LeafRightView{T}(_unchecked_deep(ft.left, ft.succ, _init_digit(right)), a)
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return LeafRightView{T}(toftree(ft.left), a)
    end

    s = _viewr_node(middle)
    # The first middle level of a leaf tree contains Leaf23 values.
    node = s.value::Leaf23{T}
    return LeafRightView{T}(_unchecked_deep(ft.left, s.rest, digit(node)), a)
end

function _viewl_node(ft::DeepFT{T}, left::DNode{T,N})::NodeLeftView{T} where {T,N}
    a = left.child[1]
    if N > 1
        return NodeLeftView{T}(a, _unchecked_deep(_tail_digit(left), ft.succ, ft.right))
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return NodeLeftView{T}(a, toftree(ft.right))
    end

    s = _viewl_node(middle)
    # A nonempty successor of a node-level tree is at least two levels deep,
    # so the borrowed value is necessarily a Node23 rather than a Leaf23.
    node = s.value::Node23{T}
    return NodeLeftView{T}(a, _unchecked_deep(digit(node), s.rest, ft.right))
end

function _viewr_node(ft::DeepFT{T}, right::DNode{T,N})::NodeRightView{T} where {T,N}
    a = right.child[N]
    if N > 1
        return NodeRightView{T}(_unchecked_deep(ft.left, ft.succ, _init_digit(right)), a)
    end

    middle = ft.succ
    if middle isa EmptyFT{T}
        return NodeRightView{T}(toftree(ft.left), a)
    end

    s = _viewr_node(middle)
    # Symmetric to _viewl_node: recursive borrowing here always yields Node23.
    node = s.value::Node23{T}
    return NodeRightView{T}(_unchecked_deep(ft.left, s.rest, digit(node)), a)
end

@inline function _viewl_leaf(ft::DeepFT{T})::LeafLeftView{T} where {T}
    _viewl_leaf(ft, ft.left::DLeaf{T})
end

@inline function _viewr_leaf(ft::DeepFT{T})::LeafRightView{T} where {T}
    _viewr_leaf(ft, ft.right::DLeaf{T})
end

function _viewl_node(ft::DeepFT{T})::NodeLeftView{T} where {T}
    _viewl_node(ft, ft.left::DNode{T})
end

function _viewr_node(ft::DeepFT{T})::NodeRightView{T} where {T}
    _viewr_node(ft, ft.right::DNode{T})
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

const DigitFragment{T} = Union{Nothing,DigitFTRep{T}}

struct DigitSplit{T}
    left::DigitFragment{T}
    value::SplitValue{T}
    right::DigitFragment{T}
end

struct TreeSplit{T}
    left::FingerTreeRep{T}
    value::SplitValue{T}
    right::FingerTreeRep{T}
end

struct Tree23Split{T}
    left::DigitFragment{T}
    value::SplitValue{T}
    right::DigitFragment{T}
end

# A split fragment has at most three children.  Represent nonempty fragments
# immediately as digits and package the result in one concrete return type.
function split(d::DigitFT{T,1}, i) where {T}
    a = d.child[1]
    i <= len(a) && return DigitSplit{T}(nothing, a, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,2}, i) where {T}
    a, b = d.child
    j = len(a)
    i <= j && return DigitSplit{T}(nothing, a, _unchecked_digit(b))
    i -= j
    i <= len(b) && return DigitSplit{T}(_unchecked_digit(a), b, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,3}, i) where {T}
    a, b, c = d.child
    j = len(a)
    i <= j && return DigitSplit{T}(nothing, a, _unchecked_digit(b, c))
    i -= j
    j = len(b)
    i <= j && return DigitSplit{T}(_unchecked_digit(a), b, _unchecked_digit(c))
    i -= j
    i <= len(c) && return DigitSplit{T}(_unchecked_digit(a, b), c, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,4}, i) where {T}
    a, b, c, e = d.child
    j = len(a)
    i <= j && return DigitSplit{T}(nothing, a, _unchecked_digit(b, c, e))
    i -= j
    j = len(b)
    i <= j && return DigitSplit{T}(_unchecked_digit(a), b, _unchecked_digit(c, e))
    i -= j
    j = len(c)
    i <= j && return DigitSplit{T}(_unchecked_digit(a, b), c, _unchecked_digit(e))
    i -= j
    i <= len(e) && return DigitSplit{T}(_unchecked_digit(a, b, c), e, nothing)
    throw(BoundsError())
end

function _split23(n::Leaf23{T}, i::Int)::Tree23Split{T} where {T}
    if isnothing(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T}(nothing, n.a, _unchecked_digit(n.b))
        i -= j
        i <= len(n.b) && return Tree23Split{T}(_unchecked_digit(n.a), n.b, nothing)
    else
        c = something(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T}(nothing, n.a, _unchecked_digit(n.b, c))
        i -= j
        j = len(n.b)
        i <= j && return Tree23Split{T}(_unchecked_digit(n.a), n.b, _unchecked_digit(c))
        i -= j
        i <= len(c) && return Tree23Split{T}(_unchecked_digit(n.a, n.b), c, nothing)
    end
    throw(BoundsError())
end

function _split23(n::Node23{T}, i::Int)::Tree23Split{T} where {T}
    if isnothing(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T}(nothing, n.a, _unchecked_digit(n.b))
        i -= j
        i <= len(n.b) && return Tree23Split{T}(_unchecked_digit(n.a), n.b, nothing)
    else
        c = something(n.c)
        j = len(n.a)
        i <= j && return Tree23Split{T}(nothing, n.a, _unchecked_digit(n.b, c))
        i -= j
        j = len(n.b)
        i <= j && return Tree23Split{T}(_unchecked_digit(n.a), n.b, _unchecked_digit(c))
        i -= j
        i <= len(c) && return Tree23Split{T}(_unchecked_digit(n.a, n.b), c, nothing)
    end
    throw(BoundsError())
end


function collect(tree::FingerTree)
    values = Vector{eltype(tree)}(undef, length(tree))
    traverse((value, i) -> (values[i] = value), tree)
    values
end

const NonEmptyFT{T} = Union{SingleFT{T},DeepFT{T}}

_deepl(::Nothing, ::EmptyFT{T}, right::DigitFTRep{T}) where {T} = toftree(right)
function _deepl(::Nothing, ft::NonEmptyFT{T}, right::DigitFTRep{T}) where {T}
    s = _viewl_node(ft)
    _unchecked_deep(digit(s.value), s.rest, right)
end
_deepl(left::DigitFTRep{T}, ft::FingerTreeRep{T}, right::DigitFTRep{T}) where {T} =
    _unchecked_deep(left, ft, right)

function deepl(
    left::DigitFragment{T},
    middle::FingerTreeRep{T},
    right::DigitFTRep{T},
)::FingerTreeRep{T} where {T}
    _deepl(left, middle, right)
end

_deepr(left::DigitFTRep{T}, ::EmptyFT{T}, ::Nothing) where {T} = toftree(left)
function _deepr(left::DigitFTRep{T}, ft::NonEmptyFT{T}, ::Nothing) where {T}
    s = _viewr_node(ft)
    _unchecked_deep(left, s.rest, digit(s.value))
end
_deepr(left::DigitFTRep{T}, ft::FingerTreeRep{T}, right::DigitFTRep{T}) where {T} =
    _unchecked_deep(left, ft, right)

function deepr(
    left::DigitFTRep{T},
    middle::FingerTreeRep{T},
    right::DigitFragment{T},
)::FingerTreeRep{T} where {T}
    _deepr(left, middle, right)
end

function _split(ft::EmptyFT{T}, i::Int)::TreeSplit{T} where {T}
    throw(BoundsError(ft, i))
end

function _split(ft::SingleFT{T}, i::Int)::TreeSplit{T} where {T}
    empty = EmptyFT{T}()
    TreeSplit{T}(empty, ft.a, empty)
end

function _split(ft::DeepFT{T}, i::Int)::TreeSplit{T} where {T}
    j = len(ft.left)
    if i <= j
        s = split(ft.left, i)
        left = isnothing(s.left) ? EmptyFT{T}() : toftree(something(s.left))
        return TreeSplit{T}(left, s.value, deepl(s.right, ft.succ, ft.right))
    end
    i -= j
    j = len(ft.succ)
    if i <= j
        s = _split(ft.succ, i)
        ml = s.left
        xs = s.value
        mr = s.right
        i -= len(ml)
        ns = isa(xs, T) ? Tree23Split{T}(nothing, xs, nothing) : _split23(xs, i)
        left = deepr(ft.left, ml, ns.left)
        right = deepl(ns.right, mr, ft.right)
        return TreeSplit{T}(left, ns.value, right)
    end
    i -= j
    j = len(ft.right)
    if i <= j
        s = split(ft.right, i)
        right = isnothing(s.right) ? EmptyFT{T}() : toftree(something(s.right))
        return TreeSplit{T}(deepr(ft.left, ft.succ, s.left), s.value, right)
    end
    throw(BoundsError())
end

function split(ft::FingerTree{T}, i::Integer) where {T}
    index = Int(i)
    1 <= index <= length(ft) || throw(BoundsError(ft, i))
    s = _split(ft, index)
    s.left, s.value, s.right
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
@inline function Base.iterate(ft::FingerTree{T}) where {T}
    state = IterationState{T}(TraversalBranch{T}[], Int[], T[], 1)
    sizehint!(state.branches, 16)
    sizehint!(state.next, 16)
    sizehint!(state.pending, 4)
    _descend!(state, ft::FingerTreeRep{T})
    _iterate(state)
end

@inline Base.iterate(::FingerTree{T}, state::IterationState{T}) where {T} = _iterate(state)

_descend!(::IterationState, ::EmptyFT) = nothing

function _descend!(state::IterationState{T}, branch::TraversalBranch{T}) where {T}
    push!(state.branches, branch)
    push!(state.next, 1)
    nothing
end

function _descend!(state::IterationState{T}, single::SingleFT{T}) where {T}
    child = single.a
    if child isa Tree23{T}
        _descend!(state, child::Tree23Rep{T})
    else
        _descend!(state, child::T)
    end
end

function _descend!(state::IterationState{T}, leaf::DLeaf{T}) where {T}
    empty!(state.pending)
    for child in leaf.child
        push!(state.pending, child)
    end
    state.pending_next = 1
    nothing
end

function _descend!(state::IterationState{T}, leaf::Leaf23{T}) where {T}
    empty!(state.pending)
    push!(state.pending, leaf.a)
    push!(state.pending, leaf.b)
    !isnothing(leaf.c) && push!(state.pending, something(leaf.c))
    state.pending_next = 1
    nothing
end

function _descend!(state::IterationState{T}, value::T) where {T}
    empty!(state.pending)
    push!(state.pending, value)
    state.pending_next = 1
    nothing
end

@inline function _iterate(state::IterationState{T}) where {T}
    while true
        if state.pending_next <= length(state.pending)
            value = state.pending[state.pending_next]
            state.pending_next += 1
            return value, state
        end

        isempty(state.branches) && return nothing

        branch = state.branches[end]
        next = state.next[end]

        if branch isa DeepFT{T}
            if next == 1
                state.next[end] = 2
                child = branch.left
            elseif next == 2
                state.next[end] = 3
                child = branch.succ
            else
                pop!(state.branches)
                pop!(state.next)
                child = branch.right
            end
            _descend!(state, child)
        elseif branch isa DNode
            if next == width(branch)
                pop!(state.branches)
                pop!(state.next)
            else
                state.next[end] = next + 1
            end
            _descend!(state, branch.child[next])
        else
            if next == width(branch)
                pop!(state.branches)
                pop!(state.next)
            else
                state.next[end] = next + 1
            end
            child = next == 1 ? branch.a : next == 2 ? branch.b : something(branch.c)
            _descend!(state, child)
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
concat(l::FingerTree{T}, r::FingerTree{T}) where {T} = app3(l, (), r)
concat(l::FingerTree{T}, x, r::FingerTree{T}) where {T} = app3(l, (x,), r)

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

end
