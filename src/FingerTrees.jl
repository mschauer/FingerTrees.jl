module FingerTrees
import Base: reduce, length, collect, split, eltype, isempty

export FingerTree, EmptyFT
export assoc, concat, conjl, conjr, split, splitl, splitr

# ---------------------------------------------------------------------------
# Internal representation
# ---------------------------------------------------------------------------

abstract type FingerTree{T} end
abstract type Tree23{T} end

struct Leaf23{T} <: Tree23{T}
    a::T
    b::T
    c::Union{Nothing,T}
    len::Int
    depth::Int
    function Leaf23(a::T, b::T) where {T}
        dep(a) == dep(b) || throw(ArgumentError("cannot construct an uneven 2-leaf"))
        new{T}(a, b, nothing, len(a) + len(b), dep(a) + 1)
    end
    function Leaf23(a::T, b::T, c::T) where {T}
        dep(a) == dep(b) == dep(c) || throw(ArgumentError("cannot construct an uneven 3-leaf"))
        new{T}(a, b, c, len(a) + len(b) + len(c), dep(a) + 1)
    end
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
end

const Tree23Rep{T} = Union{Leaf23{T},Node23{T}}

Tree23(a,b,c) = Leaf23(a,b,c)
Tree23(a,b) = Leaf23(a,b)
Tree23(a::Tree23{T},b::Tree23{T},c::Tree23{T}) where {T} = Node23(a,b,c)
Tree23(a::Tree23{T},b::Tree23{T}) where {T} = Node23(a,b)

abstract type DigitFT{T,N} end

struct DLeaf{T,N} <: DigitFT{T,N} # Constructors restrict N to 1:4.
    child::NTuple{N,T}
    len::Int
    depth::Int
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


struct DNode{T,N} <: DigitFT{T,N}
    child::NTuple{N,Tree23Rep{T}}
    len::Int
    depth::Int
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

function digit(n::Tree23{T}) where T
    if isnothing(n.c)
        DigitFT(n.a, n.b)
    else
        DigitFT(n.a, n.b, something(n.c))
    end
end
digit(t::NTuple{N,T}) where {N, T} = DigitFT(t...)
digit(t::T) where {T} = DigitFT(t)

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
end

const FingerTreeRep{T} = Union{EmptyFT{T}, SingleFT{T}, DeepFT{T}}

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
fingertree(a, b) = DeepFT(a, b)
fingertree(a, b, c) = DeepFT(DigitFT(a, b), DigitFT(c))
fingertree(a, b, c, d) = DeepFT(DigitFT(a, b), DigitFT(c, d))
fingertree(a, b, c, d, e) = DeepFT(DigitFT(a, b, c), DigitFT(d, e))
fingertree(a, b, c, d, e, f) = DeepFT(DigitFT(a, b, c), DigitFT(d, e, f))
fingertree(a, b, c, d, e, f, g) = DeepFT(DigitFT(a, b, c, d), DigitFT(e, f, g))
fingertree(a, b, c, d, e, f, g, h) = DeepFT(DigitFT(a, b, c, d), DigitFT(e, f, g, h))

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

conjl(a, digit::DigitFT1{T}) where {T} = DigitFT(a, digit.child[1])
conjl(a, digit::DigitFT2{T}) where {T} = DigitFT(a, digit.child[1], digit.child[2])
conjl(a, digit::DigitFT3{T}) where {T} = DigitFT(a, digit.child...)

conjr(digit::DigitFT1{T}, a) where {T} = DigitFT(digit.child[1], a)
conjr(digit::DigitFT2{T}, a) where {T} = DigitFT(digit.child[1], digit.child[2], a)
conjr(digit::DigitFT3{T}, a) where {T} = DigitFT(digit.child..., a)


splitl(digit::DigitFT2{T}) where {T} = digit.child[1], DigitFT(digit.child[2])
splitl(digit::DigitFT3{T}) where {T} = digit.child[1], DigitFT(digit.child[2:end]...)
splitl(digit::DigitFT4{T}) where {T} = digit.child[1], DigitFT(digit.child[2:end]...)

splitr(digit::DigitFT2{T}) where {T} = DigitFT(digit.child[1]), digit.child[end]
splitr(digit::DigitFT3{T}) where {T} = DigitFT(digit.child[1:end-1]...), digit.child[end]
splitr(digit::DigitFT4{T}) where {T} = DigitFT(digit.child[1:end-1]...), digit.child[end]

# ---------------------------------------------------------------------------
# Indexing
# ---------------------------------------------------------------------------

function Base.getindex(d::DigitFT{T}, i::Int)::T where {T}
    for k in 1:width(d)
        j = len(d.child[k])
        if i <= j
            return getindex(d.child[k], i)
        end
        i -= j
    end
    throw(BoundsError())
end
function Base.getindex(n::Tree23{T}, i::Int)::T where {T}
    j = len(n.a)
    i <= j && return getindex(n.a, i)
    i -= j; j = len(n.b)
    i <= j && return getindex(n.b, i)
    if !isnothing(n.c)
        i -= j; j = len(something(n.c))
        i <= j && return getindex(something(n.c), i)
    end
    throw(BoundsError())
end

function Base.getindex(::EmptyFT{T}, i::Int)::T where {T}
    throw(BoundsError())
end
function Base.getindex(ft::SingleFT{T}, i::Int)::T where {T}
    getindex(ft.a, i)
end
function Base.getindex(ft::DeepFT{T}, i::Int)::T where {T}
    j = len(ft.left)
    i <= j && return getindex(ft.left, i)
    i -= j

    j = len(ft.succ)
    i <= j && return getindex(ft.succ, i)
    i -= j

    j = len(ft.right)
    i <= j && return getindex(ft.right, i)
    throw(BoundsError())
end

Base.getindex(ft::FingerTree, i::Integer) = getindex(ft, Int(i))

conjl(a::T, _::EmptyFT{T}) where {T} = SingleFT(a)
conjr(_::EmptyFT{T}, a::T) where {T} = SingleFT(a)

conjl(a::Tree23{T}, _::EmptyFT{T}) where {T} = SingleFT(a)
conjr(_::EmptyFT{T}, a::Tree23{T}) where {T} = SingleFT(a)

conjl(a, single::SingleFT{K}) where {K} = DeepFT(a, EmptyFT{K}(), single.a)
conjr(single::SingleFT{K}, a) where {K} = DeepFT(single.a, EmptyFT{K}(), a)

splitl(ft::EmptyFT) = throw(BoundsError(ft))
splitr(l::EmptyFT) = splitl(l)

function splitl(single::SingleFT{K}) where {K}
    single.a, EmptyFT{K}()
end
function splitr(single::SingleFT{K}) where {K}
    EmptyFT{K}(), single.a
end
function conjl(a, ft::DeepFT{T}) where {T}
    if width(ft.left) < 4
        DeepFT(conjl(a, ft.left), ft.succ, ft.right)
    else
        f = Tree23(ft.left.child[2], ft.left.child[3], ft.left.child[4])
        DeepFT(DigitFT(a, ft.left.child[1]), conjl(f, ft.succ), ft.right)
    end
end

function conjr(ft::DeepFT, a)
    if width(ft.right) < 4
        DeepFT(ft.left, ft.succ, conjr(ft.right, a))
    else
        f = Tree23(ft.right.child[1:3]...)
        DeepFT(ft.left, conjr(ft.succ, f), DigitFT(ft.right.child[4], a))
    end
end

function splitl(ft::DeepFT)
    if width(ft.left) > 1
        a, as = splitl(ft.left)
        return a, DeepFT(as, ft.succ, ft.right)
    else
        a = ft.left.child[1]
        if isempty(ft.succ)
            return a, toftree(ft.right)
        else
            c, gt = splitl(ft.succ)
            return a, DeepFT(digit(c), gt, ft.right)
        end
    end
end
function splitr(ft::DeepFT)
    if width(ft.right) > 1
        as, a = splitr(ft.right)
        return DeepFT(ft.left, ft.succ, as), a
    else
        a = ft.right.child[1]
        if isempty(ft.succ)
            return toftree(ft.left), a
        else
            gt, c = splitr(ft.succ)
            return DeepFT(ft.left, gt, digit(c)), a
        end
    end
end

# ---------------------------------------------------------------------------
# Splitting and persistent update
# ---------------------------------------------------------------------------

const DigitFragment{T} = Union{Nothing,DigitFTRep{T}}
const SplitValue{T} = Union{T,Tree23Rep{T}}

struct DigitSplit{T}
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
    i <= j && return DigitSplit{T}(nothing, a, DigitFT(b))
    i -= j
    i <= len(b) && return DigitSplit{T}(DigitFT(a), b, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,3}, i) where {T}
    a, b, c = d.child
    j = len(a)
    i <= j && return DigitSplit{T}(nothing, a, DigitFT(b, c))
    i -= j
    j = len(b)
    i <= j && return DigitSplit{T}(DigitFT(a), b, DigitFT(c))
    i -= j
    i <= len(c) && return DigitSplit{T}(DigitFT(a, b), c, nothing)
    throw(BoundsError())
end

function split(d::DigitFT{T,4}, i) where {T}
    a, b, c, e = d.child
    j = len(a)
    i <= j && return DigitSplit{T}(nothing, a, DigitFT(b, c, e))
    i -= j
    j = len(b)
    i <= j && return DigitSplit{T}(DigitFT(a), b, DigitFT(c, e))
    i -= j
    j = len(c)
    i <= j && return DigitSplit{T}(DigitFT(a, b), c, DigitFT(e))
    i -= j
    i <= len(e) && return DigitSplit{T}(DigitFT(a, b, c), e, nothing)
    throw(BoundsError())
end

function split(n::Leaf23, i)
    if isnothing(n.c)
        j = len(n.a)
        i <= j && return nothing, n.a, DigitFT(n.b)
        i -= j
        i <= len(n.b) && return DigitFT(n.a), n.b, nothing
    else
        c = something(n.c)
        j = len(n.a)
        i <= j && return nothing, n.a, DigitFT(n.b, c)
        i -= j
        j = len(n.b)
        i <= j && return DigitFT(n.a), n.b, DigitFT(c)
        i -= j
        i <= len(c) && return DigitFT(n.a, n.b), c, nothing
    end
    throw(BoundsError())
end

function split(n::Node23, i)
    if isnothing(n.c)
        j = len(n.a)
        i <= j && return nothing, n.a, DigitFT(n.b)
        i -= j
        i <= len(n.b) && return DigitFT(n.a), n.b, nothing
    else
        c = something(n.c)
        j = len(n.a)
        i <= j && return nothing, n.a, DigitFT(n.b, c)
        i -= j
        j = len(n.b)
        i <= j && return DigitFT(n.a), n.b, DigitFT(c)
        i -= j
        i <= len(c) && return DigitFT(n.a, n.b), c, nothing
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
    x, ft2 = splitl(ft)
    DeepFT(digit(x), ft2, right)
end
_deepl(left::DigitFTRep{T}, ft::FingerTreeRep{T}, right::DigitFTRep{T}) where {T} =
    DeepFT(left, ft, right)

function deepl(
    left::DigitFragment{T},
    middle::FingerTreeRep{T},
    right::DigitFTRep{T},
)::FingerTreeRep{T} where {T}
    _deepl(left, middle, right)
end

_deepr(left::DigitFTRep{T}, ::EmptyFT{T}, ::Nothing) where {T} = toftree(left)
function _deepr(left::DigitFTRep{T}, ft::NonEmptyFT{T}, ::Nothing) where {T}
    ft2, x = splitr(ft)
    DeepFT(left, ft2, digit(x))
end
_deepr(left::DigitFTRep{T}, ft::FingerTreeRep{T}, right::DigitFTRep{T}) where {T} =
    DeepFT(left, ft, right)

function deepr(
    left::DigitFTRep{T},
    middle::FingerTreeRep{T},
    right::DigitFragment{T},
)::FingerTreeRep{T} where {T}
    _deepr(left, middle, right)
end

split(ft::EmptyFT, i) = throw(BoundsError(ft, i))

function split(ft::SingleFT{K}, i) where {K}
    1 <= i <= length(ft) || throw(BoundsError(ft, i))
    e = EmptyFT{K}()
    return e, ft.a, e
end

function split(ft::DeepFT{T}, i) where {T}
    1 <= i <= length(ft) || throw(BoundsError(ft, i))
    j = len(ft.left)
    if i <= j
        s = split(ft.left, i)
        left = isnothing(s.left) ? EmptyFT{T}() : toftree(something(s.left))
        return left, s.value, deepl(s.right, ft.succ, ft.right)
    end
    i -= j
    j = len(ft.succ)
    if i <= j
        ml, xs, mr = split(ft.succ, i)
        i -= len(ml)
        l, x, r = isa(xs, T) ? (nothing, xs, nothing) : split(xs, i)
        return deepr(ft.left, ml, l), x, deepl(r, mr, ft.right)
    end
    i -= j
    j = len(ft.right)
    if i <= j
        s = split(ft.right, i)
        right = isnothing(s.right) ? EmptyFT{T}() : toftree(something(s.right))
        return deepr(ft.left, ft.succ, s.left), s.value, right
    end
    throw(BoundsError())
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
            return DNode(children...)
        end
        i -= j
    end
    throw(BoundsError())
end

function _assoc(n::Leaf23{T}, value::T, i::Int) where {T}
    c = n.c

    j = len(n.a)
    if i <= j
        return isnothing(c) ? Leaf23(value, n.b) : Leaf23(value, n.b, something(c))
    end
    i -= j

    j = len(n.b)
    if i <= j
        return isnothing(c) ? Leaf23(n.a, value) : Leaf23(n.a, value, something(c))
    end

    if !isnothing(c)
        i -= j
        i <= len(something(c)) && return Leaf23(n.a, n.b, value)
    end

    throw(BoundsError())
end

function _assoc(n::Node23{T}, value::T, i::Int) where {T}
    c = n.c

    j = len(n.a)
    if i <= j
        updated = _assoc(n.a, value, i)
        return isnothing(c) ? Node23(updated, n.b) : Node23(updated, n.b, something(c))
    end
    i -= j

    j = len(n.b)
    if i <= j
        updated = _assoc(n.b, value, i)
        return isnothing(c) ? Node23(n.a, updated) : Node23(n.a, updated, something(c))
    end

    if !isnothing(c)
        i -= j
        child = something(c)
        if i <= len(child)
            return Node23(n.a, n.b, _assoc(child, value, i))
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
        return DeepFT(_assoc(ft.left, value, i), ft.succ, ft.right)
    end
    i -= j

    j = len(ft.succ)
    if i <= j
        return DeepFT(ft.left, _assoc(ft.succ, value, i), ft.right)
    end
    i -= j

    j = len(ft.right)
    if i <= j
        return DeepFT(ft.left, ft.succ, _assoc(ft.right, value, i))
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


nodes(a,b) = (Tree23(a, b),)
nodes(a,b,c) = (Tree23(a,b,c),)
nodes(a,b,c,d) = (Tree23(a, b), Tree23(c,d))
nodes(a,b,c,xs...) = tuple(Tree23(a,b,c), nodes(xs...)...)

app3(l::DeepFT, ts, r::DeepFT) =
    DeepFT(l.left, app3(l.succ, nodes(l.right.child..., ts..., r.left.child...), r.succ), r.right)
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
