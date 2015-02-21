module FingerTrees
import Base: reduce, start, next, done, length, collect, split

export FingerTree, conjl, conjr, splitl, splitr, len, fingertree, flat, split, travstruct, traverse, concat

abstract FingerTree{K}

immutable EmptyFT{K<:Union(Char, Number)} <: FingerTree{K} 
end



immutable Node23{T, K<:Union(Char, Number)} 
    a::T
    b::T
    c::Nullable{T}
    len::Int
    depth::Int
    function Node23(a, b) 
        if !(dep(a)==dep(b)) error("Try to construct uneven Node2") end
        new(a, b, Nullable{T}(), len(a)+len(b), dep(a)+1)
    end
    function Node23(a, b, c) 
        if !(dep(a)==dep(b)==dep(c)) error("Try to construct uneven Node3") end
        new(a,b,c, len(a)+len(b)+len(c), dep(a)+1)
    end
end

Node23{T}(a::T,b::T,c::T) = Node23{T, T}(a,b,c)
Node23{T}(a::T,b::T) = Node23{T, T}(a,b)
Node23{T,K}(a::Node23{T,K},b::Node23{T,K},c::Node23{T,K}) = Node23{Node23, K}(a,b,c)
Node23{T,K}(a::Node23{T,K},b::Node23{T,K}) = Node23{Node23, K}(a,b)
astuple(n::Node23) = isnull(n.c) ? (n.a, n.b) : (n.a, n.b, get(n.c))


immutable DigitFT{N, T, K}
    child::NTuple{N, T}
    len::Int
    depth::Int
    DigitFT() = new((),0,0)
    DigitFT(a) = new((a,), len(a), dep(a))
    function DigitFT(a,b) 
        if dep(a)!=dep(b) error("Try to construct uneven digit $b") end
        new((a,b), len(a)+len(b), dep(a))
    end
    function DigitFT(a,b,c) 
        if !(dep(a)==dep(b)==dep(c)) error("Try to construct uneven digit $b ") end
        new((a,b,c), len(a)+len(b)+len(c), dep(a))
    end
    function DigitFT(a,b,c,d) 
        if !(dep(a)==dep(b)==dep(c)==dep(d)) error("Try to construct uneven digit $b") end
        new((a,b,c,d), +(len(a),len(b),len(c),len(d)), dep(a))
    end    
end

typealias DigitFT0{T,K} DigitFT{0,T,K}
typealias DigitFT1{T,K} DigitFT{1,T,K}
typealias DigitFT2{T,K} DigitFT{2,T,K}
typealias DigitFT3{T,K} DigitFT{3,T,K}
typealias DigitFT4{T,K} DigitFT{4,T,K}
#typealias DigitFT04{T,K} Union(DigitFT{0,T,K},DigitFT{1,T,K},DigitFT{2,T,K},DigitFT{3,T,K},DigitFT{4,T,K})

DigitFT{T}(a::T) = DigitFT1{T,T}(a)  
DigitFT{T}(a::T,b::T) = DigitFT2{T,T}(a,b)  
DigitFT{T}(a::T,b::T,c::T) = DigitFT3{T,T}(a,b,c)  
DigitFT{T}(a::T,b::T,c::T,d::T) = DigitFT4{T,T}(a,b,c,d)  
DigitFT{T,K}(a::Node23{T,K}) = DigitFT1{Node23,K}(a)  
DigitFT{T,K}(a::Node23{T,K},b) = DigitFT2{Node23,K}(a,b)  
DigitFT{T,K}(a::Node23{T,K},b,c) = DigitFT3{Node23,K}(a,b,c)  
DigitFT{T,K}(a::Node23{T,K},b,c,d) = DigitFT4{Node23,K}(a,b,c,d)  

function digit{T,K}(n::Node23{T,K})
    if isnull(n.c) 
        DigitFT2{T,K}(n.a, n.b)
    else
        DigitFT3{T,K}(n.a, n.b, get(n.c))
    end
end    


immutable SingleFT{K} <: FingerTree{K} 
    a::Union(Node23,K)
end
SingleFT{K}(a::K) = SingleFT{K}(a)
SingleFT{T,K}(a::Node23{T,K}) = SingleFT{K}(a)


immutable DeepFT{K<:Union(Int,Char)} <: FingerTree{K}
    left::DigitFT#{T}
    succ::FingerTree
    right::DigitFT#{T}
    len::Int
    depth::Int
    function DeepFT(l::DigitFT, s::FingerTree{K} , r::DigitFT)
        if !(dep(l) == dep(s) - 1 == dep(r) || (isempty(s) && dep(l) == dep(r)))
            dump(l); dump(s);dump(r)
            error("Attempt to construct uneven finger tree")
        end
        new(l, s, r, len(l) + len(s) + len(r), dep(l))
    end
    function DeepFT(ll, s::FingerTree{K} , rr)
        l = DigitFT(ll...)
        r = DigitFT(rr...)
        
        if !(dep(l) == dep(s) - 1 == dep(r) || (isempty(s) && dep(l) == dep(r)))
            dump(l); dump(s);dump(r)
            error("Attempt to construct uneven finger tree")
        end
        new(l, s, r, len(l) + len(s) + len(r), dep(l))
    end
end
DeepFT{N, K}(l::DigitFT{N, Node23,K}, s::FingerTree{K}, r::DigitFT) = DeepFT{K}(l, s, r) 
DeepFT{N, K}(l::DigitFT{N, K,K}, s::FingerTree{K}, r::DigitFT) = DeepFT{K}(l, s, r) 
DeepFT{K}(l, s::FingerTree{K}, r) = DeepFT{K}(l,s,r)
DeepFT{T,K}(l::Node23{T,K}, s::FingerTree{K}, r) = DeepFT{K}(DigitFT(l), s, DigitFT(r)) 

DeepFT{N,T, K}(l::DigitFT{N,T, K}, r::DigitFT) = DeepFT{K}(l, EmptyFT{K}, r)
DeepFT{N,T, K}(l::DigitFT, r::DigitFT{N,T,K}) = DeepFT{K}(l, EmtpyFT{K}, r)
DeepFT{N, K}(l::DigitFT{N, Node23,K}, r::DigitFT) = DeepFT{K}(l, EmptyFT{K}(), r) 
DeepFT{T,K}(l::Node23{T,K}, r) = DeepFT{K}(DigitFT(l),EmptyFT{K}(), DigitFT(r)) 
DeepFT{T}(l::T, r::T) = DeepFT{T}(DigitFT(l), EmptyFT{T}(), DigitFT(r))
DeepFT{N,M,T,K}(l::DigitFT{N,T,K}, e::EmptyFT{K}, r::DigitFT{M,T,K}) = DeepFT{K}(l, _,r)


dep(_) = 0
dep(n::Node23) = n.depth
dep(d::DigitFT) = d.depth
dep(s::SingleFT) = dep(s.a)
dep(_::EmptyFT) = 0
dep(ft::DeepFT) = ft.depth


fteltype(b) = typeof(b)
fteltype{T}(b::FingerTree{T}) = fteltype(T)
fteltype{T}(b::DigitFT{T}) = T

# TODO: allow other counting functions
len(a) = 1
len{K, S}(n::NTuple{K, S}) = K
len(_::()) = 0
len{K}(n::NTuple{K, Node23}) = mapreduce(len, +, n)


len(n::Node23) = n.len
len(digit::DigitFT) = digit.len
len(_::EmptyFT) = 0

len(deep::DeepFT) = deep.len
len(n::SingleFT) = len(n.a)
length(ft::FingerTree) = len(ft)

isempty(_::EmptyFT) = true
isempty(_::FingerTree) = false

width(digit::DigitFT) = length(digit.child)
width(n::Node23) = length(isnull(n.c) ? 3 : 2)

function conjl(t) 
    ft = t[end]
    for i in length(t)-1:-1:1
        ft = conjl(t[i], ft)
    end
    ft
end
function conjr(t) 
    ft = t[1]
    for x in t[2:end]
        ft = conjr(ft, x)
    end
    ft
end


FingerTree(K,ft::FingerTree) = ft
function FingerTree(K,t)
    ft = EmptyFT{K}()
    for x in t
        ft = conjr(ft, x)
    end
    ft
end

fingertree(a) = SingleFT(a)
fingertree(a,b) = DeepFT(a, b)
fingertree(a,b,c) = DeepFT(DigitFT(a,b), DigitFT(c))
fingertree(a,b,c,d) = DeepFT(DigitFT(a,b), DigitFT(c,d))
fingertree(a,b,c,d,e) = DeepFT(DigitFT(a,b,c), DigitFT(d,e))
fingertree(a,b,c,d,e,f) = DeepFT(DigitFT(a,b,c), DigitFT(d,e,f))
fingertree(a,b,c,d,e,f,g) = DeepFT(DigitFT(a,b,c,d), DigitFT(e,f,g))
fingertree(a,b,c,d,e,f,g,h) = DeepFT(DigitFT(a,b,c,d), DigitFT(e,f,g,h))


conjl{T,K}(a, digit::DigitFT0{T,K}) = DigitFT1{T,K}(a)
conjl{T,K}(a, digit::DigitFT1{T,K}) = DigitFT2{T,K}(a, digit.child...)
conjl{T,K}(a, digit::DigitFT2{T,K}) = DigitFT3{T,K}(a, digit.child...)
conjl{T,K}(a, digit::DigitFT3{T,K}) = DigitFT4{T,K}(a, digit.child...)

conjr{T,K}(digit::DigitFT0{T,K}, a) = DigitFT1{T,K}(a)
conjr{T,K}(digit::DigitFT1{T,K}, a) = DigitFT2{T,K}(digit.child..., a)
conjr{T,K}(digit::DigitFT2{T,K}, a) = DigitFT3{T,K}(digit.child..., a)
conjr{T,K}(digit::DigitFT3{T,K}, a) = DigitFT4{T,K}(digit.child..., a)


splitl{T,K}(digit::DigitFT1{T,K}) = digit.child[1], DigitFT0{(),K}()
splitl{T,K}(digit::DigitFT2{T,K}) = digit.child[1], DigitFT1{T,K}(digit.child[2:end]...)
splitl{T,K}(digit::DigitFT3{T,K}) = digit.child[1], DigitFT2{T,K}(digit.child[2:end]...)
splitl{T,K}(digit::DigitFT4{T,K}) = digit.child[1], DigitFT3{T,K}(digit.child[2:end]...)

splitr{T,K}(digit::DigitFT1{T,K}) = DigitFT0{(),K}(), digit.child[end]
splitr{T,K}(digit::DigitFT2{T,K}) = DigitFT1{T,K}(digit.child[1:end-1]...), digit.child[end]
splitr{T,K}(digit::DigitFT3{T,K}) = DigitFT2{T,K}(digit.child[1:end-1]...), digit.child[end]
splitr{T,K}(digit::DigitFT4{T,K}) = DigitFT3{T,K}(digit.child[1:end-1]...), digit.child[end]

function Base.getindex(d::DigitFT, i)
    for k in 1:width(d)
        j = len(d.child[k]) 
        if i <= j return getindex(d.child[k], i) end
        i -= j    
    end
    throw(BoundsError())
end
function Base.getindex(n::Node23, i)
    j = len(n.a)
    i <= j && return getindex(n.a, i)
    i -= j; j = len(n.b)
    i <= j && return getindex(n.b, i)
    if !isnull(n.c)
        i -= j; j = len(get(n.c))
        i <= j && return getindex(get(n.c), i)
    end
    println(i, " ", j, n)
    throw(BoundsError())
end

Base.getindex(::EmptyFT, i) = throw(BoundsError())
Base.getindex(ft::SingleFT, i) = getindex(ft.a, i)
function Base.getindex(ft::DeepFT, i)
    j = len(ft.left)
    if i <= j return getindex(ft.left, i) end
    i -= j; j = len(ft.succ)
    if i <= j return getindex(ft.succ, i) end
    i -= j; j = len(ft.right)
    if i <= j return getindex(ft.right, i) end
    println(i, j, ft)
    throw(BoundsError())
end



conjl(a, _::EmptyFT) = SingleFT(a)
conjr(_::EmptyFT, a) = SingleFT(a)

conjl{K}(a, single::SingleFT{K}) = DeepFT(a,EmptyFT{K}(), single.a)
conjr{K}(single::SingleFT{K}, a) = DeepFT(single.a, EmptyFT{K}(),a)
#conjl{T,K}(a::Node23{T,K}, single::SingleFT{K}) = DeepFT{K}(DigitFT1(a), DigitFT1(single.a))
#conjr{T,K}(single::SingleFT{K}, a::Node23{T,K}) = DeepFT{K}(DigitFT1(single.a), DigitFT1(a))




function splitl(_::EmptyFT)
    error("finger tree empty")
end
splitr(l::EmptyFT) = splitl(l)

function splitl{K}(single::SingleFT{K})
    single.a, EmptyFT{K}()
end
function splitr{K}(single::SingleFT{K})
     EmptyFT{K}(), single.a
end
function conjl(a, ft::DeepFT)
    if width(ft.left) < 4
        #println(typeof((conjl(a,ft.left), ft.succ, ft.right)))
        r = DeepFT(conjl(a,ft.left), ft.succ, ft.right)
        #println("DONE")
        #r
    else
        f = (Node23(ft.left.child[2:4]...))
        #println(typeof((DigitFT(a, ft.left.child[1]), conjl(f,ft.succ), ft.right)))
        r = DeepFT(DigitFT(a, ft.left.child[1]), conjl(f,ft.succ), ft.right)
        #println("DONE")
        #r
    end
end

function conjr(ft::DeepFT, a)
    if width(ft.right) < 4
        #println(typeof((ft.left, ft.succ, conjr(ft.right,a))))
        r = DeepFT(ft.left, ft.succ, conjr(ft.right, a))
        #println("DONE")
        #r
    else        
        f = Node23(ft.right.child[1:3]...)
        #println(typeof((ft.left, conjr(ft.succ, f), DigitFT(ft.right.child[4], a))))
        r = DeepFT(ft.left, conjr(ft.succ, f), DigitFT(ft.right.child[4], a))
        #println("DONE")
        #r
    end
end

function splitl(ft::DeepFT)
    a, as = splitl(ft.left)
    if width(as) > 0
        return a, DeepFT(as, ft.succ, ft.right)
    else
        if isempty(ft.succ) 
            b, bs = splitl(ft.right)
            if width(bs) > 0
                return a, DeepFT(DigitFT(b), ft.succ, bs)
            else
                return a, SingleFT(b)
            end
        else
            c, gt = splitl(ft.succ) 
            return a, DeepFT(digit(c), gt, ft.right)
        end
    end
end
function splitr(ft::DeepFT)
    as, a = splitr(ft.right)
    if width(as) > 0
        return DeepFT(ft.left, ft.succ, as), a
    else
        if isempty(ft.succ) 
            bs, b = splitr(ft.left)
            if width(bs) > 0
                return DeepFT(bs, ft.succ, DigitFT(b)), a
            else
                return SingleFT(b), a
            end
        else
             gt, c = splitr(ft.succ)
             return DeepFT(ft.left, gt, digit(c)), a
        end
    end
end

function split(ft::EmptyFT, i)
    error("can't split empty FingerTree")
end

function split{K}(ft::SingleFT{K}, i)
    if isa(ft.a, Node23) return split(ft.a, i) end
    
    e = EmptyFT{K}() 
    return e, ft.a, e
end

function splitv(t, i)
    t[1:i-1], t[i], t[i+1:end]
end

function split(d::DigitFT, i)
    for k in 1:width(d)
        j = len(d.child[k]) 
        if i <= j 
            return splitv(d.child, k) end
        i -= j    
    end
    throw(BoundsError())
end
function split(n::Node23, i)
    if isnull(n.c)
        j = len(n.a) 
        i <= j  && return (), n.a, (n.b,)
        i -= j; j = len(n.b) 
        i <= j  && return (n.a,), n.b, ()
    else 
        j = len(n.a) 
        i <= j  && return (), n.a, (n.b,get(n.c))
        i -= j; j = len(n.b) 
        i <= j  && return (n.a,), n.b, (get(n.c))
        i -= j; j = len(get(n.c)) 
        i <= j  && return (n.a,n.b), get(n.c), ()
    end
    throw(BoundsError())
end


function collect(xs::FingerTree)
     v = Array(fteltype(xs), len(xs))
     traverse((x, i) -> (v[i] = x;), xs)
     v
end

rotr(d, ft::EmptyFT) = fingertree(d.child...)
function rotr{K}(d, ft::FingerTree{K})
    ft, x = splitr(ft)
    y = isa(x, Node23) ? astuple(x) : (x,)
    if isa(ft, SingleFT) && !isa(ft.a, Node23) return fingertree(d.child..., ft.a, y...) end
    DeepFT{K}(DigitFT(d.child...), ft, DigitFT(y...))
end
rotl(ft::EmptyFT, d) = fingertree(d.child...)
function rotl{K}(ft::FingerTree{K},d)
    x, ft = splitl(ft)
    y = isa(x, Node23) ? astuple(x) : (x,) 
    if isa(ft, SingleFT) && !isa(ft.a, Node23) return fingertree(y..., ft.a, d.child...) end
    DeepFT{K}(DigitFT(y...), ft, DigitFT(d.child...))
end

 
deepl(t::(), ft::FingerTree, d) = rotl(ft, d) 
deepl{K}(t::Node23, ft::FingerTree{K}, d) = DeepFT{K}(DigitFT(t), ft, d)
deepl{K}(t, ft::FingerTree{K}, d) = DeepFT{K}(DigitFT(t...), ft, d)

deepr(d, ft::FingerTree, t::()) = rotr(d, ft) 
deepr{K}(d, ft::FingerTree{K}, t::Node23) = DeepFT{K}(d, ft, DigitFT(t))
deepr{K}(d, ft::FingerTree{K}, t) = DeepFT{K}(d, ft, DigitFT(t...))

function split{K}(ft::DeepFT{K}, i)
    j = len(ft.left)
    if i <= j
        l, x, r = split(ft.left, i) 
        return FingerTree(K,l), x, deepl(r, ft.succ, ft.right)
    end
    i -= j; j = len(ft.succ)
    if i <= j 
        ml, xs, mr = split(ft.succ, i)    
        i -= len(ml)
        l, x, r =  isa(xs,Node23) ? split(xs, i) : ((),xs,())
        ml = FingerTree(K,ml)
        mr = FingerTree(K,mr)
        return deepr(ft.left, ml, l), x, deepl(r, mr, ft.right)
    end
    i -= j; j = len(ft.right)
    if i <= j 
        l, x, r = split(ft.right, i) 
        return deepr(ft.left, ft.succ, l), x, FingerTree(K,r)
    end
    throw(BoundsError())
end


Base.reduce(op::Function, v, ::EmptyFT) = v
Base.reduce(op::Function, v, t::SingleFT) = reduce(op, v, ft.a)
function Base.reduce(op::Function, v, d::DigitFT)
    for k in 1:width(d)
        v = reduce(op, v, d.child[k])
    end
    v
end
function Base.reduce(op::Function, v, n::Node23)
    t = tuple(n)
    for k in 1:width(t)
        v = reduce(op, v, t[k])
    end
    v
end
function Base.reduce(op::Function, v, ft::DeepFT)
    v = reduce(op, v, ft.left)
    v = reduce(op, v, ft.succ)
    v = reduce(op, v, ft.right)
end

traverse(op::Function, a, i) = (op(a, i); i + 1)
traverse(op::Function,  ::EmptyFT, i) = return i
traverse(op::Function, ft::SingleFT, i) = traverse(op, ft.a, i)

function traverse(op::Function, n::DigitFT, i)
    for k in 1:width(n)
        i = traverse(op, n.child[k], i)
    end
    i
end
function traverse(op::Function, n::Node23, i)
    i = traverse(op, n.a, i)
    i = traverse(op, n.b, i)
    !isnull(n.c) && (i = traverse(op, get(n.c), i))
    i
end
function traverse(op::Function, ft::DeepFT, i)
    i = traverse(op, ft.left, i)
    i = traverse(op, ft.succ, i)
    traverse(op, ft.right, i)
end
traverse(op, ft) = (traverse(op, ft, 1);)


#Traversal with a op that takes also the depth as input
travstruct(op::Function, a, d) = (op(a, d);d)
travstruct(op::Function,  ::EmptyFT, d) = return d
travstruct(op::Function, ft::SingleFT, d) = travstruct(op, ft.a, d)
function travstruct{T<:Union(DigitFT, Node23)}(op::Function,n::T, d)
    d2 = travstruct(op, n.child[1], d)
    for k in 2:width(n)
        assert(d2 == travstruct(op, n.child[k], d ))
    end
    d2
end
function travstruct(op::Function, ft::DeepFT, d)
    d2 = travstruct(op, ft.left, d) 
    assert(d2 == travstruct(op, ft.succ, d + 1) - 1 ==  travstruct(op, ft.right, d))
    d2 
end
travstruct(op, ft) = travstruct(op, ft, 1)


# Scheme:
# state = start(I)
# while !done(I, state)
#   (i, state) = next(I, state)
#     # body
# end
# rather slow
function start(ft::FingerTree)
    trav = () -> traverse((x,i) -> produce(x), ft)
    t = Task(trav)
    i = consume(t)
    (i, t)
end
function next(ft::FingerTree, state)
    state[1], (consume(state[2]), state[2])
end
function done(ft::FingerTree, state)
    state[2].state==:done
end
 
 
app3(l::SingleFT, ts, r::SingleFT) = fingertree(l.a, ts..., r.a)
app3(::EmptyFT, ts, r::EmptyFT) =     fingertree(ts...) # for example ts::NTuple{N,Node23}, 
app3(::EmptyFT, ts, r::SingleFT) = fingertree(ts..., r.a)
app3(l::SingleFT, ts, ::EmptyFT) = fingertree(l.a, ts...)
app3(::EmptyFT, ts, r) = conjl(tuple(ts..., r))
app3(l, ts, ::EmptyFT) = conjr(l, ts...)
app3(x::SingleFT, ts, r) = conjl(x.a, conjl(tuple(ts..., r)))
app3(l, ts, x::SingleFT) = conjr(conjr(tuple(l, ts...)), x.a)


nodes(a,b) = (Node23(a, b),)
nodes(a,b,c) = (Node23(a,b,c),)
nodes(a,b,c,d) = (Node23(a, b), Node23(c,d))
nodes(a,b,c,xs...) = tuple(Node23(a,b,c), nodes(xs...)...)

app3(l::DeepFT, ts, r::DeepFT) = 
    DeepFT(l.left, app3(l.succ, nodes(l.right.child..., ts..., r.left.child...),r.succ),  r.right)
concat(l::FingerTree, r::FingerTree) = app3(l, (), r)
concat(l::FingerTree, x, r::FingerTree) = app3(l, (x,), r)


Base.show(io::IO, d::DigitFT) = print(io, d.child...)
Base.show(io::IO, n::Node23) = len(n) < 20 ? print(io, "^", n.a, n.b, isnull(n.c) ? "" : get(n.c)) : print(" ... ")
Base.show(io::IO, d::DeepFT) = print(io, "(", d.left, " .. ", d.succ, " .. ", d.right, ")")
Base.show(io::IO, d::SingleFT) = print(io, "(", d.a, ")")
Base.show(io::IO, d::EmptyFT) = print(io, "(/)")


end
