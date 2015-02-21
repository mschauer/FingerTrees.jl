module FingerTrees
import Base.reduce
import Base.start, Base.next, Base.done
import Base.length

export FingerTree, conjl, conj, splitl, splitr, len, fttree, flat, split, travstruct, traverse, concat, checkinteg

abstract FingerTree{T}
abstract Tree23{T}

immutable EmptyFT{T} <: FingerTree{T} end
#immutable EmptyTree23{T} <: Tree23{T} end


immutable Leaf23{T} <: Tree23{T}
    a::T
end

abstract Node23{T} <: Tree23{T}

immutable Node2{T} <: Node23{T}
    child::NTuple{2, Tree23{T}}
    len::Int
    depth::Int
    function Node2(a, b) 
        if !(dep(a)==dep(b)) error("Try to construct uneven Node2") end
        new((a,b), len(a)+len(b), dep(a)+1)
    end
end
immutable Node3{T} <: Node23{T}
    child::NTuple{3, Tree23{T}}
    len::Int
    depth::Int
    function Node3(a, b, c) 
        if !(dep(a)==dep(b)==dep(c)) error("Try to construct uneven Node3") end
        new((a,b,c), len(a)+len(b)+len(c), dep(a)+1)
    end
end
Node23{T}(a::Tree23{T},b::Tree23{T},c::Tree23{T}) = Node3{T}(a,b,c)
Node23{T}(a::Tree23{T},b::Tree23{T}) = Node2{T}(a,b)

Node23{T}(a::Tree23{T}...) = Node23{T}(a...)

abstract DigitFT{T}

immutable DigitFT0{T} <: DigitFT{T}
    child::NTuple{0, Tree23}
    len::Int
    depth::Int
    DigitFT0() = new((),0,0)
end

immutable DigitFT1{T} <: DigitFT{T}
    child::NTuple{1, Tree23}
    len::Int
    depth::Int
    function DigitFT1(a)
        new((a,), len(a), dep(a))
    end
end

immutable DigitFT2{T} <: DigitFT{T}
    child::NTuple{2, Tree23}
    len::Int
    depth::Int
    function DigitFT2(a,b) 
        if dep(a)!=dep(b) error("Try to construct uneven digit $b") end
        new((a,b), len(a)+len(b), dep(a))
    end
end

immutable DigitFT3{T} <: DigitFT{T}
    child::NTuple{3, Tree23}
    len::Int
    depth::Int
    function DigitFT3(a,b,c) 
        if !(dep(a)==dep(b)==dep(c)) error("Try to construct uneven digit $b ") end
        new((a,b,c), len(a)+len(b)+len(c), dep(a))
    end
end

immutable DigitFT4{T} <: DigitFT{T}
    child::NTuple{4, Tree23}
    len::Int
    depth::Int
    function DigitFT4(a,b,c,d) 
        if !(dep(a)==dep(b)==dep(c)==dep(d)) error("Try to construct uneven digit $b") end
        new((a,b,c,d), +(len(a),len(b),len(c),len(d)), dep(a))
    end    
end
DigitFT{T}(a::Leaf23{T}) =  DigitFT1{T}(a)  

DigitFT{T}(a::Tree23{T},b,c,d) =  DigitFT4{T}(a,b,c,d)  
DigitFT{T}(a::Tree23{T},b,c) =  DigitFT3{T}(a,b,c)  
DigitFT{T}(a::Tree23{T},b) =  DigitFT2{T}(a,b)  
DigitFT{T}(a::Tree23{T}) =  DigitFT1{T}(a)  
DigitFT{T}() =  DigitFT0{T}()  

#DigitFT{T}(b::T...) = DigitFT{T}(map(box,b)...)
#DigitFT{T}(b::Tree23{T}...) = DigitFT{T}(b...)


immutable SingleFT{T} <: FingerTree{T} 
    a::Tree23{T}
end
SingleFT{T}(a::Tree23{T}) = SingleFT{T}(a)

immutable DeepFT{T} <: FingerTree{T}
    left::DigitFT{T}
    succ::FingerTree{T}
    right::DigitFT{T}
    len::Int
    depth::Int
    function DeepFT(l, s::Union(SingleFT, DeepFT), r)
        if !(dep(l) == dep(s) - 1 == dep(r))
            dump(l); dump(s);dump(r)
            error("Attempt to construct uneven finger tree")
        end
        new(l, s, r, len(l) + len(s) + len(r), dep(l))
    end
    function DeepFT(l, r)
        if !(dep(l) == dep(r))
            dump(l); dump(r)
            error("Attempt to construct uneven finger tree")
        end
        new(l,EmptyFT{T}(), r, len(l) + len(r), dep(l))
    end
    function DeepFT(l, s::EmptyFT, r)
        if !(dep(l) == dep(r))
            dump(l); dump(r)
            error("Attempt to construct uneven finger tree")
        end
        new(l,s, r, len(l) + len(r), dep(l))
    end
    
end
DeepFT{T}(l::DigitFT{T}, s, r::DigitFT{T}) = DeepFT{T}(l, s, r) 
DeepFT{T}(l::Tree23{T}, s, r::Tree23{T}) = DeepFT{T}(DigitFT1{T}(l), s, DigitFT1{T}(r))
DeepFT{T}(l::DigitFT{T}, r::DigitFT{T}) = DeepFT{T}(l, r)
DeepFT{T}(l::Tree23{T}, r::Tree23{T}) = DeepFT{T}(DigitFT1{T}(l), DigitFT1{T}(r))
DeepFT{T}(l::DigitFT{T}, _::EmptyFT{T}, r::DigitFT{T}) = DeepFT{T}(l, r)


dep(_::Leaf23) = 0
dep(n::Node23) = n.depth
dep(d::DigitFT) = d.depth
dep(s::SingleFT) = dep(s.a)
dep(_::EmptyFT) = 0
#dep(_::EmptyTree23) = 0
dep(ft::DeepFT) = ft.depth

box(b::Tree23) = b
box{T}(b::T) = Leaf23{T}(b)
unbox(b::Leaf23) = b.a
unbox(b) = b

fteltype(b) = typeof(b)
fteltype{T}(b::Tree23{T}) = T
fteltype{T}(b::FingerTree{T}) = T
fteltype{T}(b::DigitFT{T}) = T

# TODO: allow other counting functions
len(n::Leaf23) = 1
len{K}(n::NTuple{K, Leaf23}) = K
len{K}(n::NTuple{K, Node23}) = mapreduce(len, +, n)

len(n::Node23) = n.len
len(digit::DigitFT) = digit.len
len(_::EmptyFT) = 0
#len(_::EmptyTree23) = 0

len(deep::DeepFT) = deep.len
len(n::SingleFT) = len(n.a)
length(ft::FingerTree) = len(ft)

isempty(_::EmptyFT) = true
isempty(_::FingerTree) = false

width(digit::DigitFT) = length(digit.child)
width(n::Node23) = length(n.child)

#conj(a,b) = conjl(a,b)
function conjl(t) 
    ft = t[end]
    for i in length(t)-1:-1:1
        ft = conjl(t[i], ft)
    end
    ft
end
function conj(t) 
    ft = t[1]
    for x in t[2:end]
        ft = conj(ft, x)
    end
    ft
end
#function conj(ft, t...)
#    for x in t[1:end]
#        ft = conj(ft, x)
#    end
#    ft
#end
fttree2(T, ft::FingerTree) = ft
function fttree2(T, t)
    ft = EmptyFT{T}()
    for x in t
        ft = conj(ft, x)
    end
    ft
end

fttree(a) = SingleFT(a)
fttree(a,b) = DeepFT(a, b)
fttree(a,b,c) = DeepFT(DigitFT(a,b), DigitFT(c))
fttree(a,b,c,d) = DeepFT(DigitFT(a,b), DigitFT(c,d))
fttree(a,b,c,d,e) = DeepFT(DigitFT(a,b,c), DigitFT(d,e))
fttree(a,b,c,d,e,f) = DeepFT(DigitFT(a,b,c), DigitFT(d,e,f))
fttree(a,b,c,d,e,f,g) = DeepFT(DigitFT(a,b,c,d), DigitFT(e,f,g))
fttree(a,b,c,d,e,f,g,h) = DeepFT(DigitFT(a,b,c,d), DigitFT(e,f,g,h))


conjl{T}(a, digit::DigitFT0{T}) = DigitFT1{T}(box(a))
conjl{T}(a, digit::DigitFT1{T}) = DigitFT2{T}(box(a), digit.child...)
conjl{T}(a, digit::DigitFT2{T}) = DigitFT3{T}(box(a), digit.child...)
conjl{T}(a, digit::DigitFT3{T}) = DigitFT4{T}(box(a), digit.child...)
conj{T}(digit::DigitFT0{T}, a) =   DigitFT1{T}(box(a))
conj{T}(digit::DigitFT1{T}, a) =   DigitFT2{T}(digit.child..., box(a))
conj{T}(digit::DigitFT2{T}, a) =   DigitFT3{T}(digit.child..., box(a))
conj{T}(digit::DigitFT3{T}, a) =   DigitFT4{T}(digit.child..., box(a))


splitl{T}(digit::DigitFT1{T}) = digit.child[1], DigitFT0{T}()
splitl{T}(digit::DigitFT2{T}) = digit.child[1], DigitFT1{T}(digit.child[2:end]...)
splitl{T}(digit::DigitFT3{T}) = digit.child[1], DigitFT2{T}(digit.child[2:end]...)
splitl{T}(digit::DigitFT4{T}) = digit.child[1], DigitFT3{T}(digit.child[2:end]...)

splitr{T}(digit::DigitFT1{T}) = DigitFT0{T}(), digit.child[end]
splitr{T}(digit::DigitFT2{T}) = DigitFT1{T}(digit.child[1:end-1]...), digit.child[end]
splitr{T}(digit::DigitFT3{T}) = DigitFT2{T}(digit.child[1:end-1]...), digit.child[end]
splitr{T}(digit::DigitFT4{T}) = DigitFT3{T}(digit.child[1:end-1]...), digit.child[end]

Base.getindex(leaf::Leaf23, i) = i != 1 ? throw(BoundsError()) : leaf.a
function Base.getindex{T<:Union(Node23,DigitFT)}(n::T, i)
    for k in 1:width(n)
        j = len(n.child[k]) 
        if i <= j return getindex(n.child[k], i) end
        i -= j    
    end
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
    throw(BoundsError())
end
conjl{T}(a::T, ft::FingerTree{T}) = conjl(box(a), ft)
conj{T}(ft::FingerTree{T}, a::T) = conj(ft, box(a))

conjl{T}(a::Node23{T}, _::EmptyFT{T}) = SingleFT{T}(box(a))
conjl{T}(a::Leaf23{T}, _::EmptyFT{T}) = SingleFT{T}(a)
conj{T}(_::EmptyFT{T}, a::Node23{T}) = SingleFT{T}(box(a))
conj{T}(_::EmptyFT{T},a::Leaf23{T}) = SingleFT{T}(a)

conjl{T}(a::T, _::EmptyFT{T}) = SingleFT(box(a))
conj{T}( _::EmptyFT{T}, a::T) = SingleFT(box(a))

function splitl(_::EmptyFT)
    error("finger tree empty")
end
splitr(l::EmptyFT) = splitl(l)

conjl{T}(a::Tree23{T}, single::SingleFT{T}) = DeepFT(a, single.a)
conj{T}(single::SingleFT{T}, a::Tree23{T}) = DeepFT(single.a, a)

function splitl(single::SingleFT)
    unbox(single.a), EmptyFT{fteltype(single.a)}()
end
function splitr(single::SingleFT)
     EmptyFT{fteltype(single.a)}(), unbox(single.a)
end
function conjl{T}(a::Tree23{T}, ft::DeepFT{T})
    if width(ft.left) < 4
        DeepFT(conjl(a,ft.left), ft.succ, ft.right)
    else
        f = (Node23(ft.left.child[2:4]...))
        DeepFT(DigitFT(a, ft.left.child[1]), conjl(f,ft.succ), ft.right)
    end
end

function conj{T}(ft::DeepFT{T}, a::Tree23{T})
    if width(ft.right) < 4
        DeepFT(ft.left, ft.succ, conj(ft.right, a))
    else        
        f = Node23(ft.right.child[1:3]...)
        DeepFT(ft.left, conj(ft.succ, f), DigitFT(ft.right.child[4], a))
    end
end

function splitl(ft::DeepFT)
    a, as = splitl(ft.left)
    if width(as) > 0
        return unbox(a), DeepFT(as, ft.succ, ft.right)
    else
        if isempty(ft.succ) 
            b, bs = splitl(ft.right)
            if width(bs) > 0
                return unbox(a), DeepFT(DigitFT(b), ft.succ, bs)
            else
                return unbox(a), SingleFT(b)
            end
        else
            c, gt = splitl(ft.succ) 
            return unbox(a), DeepFT(DigitFT(c.child...), gt, ft.right)
        end
    end
end
function splitr(ft::DeepFT)
    as, a= splitr(ft.right)
    if width(as) > 0
        return DeepFT(ft.left, ft.succ, as), unbox(a)
    else
        if isempty(ft.succ) 
            bs, b = splitr(ft.left)
            if width(bs) > 0
                return DeepFT(bs, ft.succ, DigitFT(b)), unbox(a)
            else
                return SingleFT(b), unbox(a)
            end
        else
             gt, c = splitr(ft.succ)
             return DeepFT(ft.left, gt, DigitFT(c.child...)), unbox(a)
        end
    end
end

function split(ft::EmptyFT, i)
    error("can't split empty FingerTree")
end

function split(ft::SingleFT, i)
    if isa(ft.a, Node23) return split(ft.a, i) end
    
    e = EmptyFT{fteltype(ft)}() 
    return e, unbox(ft.a), e
end

function splitv(t, i)
    t[1:i-1], unbox(t[i]), t[i+1:end]
end

function split(n::Union(Node23,DigitFT), i)
    for k in 1:width(n)
        j = len(n.child[k]) 
        if i <= j 
            return splitv(n.child, k) end
        i -= j    
    end
    throw(BoundsError())
end


function flat(xs)
     v = Array(fteltype(xs), len(xs))
     traverse((x, i) -> (v[i] = x;), xs)
     v
end

rotr(d, ft::EmptyFT) = fttree(d.child...)
function rotr(d, ft)
    ft, x = splitr(ft)
    y = isa(x, Node23) ? x.child : (box(x),)
    if isa(ft, SingleFT) && isa(ft.a, Leaf23) return fttree(d.child..., ft.a, y...) end
    DeepFT(DigitFT(d.child...), ft, DigitFT(y...))
end
rotl(ft::EmptyFT, d) = fttree(d.child...)
function rotl(ft,d)
    x, ft = splitl(ft)
    y = isa(x, Node23) ? x.child :(box(x),) 
    if isa(ft, SingleFT) && isa(ft.a, Leaf23) return fttree(y..., ft.a, d.child...) end
    DeepFT(DigitFT(y...), ft, DigitFT(d.child...))
end

 
deepl(t::(), ft, d) = rotl(ft, d) 
deepl(t, ft, d) = DeepFT(DigitFT(t...), ft, d)

deepr(d, ft, t::()) = rotr(d, ft) 
deepr(d, ft, t) = DeepFT(d, ft, DigitFT(t...))

function split{T}(ft::DeepFT{T}, i)
    j = len(ft.left)
    if i <= j
        l, x, r = split(ft.left, i) 
        return fttree2(T, l), x, deepl(r, ft.succ, ft.right)
    end
    i -= j; j = len(ft.succ)
    if i <= j 
        ml, xs, mr = split(ft.succ, i)    
        i -= len(ml)
        l, x, r =  isa(xs,Tree23) ? split(xs, i) : ((),xs,())
        ml = fttree2(T, ml)
        mr = fttree2(T, mr)
        return deepr(ft.left, ml, l), x, deepl(r, mr, ft.right)
    end
    i -= j; j = len(ft.right)
    if i <= j 
        l, x, r = split(ft.right, i) 
        return deepr(ft.left, ft.succ, l), x, fttree2(T, r)
    end
    throw(BoundsError())
end


Base.reduce(op::Function, v, l::Leaf23) = op(v, l.a)
Base.reduce(op::Function, v, ::EmptyFT) = v
Base.reduce(op::Function, v, t::SingleFT) = reduce(op, v, ft.a)
function Base.reduce{T<:Union(DigitFT, Node23)}(op::Function, v, n::T)
    for k in 1:width(n)
        v = reduce(op, v, n.child[k])
    end
    v
end
function Base.reduce(op::Function, v, ft::DeepFT)
    v = reduce(op, v, ft.left)
    v = reduce(op, v, ft.succ)
    v = reduce(op, v, ft.right)
end

traverse(op::Function, l::Leaf23, i) = (op(l.a, i); i + 1)
traverse(op::Function,  ::EmptyFT, i) = return i
traverse(op::Function, ft::SingleFT, i) = traverse(op, ft.a, i)

function traverse{T<:Union(DigitFT, Node23)}(op::Function, n::T, i)
    for k in 1:width(n)
        i = traverse(op, n.child[k], i)
    end
    i
end
function traverse(op::Function, ft::DeepFT, i)
    i = traverse(op, ft.left, i)
    i = traverse(op, ft.succ, i)
    traverse(op, ft.right, i)
end
traverse(op, ft) = (traverse(op, ft, 1);)

travstruct(op::Function, l::Leaf23, d) = (op(l.a, d);d)
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


checkinteg(l::Leaf23, d) = (d == 0)
checkinteg( ::EmptyFT, d) = return true
checkinteg( ft::SingleFT, d) = checkinteg(ft.a, d-1)
function checkinteg{T<:Union(DigitFT, Node23)}(n::T, d)
    r = true
    for k in 1:width(n)
        r = r && checkinteg(n.child[k], d-1)
    end
    r
end
function checkinteg(ft::DeepFT, d)
    checkinteg(ft.left, d) && checkinteg(ft.succ, d + 1) && checkinteg(ft.right, d)
end
checkinteg(ft) = checkinteg(ft, 1)
function chk(ft) 
 !checkinteg(ft) && (dump(ft); error("Malformed finger tree"))
 ft
end

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
 
 
app3(l::SingleFT, ts, r::SingleFT) = fttree(l.a, ts..., r.a)
app3(::EmptyFT, ts, r::EmptyFT) = fttree(ts...)
app3(::EmptyFT, ts, r::SingleFT) = fttree(ts..., r.a)
app3(l::SingleFT, ts, ::EmptyFT) = fttree(l.a, ts...)
app3(::EmptyFT, ts, r) = conjl(tuple(ts..., r))
app3(l, ts, ::EmptyFT) = conj(l, ts...)
app3(x::SingleFT, ts, r) = conjl(x.a, conjl(tuple(ts..., r)))
app3(l, ts, x::SingleFT) = conj(conj(tuple(l, ts...)), x.a)


nodes(a,b) = (Node23(a, b),)
nodes(a,b,c) = (Node23(a,b,c),)
nodes(a,b,c,d) = (Node23(a, b), Node23(c,d))
nodes(a,b,c,xs...) = tuple(Node23(a,b,c), nodes(xs...)...)

app3(l::DeepFT, ts, r::DeepFT) = 
    DeepFT(l.left, app3(l.succ, nodes(l.right.child..., ts..., r.left.child...),r.succ),  r.right)
concat(l::FingerTree, r::FingerTree) = app3(l, (), r)
concat(l::FingerTree,x, r::FingerTree) = app3(l, (box(x),), r)


Base.show(io::IO, l::Leaf23) = print(io, "'", l.a)
Base.show(io::IO, d::DigitFT) = print(io, d.child...)
Base.show(io::IO, n::Node23) = len(n) < 20 ? print(io, "^", n.child..., "") : print(" ... ")
Base.show(io::IO, d::DeepFT) = print(io, "(", d.left, " .. ", d.succ, " .. ", d.right, ")")
Base.show(io::IO, d::SingleFT) = print(io, "(", d.a, ")")
Base.show(io::IO, d::EmptyFT) = print(io, "(/)")


end
