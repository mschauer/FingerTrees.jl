module FT
import Base.reduce
export reduce
import Base.start, Base.next, Base.done
export start, next, done, concat
import Base.length
export length

abstract FingerTree{T}
abstract Tree23{T}

immutable Leaf23{T} <: Tree23{T}
    a::T
end
immutable Node23{T} <: Tree23{T}
    child::NTuple{Any, Tree23{T}}
    len::Int
    Node23(a, b) = new((a,b), len(a)+len(b))
    Node23(a, b, c) = new((a,b,c), len(a)+len(b)+len(c))
end
Node23{T}(a::Tree23{T}...) = Node23{T}(a...)

immutable DigitFT{T}
    child::NTuple{Any, Tree23}
    len::Int
    DigitFT(b...) = new(b, mapreduce(len,+,b))
end

DigitFT{T}(b::T...) = DigitFT{T}(map(prom,b)...)
DigitFT{T}(b::Tree23{T}...) = DigitFT{T}(b...)

immutable EmptyFT{T} <: FingerTree{T} end
EmptyFT() = EmptyFT{Any}()

immutable SingleFT{T} <: FingerTree{T} 
    a::Tree23{T}
end
SingleFT{T}(a::Tree23{T}) = SingleFT{T}(a)

immutable DeepFT{T} <: FingerTree{T}
    left::DigitFT{T}
    succ::FingerTree{T}
    right::DigitFT{T}
    len::Int
    DeepFT(l, s, r) = new(l, s, r, len(l) + len(s) + len(r))
end
DeepFT{T}(l::DigitFT{T}, s, r::DigitFT{T}) = DeepFT{T}(l, s, r)
DeepFT{T}(l::Tree23{T}, s, r::Tree23{T}) = DeepFT{T}(DigitFT{T}(l), s, DigitFT{T}(r))
DeepFT{T}(l::DigitFT{T}, _::EmptyFT, r::DigitFT{T}) = DeepFT{T}(l, EmptyFT{T}(), r)
DeepFT{T}(l::Tree23{T}, _::EmptyFT, r::Tree23{T}) = DeepFT{T}(DigitFT{T}(l), EmptyFT{T}(), DigitFT{T}(r))


box(b) = Leaf23(b)
box(b::Tree23) = b
unbox(b::Leaf23) = b.a
unbox(b) = b

fteltype(b) = typeof(b)
fteltype{T}(b::Tree23{T}) = T

# TODO: allow other counting functions
len(n::Leaf23) = 1
len(n::Node23) = n.len
len(digit::DigitFT) = digit.len
len(_::EmptyFT) = 0
len(deep::DeepFT) = deep.len
len(n::SingleFT) = len(n.a)
length(ft::FingerTree) = len(ft)

isempty(_::EmptyFT) = true
isempty(_::FingerTree) = false

width(digit::DigitFT) = length(digit.child)
width(n::Node23) = length(n.child)

conj(a,b) = conjl(a,b)
function conjl(t) 
    ft = t[end]
    for i in length(t)-1:-1:1
        ft = conj(t[i], ft)
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

function conjl(a, digit::DigitFT)
    assert(width(digit) < 4)
    DigitFT(box(a), digit.child...)
end
function conj(digit::DigitFT, a)
    assert(width(digit) < 4)
    DigitFT(digit.child..., box(a))
end
function splitl{T}(digit::DigitFT{T})
    assert(width(digit) > 0)
    digit.child[1], DigitFT{T}(digit.child[2:end]...)
end
function splitr{T}(digit::DigitFT{T})
    assert(width(digit) > 0)
    digit.child[end], DigitFT{T}(digit.child[1:end-1]...)
end

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
#Base.endof(ft::FingerTree) = len(ft)
#Base.first(ft::FingerTree) = ft[1]
#Base.last(ft::FingerTree) = ft[endof(ft)]

#conjl(a::Leaf23, ft::FingerTree) = conj(unbox(a), ft)
#conj(ft::FingerTree, a::Leaf23) = conj(ft, unbox(a))

function conjl(a, _::EmptyFT)
    SingleFT{fteltype(a)}(box(a))
end
conj(l::EmptyFT, a) = conjl(a, l)
function splitl(_::EmptyFT)
    error("finger tree empty")
end
splitr(l::EmptyFT) = splitl(l)

function conjl{T}(a::Tree23{T}, single::SingleFT{T})
    DeepFT(a, EmptyFT{fteltype(a)}(), single.a)
end
conjl{T}(a::T, single::SingleFT{T}) = conj(box(a), single)

function conj{T}(single::SingleFT{T}, a::Tree23{T})
    DeepFT(single.a, EmptyFT{fteltype(a)}(), a)
end
conj{T}(single::SingleFT{T}, a::T) = conj(single, box(a))

function splitl(single::SingleFT)
    unbox(single.a), EmptyFT{fteltype(single.a)}()
end
function splitr(single::SingleFT)
    unbox(single.a), EmptyFT{fteltype(single.a)}()
end
conjl{T}(a::T, ft::DeepFT{T}) = conjl(box(a), ft)
function conjl{T}(a::Tree23{T}, ft::DeepFT{T})
    if width(ft.left) < 4
        DeepFT(conj(a,ft.left), ft.succ, ft.right)
    else
        f = (Node23(ft.left.child[2:4]...))
        DeepFT(DigitFT(a, ft.left.child[1]), conj(f,ft.succ), ft.right)
    end
end

conj{T}(ft::DeepFT{T}, a::T) = conj(ft, box(a))
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
    a, as = splitr(ft.right)
    if width(as) > 0
        return unbox(a), DeepFT(ft.left, ft.succ, as)
    else
        if isempty(ft.succ) 
            b, bs = splitr(ft.left)
            if width(bs) > 0
                return unbox(a), DeepFT(bs, ft.succ, DigitFT(b))
            else
                return unbox(a), SingleFT(b)
            end
        else
             c, gt = splitr(ft.succ)
             return unbox(a), DeepFT(ft.left, gt, DigitFT(c.child...))
        end
    end
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

traverse(op::Function, l::Leaf23) = op(l.a)
traverse(op::Function,  ::EmptyFT) = return
traverse(op::Function, ft::SingleFT) = traverse(op, ft.a)
function traverse{T<:Union(DigitFT, Node23)}(op::Function,n::T)
    for k in 1:width(n)
        traverse(op, n.child[k])
    end
end
function traverse(op::Function, ft::DeepFT)
    traverse(op, ft.left)
    traverse(op, ft.succ)
    traverse(op, ft.right)
end

# Scheme:
# state = start(I)
# while !done(I, state)
#   (i, state) = next(I, state)
#     # body
# end
# rather slow
function start(ft::FingerTree)
    trav = () -> FT.traverse(produce, ft)
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
 
 
    app3(l::SingleFT, ts, r::SingleFT) = conj(l.a, conjl(tuple(ts..., r)))
    app3(::EmptyFT, ts, r::EmptyFT) = conjl(tuple(ts..., r))
    app3(::EmptyFT, ts, r::SingleFT) = conjl(tuple(ts..., r))
    app3(l::SingleFT, ts, ::EmptyFT) = conj(tuple(l, ts...))
app3(::EmptyFT, ts, r) = conjl(tuple(ts..., r))
app3(l, ts, ::EmptyFT) = conj(tuple(l, ts...))
app3(x::SingleFT, ts, r) = conj(x.a, conjl(tuple(ts..., r)))
app3(l, ts, x::SingleFT) = conj(conj(tuple(l, ts...)), x.a)


nodes(a,b) = (Node23(a, b),)
nodes(a,b,c) = (Node23(a,b,c),)
nodes(a,b,c,d) = (Node23(a, b), Node23(c,d))
nodes(a,b,c,xs...) = tuple(Node23(a,b,c), nodes(xs...)...)

app3(l::DeepFT, ts, r::DeepFT) = 
    DeepFT(l.left, app3(l.succ, nodes(l.right.child..., ts..., r.left.child...),r.succ),  r.right)
concat(l::FingerTree, r::FingerTree) = app3(l, (), r)

Base.show(io::IO, l::Leaf23) = print(io, "'", l.a)
Base.show(io::IO, d::DigitFT) = print(io, d.child...)
Base.show(io::IO, n::Node23) = print(io, "^", n.child..., "")
Base.show(io::IO, d::DeepFT) = print(io, "(", d.left, " .. ", d.succ, " .. ", d.right, ")")
Base.show(io::IO, d::SingleFT) = print(io, "(", d.a, ")")
Base.show(io::IO, d::EmptyFT) = print(io, "(/)")

end
