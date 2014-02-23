module FT
import Base.reduce
export reduce
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

len(n::Leaf23) = 1
len(n::Node23) = n.len
len(digit::DigitFT) = digit.len
len(_::EmptyFT) = 0
len(deep::DeepFT) = deep.len
len(n::SingleFT) = len(n.a)

isempty(_::EmptyFT) = true
isempty(_::FingerTree) = false

width(digit::DigitFT) = length(digit.child)
width(n::Node23) = length(n.child)

function consl(digit::DigitFT, a)
    assert(width(digit) < 4)
    DigitFT(box(a), digit.child...)
end
function consr(digit::DigitFT, a)
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

#consl(ft::FingerTree, a::Leaf23) = consl(ft, unbox(a))
#consr(ft::FingerTree, a::Leaf23) = consr(ft, unbox(a))

function consl(_::EmptyFT, a)
    SingleFT{fteltype(a)}(box(a))
end
consr(l::EmptyFT, a) = consl(l, a)
function splitl(_::EmptyFT)
    error("finger tree empty")
end
splitr(l::EmptyFT) = splitl(l)

function consl(single::SingleFT, a)
    DeepFT(box(a), EmptyFT{fteltype(a)}(), single.a)
end
function consr(single::SingleFT, a)
    DeepFT(single.a, EmptyFT{fteltype(a)}(), box(a))
end

function splitl(single::SingleFT)
    unbox(single.a), EmptyFT{fteltype(single.a)}()
end
function splitr(single::SingleFT)
    unbox(single.a), EmptyFT{fteltype(single.a)}()
end

function consl(ft::DeepFT, a)
    if width(ft.left) < 4
        DeepFT(consl(ft.left, box(a)), ft.succ, ft.right)
    else
        f = (Node23(ft.left.child[2:4]...))
        DeepFT(DigitFT(box(a), ft.left.child[1]), consl(ft.succ,f), ft.right)
    end
end
function consr(ft::DeepFT, a)
    if width(ft.right) < 4
        DeepFT(ft.left, ft.succ, consr(ft.right, box(a)))
    else        
        f = Node23(ft.right.child[1:3]...)
        DeepFT(ft.left, consr(ft.succ, f), DigitFT(ft.right.child[4], box(a)))
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

#for (fname, cons) in ((:appendr, :consr), (:appendl, :consl)) @eval begin
#shoud appenl work for iterators?
for (fname, cons) in ((:appendr, :consr),) @eval begin
    function ($fname)(ft, iter)
        state = start(iter)
        while true
            if done(iter, state)
                break
            end
            k, state = next(iter, state)
            ft = ($cons)(ft, k)
        end
        ft
    end
end end

function appendl(ft, t::Tuple) 
    for i in length(t):-1:1
        ft = consl(ft, t[i])
    end
    ft
end
function appendr(ft, t::Tuple)
    for x in t
        ft = consr(ft, x)
    end
    ft
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
traverse(op::Function, t::SingleFT) = traverse(op, ft.a)
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

# Example
# trav = () -> FT.traverse(produce, FT.randomft(100))
# t = Task(trav)
# while !(t.state==:done) print(consume(t)); end

    app3(l::SingleFT, ts, r::SingleFT) = consl(appendl(r, ts), l.a)
    app3(::EmptyFT, ts, r::EmptyFT) = appendl(r, ts)
    app3(::EmptyFT, ts, r::SingleFT) = appendl(r, ts)
    app3(l::SingleFT, ts, ::EmptyFT) = appendr(l, ts)
app3(::EmptyFT, ts, r) = appendl(r, ts)
app3(l, ts, ::EmptyFT) = appendr(l, ts)
app3(x::SingleFT, ts, r) = consl(appendl(r, ts), x.a)
app3(l, ts, x::SingleFT) = consr(appendr(l, ts), x.a)


nodes(a,b) = (Node23(a, b),)
nodes(a,b,c) = (Node23(a,b,c),)
nodes(a,b,c,d) = (Node23(a, b), Node23(c,d))
nodes(a,b,c,xs...) = tuple(Node23(a,b,c), nodes(xs...)...)

app3(l::DeepFT, ts, r::DeepFT) = 
    DeepFT(l.left, app3(l.succ, nodes(l.right.child..., ts..., r.left.child...),r.succ),  r.right)
concat(l::FingerTree, r::FingerTree) = app3(l, (), r)


Base.show(io::IO, l::Leaf23) = print(io, "'", l.a)
Base.show(io::IO, d::DigitFT) = print(io, d.child)
Base.show(io::IO, n::Node23) = print(io, ".(", n.child, ").")
#if isdefined(:FTPRETTY)
    Base.show(io::IO, d::DeepFT) = print(io, "(", d.left, " V ", d.succ, " V ", d.right, ")")
    Base.show(io::IO, d::SingleFT) = print(io, "(", d.a, ")")
    Base.show(io::IO, d::EmptyFT) = print(io, "(/)")
#end 
ft = FT.EmptyFT()
E = 'F'
if false
for i in 'A':E
    ft = FT.consr(ft,i)
    println(ft)
end
for i in 'A':E
        k , ft = FT.splitl(ft)
        println(k, "\t", ft)
end
end

export torture, randomft
function randomft(N, start = 1, verb = false)
    ft = FT.EmptyFT()
    b = randbool(N)
    l = sum(b) + start - 1
    u = l+1
    i = 1
    for i in 1:N
        if b[i] 
            ft = FT.consl(ft,l)
            l -= 1
        else 
            ft = FT.consr(ft,u)
            u += 1
        end
        verb &&     println(ft)

    end
    ft
end

function torture(N, verb=false)
    ft = randomft(N, 1, verb)
        
    for i in 1:N
        assert(ft[i] == i)
    end
    
    b = randbool(N)
    l = 1
    u = N
    for i in 1:N
        if b[i]
            k, ft = FT.splitl(ft)
            assert(k == l)
            l += 1
        else
            k, ft = FT.splitr(ft)
            assert(k == u)
            u -= 1
        end        
verb &&     println(k, " ",i, ft)
    end
    
end




end
