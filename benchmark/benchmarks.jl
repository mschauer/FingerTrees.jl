using BenchmarkTools
using FingerTrees
using FunctionalCollections
using DataStructures

const FT = FingerTrees
const FC = FunctionalCollections
const DS = DataStructures

function ft_build_right(n)
    x = FT.EmptyFT{Int}()
    for i in 1:n
        x = FT.conjr(x, i)
    end
    x
end

function ft_build_left(n)
    x = FT.EmptyFT{Int}()
    for i in 1:n
        x = FT.conjl(i, x)
    end
    x
end

function pv_build_right(n)
    x = FC.PersistentVector{Int}()
    for i in 1:n
        x = FC.push(x, i)
    end
    x
end

function deque_build_right(n)
    x = DS.Deque{Int}()
    for i in 1:n
        push!(x, i)
    end
    x
end

function deque_build_left(n)
    x = DS.Deque{Int}()
    for i in 1:n
        pushfirst!(x, i)
    end
    x
end

function vector_build_right(n)
    x = Int[]
    sizehint!(x, n)
    for i in 1:n
        push!(x, i)
    end
    x
end

function vector_build_left(n)
    x = Int[]
    sizehint!(x, n)
    for i in 1:n
        pushfirst!(x, i)
    end
    x
end

function checksum(x)
    s = 0
    for y in x
        s += y
    end
    s
end

function make_deque(n)
    d = DS.Deque{Int}()
    for i in 1:n
        push!(d, i)
    end
    d
end

const SUITE = BenchmarkGroup()

for n in (32, 1024, 32768)
    g = SUITE["n=$n"] = BenchmarkGroup()

    ft  = FingerTree(1:n)
    pv  = FC.PersistentVector(1:n)
    vec = collect(1:n)

    # Construction
    g["build", "ft-right"]    = @benchmarkable ft_build_right($n)
    g["build", "ft-left"]     = @benchmarkable ft_build_left($n)
    g["build", "pv-right"]    = @benchmarkable pv_build_right($n)
    g["build", "deque-right"] = @benchmarkable deque_build_right($n)
    g["build", "deque-left"]  = @benchmarkable deque_build_left($n)
    g["build", "vector-right"] = @benchmarkable vector_build_right($n)
    g["build", "vector-left"]  = @benchmarkable vector_build_left($n)

    # Single persistent end operations
    g["push-right", "ft"] = @benchmarkable FT.conjr($ft, 0)
    g["push-right", "pv"] = @benchmarkable FC.push($pv, 0)

    g["push-left", "ft"] = @benchmarkable FT.conjl(0, $ft)

    g["pop-right", "ft"] = @benchmarkable FT.splitr($ft)
    g["pop-right", "pv"] = @benchmarkable FC.pop($pv)

    g["pop-left", "ft"] = @benchmarkable FT.splitl($ft)

    # Mutable lower bounds. Setup is outside the timed operation.
    g["push-right", "deque"] =
        @benchmarkable push!(d, 0) setup=(d = make_deque($n)) evals=1

    g["push-left", "deque"] =
        @benchmarkable pushfirst!(d, 0) setup=(d = make_deque($n)) evals=1

    g["pop-right", "deque"] =
        @benchmarkable pop!(d) setup=(d = make_deque($n)) evals=1

    g["pop-left", "deque"] =
        @benchmarkable popfirst!(d) setup=(d = make_deque($n)) evals=1

    g["push-right", "vector"] =
        @benchmarkable push!(v, 0) setup=(v = copy($vec)) evals=1

    g["push-left", "vector"] =
        @benchmarkable pushfirst!(v, 0) setup=(v = copy($vec)) evals=1

    g["pop-right", "vector"] =
        @benchmarkable pop!(v) setup=(v = copy($vec)) evals=1

    g["pop-left", "vector"] =
        @benchmarkable popfirst!(v) setup=(v = copy($vec)) evals=1

    # Indexing
    k = n ÷ 2

    g["index", "ft"]     = @benchmarkable $ft[$k]
    g["index", "pv"]     = @benchmarkable $pv[$k]
    g["index", "vector"] = @benchmarkable $vec[$k]

    # Persistent update
    g["assoc", "ft"] = @benchmarkable FT.assoc($ft, 0, $k)
    g["assoc", "pv"] = @benchmarkable FC.assoc($pv, $k, 0)

    # Traversal
    g["iterate", "ft"]     = @benchmarkable checksum($ft)
    g["iterate", "pv"]     = @benchmarkable checksum($pv)
    g["iterate", "vector"] = @benchmarkable checksum($vec)

    # Operations for which finger trees should be algorithmically attractive
    g["split-middle", "ft"] =
        @benchmarkable FT.split($ft, $k)

    g["split-middle", "vector"] =
        @benchmarkable ($vec[1:$k-1], $vec[$k], $vec[$k+1:end])

    ft1 = FingerTree(1:k)
    ft2 = FingerTree(k+1:n)

    pv1 = FC.PersistentVector(1:k)
    pv2 = FC.PersistentVector(k+1:n)

    v1 = collect(1:k)
    v2 = collect(k+1:n)

    g["concat", "ft"] =
        @benchmarkable FT.concat($ft1, $ft2)

    g["concat", "pv"] =
        @benchmarkable FC.append($pv1, $pv2)

    g["concat", "vector"] =
        @benchmarkable vcat($v1, $v2)
end

results = run(SUITE; verbose=true)

println(results)