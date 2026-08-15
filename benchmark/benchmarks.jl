using BenchmarkTools
using DataStructures
using FingerTrees
using FunctionalCollections
using InteractiveUtils
using Printf
using Statistics

const FT = FingerTrees
const FC = FunctionalCollections
const DS = DataStructures

# ---------------------------------------------------------------------------
# Constructors and small helpers
# ---------------------------------------------------------------------------

function ft_build_right(n)
    x = FT.EmptyFT{Int}()
    for i in 1:n
        x = FT.conjr(x, i)
    end
    return x
end

function ft_build_left(n)
    x = FT.EmptyFT{Int}()
    for i in 1:n
        x = FT.conjl(i, x)
    end
    return x
end

function pv_build_right(n)
    x = FC.PersistentVector{Int}()
    for i in 1:n
        x = FC.push(x, i)
    end
    return x
end

function deque_build_right(n)
    x = DS.Deque{Int}()
    for i in 1:n
        push!(x, i)
    end
    return x
end

function deque_build_left(n)
    x = DS.Deque{Int}()
    for i in 1:n
        pushfirst!(x, i)
    end
    return x
end

function vector_build_right(n)
    x = Int[]
    sizehint!(x, n)
    for i in 1:n
        push!(x, i)
    end
    return x
end

function vector_build_left(n)
    x = Int[]
    sizehint!(x, n)
    for i in 1:n
        pushfirst!(x, i)
    end
    return x
end

function vector_assoc(x, k, value)
    y = copy(x)
    y[k] = value
    return y
end

function checksum(x)
    s = 0
    for y in x
        s += y
    end
    return s
end

# ---------------------------------------------------------------------------
# Benchmark suite
#
# Values used by single-operation benchmarks are put behind Ref.  This keeps
# the benchmark inputs runtime values and avoids constant folding / hoisting
# of operations such as indexing and traversal.
#
# Mutable benchmarks use setup + evals=1 so every timed operation sees a fresh
# container and mutations do not accumulate across evaluations.
# ---------------------------------------------------------------------------

const SUITE = BenchmarkGroup()

for n in (32, 1024, 32768)
    g = SUITE["n=$n"] = BenchmarkGroup()

    ft = FT.FingerTree(1:n)
    pv = FC.PersistentVector(1:n)
    deq = deque_build_right(n)
    vec = collect(1:n)

    k = n ÷ 2

    ftref = Ref(ft)
    pvref = Ref(pv)
    deqref = Ref(deq)
    vecref = Ref(vec)
    kref = Ref(k)

    # Construction ----------------------------------------------------------

    g["build", "ft-right"] =
        @benchmarkable ft_build_right($n)

    g["build", "ft-left"] =
        @benchmarkable ft_build_left($n)

    g["build", "pv-right"] =
        @benchmarkable pv_build_right($n)

    g["build", "deque-right"] =
        @benchmarkable deque_build_right($n)

    g["build", "deque-left"] =
        @benchmarkable deque_build_left($n)

    g["build", "vector-right"] =
        @benchmarkable vector_build_right($n)

    g["build", "vector-left"] =
        @benchmarkable vector_build_left($n)

    # Single end operations -------------------------------------------------

    g["push-right", "ft"] =
        @benchmarkable FT.conjr($(ftref)[], 0)

    g["push-left", "ft"] =
        @benchmarkable FT.conjl(0, $(ftref)[])

    g["pop-right", "ft"] =
        @benchmarkable FT.splitr($(ftref)[])

    g["pop-left", "ft"] =
        @benchmarkable FT.splitl($(ftref)[])

    g["push-right", "pv"] =
        @benchmarkable FC.push($(pvref)[], 0)

    g["pop-right", "pv"] =
        @benchmarkable FC.pop($(pvref)[])

    # The mutable structures need a fresh value for every timed mutation.
    g["push-right", "deque"] =
        @benchmarkable push!(dref[], 0) setup=(dref = Ref(deque_build_right($n))) evals=1

    g["push-left", "deque"] =
        @benchmarkable pushfirst!(dref[], 0) setup=(dref = Ref(deque_build_right($n))) evals=1

    g["pop-right", "deque"] =
        @benchmarkable pop!(dref[]) setup=(dref = Ref(deque_build_right($n))) evals=1

    g["pop-left", "deque"] =
        @benchmarkable popfirst!(dref[]) setup=(dref = Ref(deque_build_right($n))) evals=1

    # Give Vector one spare slot for push benchmarks so that we measure the
    # operation itself rather than forcing a reallocation on every sample.
    g["push-right", "vector"] =
        @benchmarkable push!(vref[], 0) setup=(
            v = copy($(vecref)[]);
            sizehint!(v, $n + 1);
            vref = Ref(v)
        ) evals=1

    g["push-left", "vector"] =
        @benchmarkable pushfirst!(vref[], 0) setup=(
            v = copy($(vecref)[]);
            sizehint!(v, $n + 1);
            vref = Ref(v)
        ) evals=1

    g["pop-right", "vector"] =
        @benchmarkable pop!(vref[]) setup=(vref = Ref(copy($(vecref)[]))) evals=1

    g["pop-left", "vector"] =
        @benchmarkable popfirst!(vref[]) setup=(vref = Ref(copy($(vecref)[]))) evals=1

    # Indexing --------------------------------------------------------------

    g["index", "ft"] =
        @benchmarkable $(ftref)[][$(kref)[]]

    g["index", "pv"] =
        @benchmarkable $(pvref)[][$(kref)[]]

    g["index", "vector"] =
        @benchmarkable $(vecref)[][$(kref)[]]

    # Persistent / copy-on-update ------------------------------------------

    g["assoc", "ft"] =
        @benchmarkable FT.assoc($(ftref)[], 0, $(kref)[])

    g["assoc", "pv"] =
        @benchmarkable FC.assoc($(pvref)[], $(kref)[], 0)

    g["assoc", "vector-copy"] =
        @benchmarkable vector_assoc($(vecref)[], $(kref)[], 0)

    # Traversal -------------------------------------------------------------

    g["iterate", "ft"] =
        @benchmarkable checksum($(ftref)[])

    g["iterate", "pv"] =
        @benchmarkable checksum($(pvref)[])

    g["iterate", "deque"] =
        @benchmarkable checksum($(deqref)[])

    g["iterate", "vector"] =
        @benchmarkable checksum($(vecref)[])

    # Split -----------------------------------------------------------------

    g["split-middle", "ft"] =
        @benchmarkable FT.split($(ftref)[], $(kref)[])

    g["split-middle", "vector"] =
        @benchmarkable begin
            v = $(vecref)[]
            j = $(kref)[]
            (v[1:j-1], v[j], v[j+1:end])
        end

    # Concatenation ---------------------------------------------------------

    ft1 = FT.FingerTree(1:k)
    ft2 = FT.FingerTree(k+1:n)

    pv1 = FC.PersistentVector(1:k)
    pv2 = FC.PersistentVector(k+1:n)

    v1 = collect(1:k)
    v2 = collect(k+1:n)

    ft1ref = Ref(ft1)
    ft2ref = Ref(ft2)
    pv1ref = Ref(pv1)
    pv2ref = Ref(pv2)
    v1ref = Ref(v1)
    v2ref = Ref(v2)

    g["concat", "ft"] =
        @benchmarkable FT.concat($(ft1ref)[], $(ft2ref)[])

    g["concat", "pv"] =
        @benchmarkable FC.append($(pv1ref)[], $(pv2ref)[])

    g["concat", "vector"] =
        @benchmarkable vcat($(v1ref)[], $(v2ref)[])
end

# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

function n_from_key(key)
    return parse(Int, split(key, "=")[2])
end

function print_results(io, results)
    println(io,
        "n\toperation\timplementation\tmedian_ns\tminimum_ns\tmemory_bytes\tallocations"
    )

    nkeys = sort(collect(keys(results)); by=n_from_key)

    for nkey in nkeys
        n = n_from_key(nkey)
        group = results[nkey]

        entries = sort(collect(group); by=x -> string(first(x)))

        for entry in entries
            key = first(entry)
            trial = last(entry)
            operation, implementation = key

            med = median(trial)
            minest = minimum(trial)

            @printf(
                io,
                "%d\t%s\t%s\t%.3f\t%.3f\t%d\t%d\n",
                n,
                operation,
                implementation,
                med.time,
                minest.time,
                med.memory,
                med.allocs,
            )
        end
    end
end

function write_versioninfo(path)
    open(path, "w") do io
        versioninfo(io)
    end
end

println("Running benchmark suite...")
results = run(SUITE; verbose=true)

println()
print_results(stdout, results)

results_dir = joinpath(@__DIR__, "results")
mkpath(results_dir)

version_tag = "julia-" * string(VERSION)

tsv_path = joinpath(results_dir, "baseline-" * version_tag * ".tsv")
open(tsv_path, "w") do io
    print_results(io, results)
end

version_path = joinpath(results_dir, "versioninfo-" * version_tag * ".txt")
write_versioninfo(version_path)

println()
println("Saved:")
println("  ", tsv_path)
println("  ", version_path)
