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

Base.@noinline function ft_build_right(n)
    x = FT.EmptyFT{Int}()
    for i in 1:n
        x = FT.conjr(x, i)
    end
    return x
end

Base.@noinline function ft_build_left(n)
    x = FT.EmptyFT{Int}()
    for i in 1:n
        x = FT.conjl(i, x)
    end
    return x
end

Base.@noinline function pv_build_right(n)
    x = FC.PersistentVector{Int}()
    for i in 1:n
        x = FC.push(x, i)
    end
    return x
end

Base.@noinline function deque_build_right(n)
    x = DS.Deque{Int}()
    for i in 1:n
        push!(x, i)
    end
    return x
end

Base.@noinline function deque_build_left(n)
    x = DS.Deque{Int}()
    for i in 1:n
        pushfirst!(x, i)
    end
    return x
end

Base.@noinline function vector_build_right(n)
    x = Int[]
    sizehint!(x, n)
    for i in 1:n
        push!(x, i)
    end
    return x
end

Base.@noinline function vector_build_left(n)
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
# Runtime-dependent microbenchmark batches
# ---------------------------------------------------------------------------

function probe_indices(n, count)
    return [mod(17 * i + 13, n) + 1 for i in 1:count]
end

micro_batch_size(n) = min(256, max(16, n ÷ 4))
index_batch_size(n) = max(256, micro_batch_size(n))

Base.@noinline function bench_index(x, indices)
    s = 0
    for i in indices
        s += x[i]
    end
    return s
end

Base.@noinline function bench_assoc_ft(x, indices, values)
    y = x
    for q in eachindex(indices, values)
        y = FT.assoc(y, values[q], indices[q])
    end
    return y
end

Base.@noinline bench_multiassoc_ft(x, indices, values) =
    FT.multiassoc(x, indices, values; presorted=true)

Base.@noinline function bench_assoc_pv(x, indices, values)
    y = x
    for q in eachindex(indices, values)
        y = FC.assoc(y, indices[q], values[q])
    end
    return y
end

Base.@noinline function bench_assoc_vector(x, indices, values)
    y = x
    for q in eachindex(indices, values)
        y = vector_assoc(y, indices[q], values[q])
    end
    return y
end

Base.@noinline function bench_push_right_ft(x, values)
    y = x
    for value in values
        y = FT.conjr(y, value)
    end
    return y
end

Base.@noinline function bench_push_left_ft(x, values)
    y = x
    for value in values
        y = FT.conjl(value, y)
    end
    return y
end

Base.@noinline function bench_push_right_pv(x, values)
    y = x
    for value in values
        y = FC.push(y, value)
    end
    return y
end

Base.@noinline function bench_push_right_mutable!(x, values)
    for value in values
        push!(x, value)
    end
    return x
end

Base.@noinline function bench_push_left_mutable!(x, values)
    for value in values
        pushfirst!(x, value)
    end
    return x
end

Base.@noinline function bench_pop_right_ft(x, count)
    y = x
    s = 0
    for _ in 1:count
        y, value = FT.splitr(y)
        s += value
    end
    return y, s
end

Base.@noinline function bench_pop_left_ft(x, count)
    y = x
    s = 0
    for _ in 1:count
        value, y = FT.splitl(y)
        s += value
    end
    return y, s
end

Base.@noinline function bench_pop_right_pv(x, count)
    y = x
    for _ in 1:count
        y = FC.pop(y)
    end
    return y
end

Base.@noinline function bench_pop_right_mutable!(x, count)
    s = 0
    for _ in 1:count
        s += pop!(x)
    end
    return x, s
end

Base.@noinline function bench_pop_left_mutable!(x, count)
    s = 0
    for _ in 1:count
        s += popfirst!(x)
    end
    return x, s
end

Base.@noinline bench_checksum(x) = checksum(x)
Base.@noinline bench_split_ft(x, k) = FT.split(x, k)

Base.@noinline function bench_split_vector(x, k)
    return (x[1:k-1], x[k], x[k+1:end])
end

Base.@noinline bench_concat_ft(a, b) = FT.concat(a, b)
Base.@noinline bench_concat_pv(a, b) = FC.append(a, b)
Base.@noinline bench_concat_vector(a, b) = vcat(a, b)

# ---------------------------------------------------------------------------
# Benchmark suite
# ---------------------------------------------------------------------------

const SUITE = BenchmarkGroup()

# Number of logical operations performed by one evaluation of each benchmark.
const OPS_PER_EVAL = Dict{Tuple{String,Tuple{String,String}},Int}()

function addbench!(group, nkey, key, benchmark; ops=1)
    group[key] = benchmark
    OPS_PER_EVAL[(nkey, key)] = ops
    return benchmark
end

for n in (32, 1024, 32768)
    nkey = "n=$n"
    g = SUITE[nkey] = BenchmarkGroup()

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

    micro_count = micro_batch_size(n)
    index_count = index_batch_size(n)

    micro_indices = probe_indices(n, micro_count)
    index_indices = probe_indices(n, index_count)
    micro_values = collect(-1:-1:-micro_count)

    batch_count = min(128, max(2, n ÷ 8))
    spread_indices = unique(round.(Int, range(1, n; length=batch_count)))
    spread_values = -spread_indices
    cluster_start = max(1, n ÷ 2 - batch_count ÷ 2)
    clustered_indices = collect(cluster_start:cluster_start + batch_count - 1)
    clustered_values = -clustered_indices

    # Construction ----------------------------------------------------------

    addbench!(g, nkey, ("build", "ft-right"),
        @benchmarkable ft_build_right($n))

    addbench!(g, nkey, ("build", "ft-left"),
        @benchmarkable ft_build_left($n))

    addbench!(g, nkey, ("build", "pv-right"),
        @benchmarkable pv_build_right($n))

    addbench!(g, nkey, ("build", "deque-right"),
        @benchmarkable deque_build_right($n))

    addbench!(g, nkey, ("build", "deque-left"),
        @benchmarkable deque_build_left($n))

    addbench!(g, nkey, ("build", "vector-right"),
        @benchmarkable vector_build_right($n))

    addbench!(g, nkey, ("build", "vector-left"),
        @benchmarkable vector_build_left($n))

    # End insertion: batched ------------------------------------------------

    addbench!(g, nkey, ("push-right", "ft"),
        @benchmarkable bench_push_right_ft($(ftref)[], $micro_values) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("push-left", "ft"),
        @benchmarkable bench_push_left_ft($(ftref)[], $micro_values) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("push-right", "pv"),
        @benchmarkable bench_push_right_pv($(pvref)[], $micro_values) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("push-right", "deque"),
        @benchmarkable bench_push_right_mutable!(d, $micro_values) setup=(
            d = deque_build_right($n)
        ) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("push-left", "deque"),
        @benchmarkable bench_push_left_mutable!(d, $micro_values) setup=(
            d = deque_build_right($n)
        ) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("push-right", "vector"),
        @benchmarkable bench_push_right_mutable!(v, $micro_values) setup=(
            v = copy($(vecref)[]);
            sizehint!(v, $n + $micro_count)
        ) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("push-left", "vector"),
        @benchmarkable bench_push_left_mutable!(v, $micro_values) setup=(
            v = copy($(vecref)[]);
            sizehint!(v, $n + $micro_count)
        ) evals=1;
        ops=micro_count)

    # End removal: batched --------------------------------------------------

    pop_count = min(micro_count, max(1, n ÷ 2))

    addbench!(g, nkey, ("pop-right", "ft"),
        @benchmarkable bench_pop_right_ft($(ftref)[], $pop_count) evals=1;
        ops=pop_count)

    addbench!(g, nkey, ("pop-left", "ft"),
        @benchmarkable bench_pop_left_ft($(ftref)[], $pop_count) evals=1;
        ops=pop_count)

    addbench!(g, nkey, ("pop-right", "pv"),
        @benchmarkable bench_pop_right_pv($(pvref)[], $pop_count) evals=1;
        ops=pop_count)

    addbench!(g, nkey, ("pop-right", "deque"),
        @benchmarkable bench_pop_right_mutable!(d, $pop_count) setup=(
            d = deque_build_right($n)
        ) evals=1;
        ops=pop_count)

    addbench!(g, nkey, ("pop-left", "deque"),
        @benchmarkable bench_pop_left_mutable!(d, $pop_count) setup=(
            d = deque_build_right($n)
        ) evals=1;
        ops=pop_count)

    addbench!(g, nkey, ("pop-right", "vector"),
        @benchmarkable bench_pop_right_mutable!(v, $pop_count) setup=(
            v = copy($(vecref)[])
        ) evals=1;
        ops=pop_count)

    addbench!(g, nkey, ("pop-left", "vector"),
        @benchmarkable bench_pop_left_mutable!(v, $pop_count) setup=(
            v = copy($(vecref)[])
        ) evals=1;
        ops=pop_count)

    # Indexing: runtime-dependent batch ------------------------------------

    addbench!(g, nkey, ("index", "ft"),
        @benchmarkable bench_index($(ftref)[], $index_indices) evals=1;
        ops=index_count)

    addbench!(g, nkey, ("index", "pv"),
        @benchmarkable bench_index($(pvref)[], $index_indices) evals=1;
        ops=index_count)

    addbench!(g, nkey, ("index", "vector"),
        @benchmarkable bench_index($(vecref)[], $index_indices) evals=1;
        ops=index_count)

    # Persistent / copy-on-update: runtime-dependent batch ------------------

    addbench!(g, nkey, ("assoc", "ft"),
        @benchmarkable bench_assoc_ft(
            $(ftref)[], $micro_indices, $micro_values
        ) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("assoc", "pv"),
        @benchmarkable bench_assoc_pv(
            $(pvref)[], $micro_indices, $micro_values
        ) evals=1;
        ops=micro_count)

    addbench!(g, nkey, ("assoc", "vector-copy"),
        @benchmarkable bench_assoc_vector(
            $(vecref)[], $micro_indices, $micro_values
        ) evals=1;
        ops=micro_count)

    # Batched assoc: compare spread and shared-path workloads directly. ----

    addbench!(g, nkey, ("multiassoc-spread", "sequential"),
        @benchmarkable bench_assoc_ft(
            $(ftref)[], $spread_indices, $spread_values
        ) evals=1;
        ops=length(spread_indices))

    addbench!(g, nkey, ("multiassoc-spread", "batched"),
        @benchmarkable bench_multiassoc_ft(
            $(ftref)[], $spread_indices, $spread_values
        ) evals=1;
        ops=length(spread_indices))

    addbench!(g, nkey, ("multiassoc-clustered", "sequential"),
        @benchmarkable bench_assoc_ft(
            $(ftref)[], $clustered_indices, $clustered_values
        ) evals=1;
        ops=batch_count)

    addbench!(g, nkey, ("multiassoc-clustered", "batched"),
        @benchmarkable bench_multiassoc_ft(
            $(ftref)[], $clustered_indices, $clustered_values
        ) evals=1;
        ops=batch_count)

    # Traversal -------------------------------------------------------------

    addbench!(g, nkey, ("iterate", "ft"),
        @benchmarkable bench_checksum($(ftref)[]) evals=1)

    addbench!(g, nkey, ("iterate", "pv"),
        @benchmarkable bench_checksum($(pvref)[]) evals=1)

    addbench!(g, nkey, ("iterate", "deque"),
        @benchmarkable bench_checksum($(deqref)[]) evals=1)

    addbench!(g, nkey, ("iterate", "vector"),
        @benchmarkable bench_checksum($(vecref)[]) evals=1)

    # Split -----------------------------------------------------------------

    addbench!(g, nkey, ("split-middle", "ft"),
        @benchmarkable bench_split_ft($(ftref)[], $(kref)[]) evals=1)

    addbench!(g, nkey, ("split-middle", "vector"),
        @benchmarkable bench_split_vector($(vecref)[], $(kref)[]) evals=1)

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

    addbench!(g, nkey, ("concat", "ft"),
        @benchmarkable bench_concat_ft($(ft1ref)[], $(ft2ref)[]) evals=1)

    addbench!(g, nkey, ("concat", "pv"),
        @benchmarkable bench_concat_pv($(pv1ref)[], $(pv2ref)[]) evals=1)

    addbench!(g, nkey, ("concat", "vector"),
        @benchmarkable bench_concat_vector($(v1ref)[], $(v2ref)[]) evals=1)
end

# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

function n_from_key(key)
    return parse(Int, split(key, "=")[2])
end

function print_results(io, results)
    println(
        io,
        "n\toperation\timplementation\tops_per_eval\t" *
        "median_ns_per_op\tminimum_ns_per_op\t" *
        "memory_bytes_per_op\tallocations_per_op"
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

            ops = OPS_PER_EVAL[(nkey, key)]
            med = median(trial)
            minest = minimum(trial)

            @printf(
                io,
                "%d\t%s\t%s\t%d\t%.3f\t%.3f\t%.3f\t%.3f\n",
                n,
                operation,
                implementation,
                ops,
                med.time / ops,
                minest.time / ops,
                med.memory / ops,
                med.allocs / ops,
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
