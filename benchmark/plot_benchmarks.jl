using Plots
using Printf

# Usage:
#   julia plot_benchmarks.jl
#   julia plot_benchmarks.jl results/baseline-julia-1.12.6.tsv
#
# With no argument, the script chooses the newest
# results/baseline-julia-*.tsv next to this file.

struct BenchRow
    n::Int
    operation::String
    implementation::String
    ops_per_eval::Int
    median_ns::Float64
    minimum_ns::Float64
    memory_bytes::Float64
    allocations::Float64
end

function read_results(path)
    lines = readlines(path)
    isempty(lines) && error("Empty benchmark file: $path")

    header = split(lines[1], '\t')
    expected = [
        "n",
        "operation",
        "implementation",
        "ops_per_eval",
        "median_ns_per_op",
        "minimum_ns_per_op",
        "memory_bytes_per_op",
        "allocations_per_op",
    ]
    header == expected || error(
        "Unexpected TSV header.\nExpected: $(join(expected, '\t'))\nGot:      $(join(header, '\t'))"
    )

    rows = BenchRow[]
    for line in lines[2:end]
        isempty(strip(line)) && continue
        f = split(line, '\t')
        length(f) == 8 || error("Malformed line: $line")
        push!(
            rows,
            BenchRow(
                parse(Int, f[1]),
                f[2],
                f[3],
                parse(Int, f[4]),
                parse(Float64, f[5]),
                parse(Float64, f[6]),
                parse(Float64, f[7]),
                parse(Float64, f[8]),
            ),
        )
    end
    return rows
end

function default_input()
    results_dir = joinpath(@__DIR__, "results")
    isdir(results_dir) || error("No results directory found at $results_dir")

    files = filter(
        f -> startswith(f, "baseline-julia-") && endswith(f, ".tsv"),
        readdir(results_dir; join=true),
    )
    isempty(files) && error("No baseline-julia-*.tsv files found in $results_dir")
    return argmax(mtime, files)
end

function values_for(rows, operation, implementation, field)
    selected = filter(
        r -> r.operation == operation && r.implementation == implementation,
        rows,
    )
    sort!(selected; by=r -> r.n)
    ns = [r.n for r in selected]
    ys = [getfield(r, field) for r in selected]
    return ns, ys
end

implementations(rows, operation) =
    sort(unique(r.implementation for r in rows if r.operation == operation))

function plot_metric(
    rows,
    operations,
    field;
    ylabel,
    filename,
    yscale=:log10,
)
    panels = Any[]

    for op in operations
        p = plot(
            title=op,
            xlabel="n",
            ylabel=ylabel,
            xscale=:log2,
            yscale=yscale,
            legend=:best,
            marker=:circle,
            linewidth=2,
        )

        for impl in implementations(rows, op)
            ns, ys = values_for(rows, op, impl, field)

            # Log scales cannot display zero-allocation series.
            if yscale == :log10
                keep = findall(>(0), ys)
                isempty(keep) && continue
                ns = ns[keep]
                ys = ys[keep]
            end

            plot!(p, ns, ys; label=impl)
        end
        push!(panels, p)
    end

    ncols = 2
    nrows = cld(length(panels), ncols)
    fig = plot(
        panels...;
        layout=(nrows, ncols),
        size=(1100, 330 * nrows),
        plot_title="FingerTrees.jl performance experiment",
    )
    savefig(fig, filename)
    return fig
end

function plot_ft_vs_pv(rows, operations, filename)
    panels = Any[]

    for op in operations
        ft_ns, ft_time = values_for(rows, op, "ft", :median_ns)
        pv_ns, pv_time = values_for(rows, op, "pv", :median_ns)

        common = intersect(ft_ns, pv_ns)
        isempty(common) && continue

        ft = Dict(zip(ft_ns, ft_time))
        pv = Dict(zip(pv_ns, pv_time))
        ratios = [ft[n] / pv[n] for n in common]

        p = plot(
            common,
            ratios;
            title=op,
            xlabel="n",
            ylabel="FT time / PV time",
            xscale=:log2,
            yscale=:log10,
            marker=:circle,
            linewidth=2,
            label="FT / PV",
        )
        hline!(p, [1.0]; linestyle=:dash, label="equal")
        push!(panels, p)
    end

    ncols = 2
    nrows = cld(length(panels), ncols)
    fig = plot(
        panels...;
        layout=(nrows, ncols),
        size=(1000, 330 * nrows),
        plot_title="FingerTree relative to PersistentVector",
    )
    savefig(fig, filename)
    return fig
end

function print_large_n_summary(rows)
    nmax = maximum(r.n for r in rows)
    println("\nLargest n = $nmax")
    println(
        rpad("operation", 16),
        lpad("FT median", 14),
        lpad("PV median", 14),
        lpad("FT/PV", 10),
    )

    common_ops = sort!(collect(intersect(
        Set(r.operation for r in rows if r.n == nmax && r.implementation == "ft"),
        Set(r.operation for r in rows if r.n == nmax && r.implementation == "pv"),
    )))

    for op in common_ops
        ft = only(r for r in rows if r.n == nmax && r.operation == op && r.implementation == "ft")
        pv = only(r for r in rows if r.n == nmax && r.operation == op && r.implementation == "pv")
        @printf(
            "%-16s %11.3f ns %11.3f ns %9.2fx\n",
            op,
            ft.median_ns,
            pv.median_ns,
            ft.median_ns / pv.median_ns,
        )
    end
end

input = isempty(ARGS) ? default_input() : abspath(ARGS[1])
rows = read_results(input)

outdir = joinpath(dirname(input), "plots")
mkpath(outdir)

println("Reading: ", input)
println("Writing plots to: ", outdir)

# Operations for which scaling is especially informative.
time_ops = [
    "index",
    "assoc",
    "push-right",
    "pop-right",
    "iterate",
    "split-middle",
    "concat",
    "build",
]

memory_ops = [
    "index",
    "assoc",
    "push-right",
    "pop-right",
    "iterate",
    "split-middle",
    "concat",
]

common_ft_pv_ops = [
    "index",
    "assoc",
    "push-right",
    "pop-right",
    "iterate",
    "concat",
]

plot_metric(
    rows,
    time_ops,
    :median_ns;
    ylabel="median ns / operation",
    filename=joinpath(outdir, "time-scaling.png"),
)

plot_metric(
    rows,
    memory_ops,
    :memory_bytes;
    ylabel="allocated bytes / operation",
    filename=joinpath(outdir, "memory-scaling.png"),
)

plot_metric(
    rows,
    memory_ops,
    :allocations;
    ylabel="allocations / operation",
    filename=joinpath(outdir, "allocation-count-scaling.png"),
)

plot_ft_vs_pv(
    rows,
    common_ft_pv_ops,
    joinpath(outdir, "ft-vs-pv-ratio.png"),
)

print_large_n_summary(rows)

println("\nSaved:")
for f in (
    "time-scaling.png",
    "memory-scaling.png",
    "allocation-count-scaling.png",
    "ft-vs-pv-ratio.png",
)
    println("  ", joinpath(outdir, f))
end
