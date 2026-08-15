#!/usr/bin/env python3
"""Minimal Julia-1.x compatibility pass for mschauer/FingerTrees.jl.

Run from the root of an unmodified checkout of
https://github.com/mschauer/FingerTrees.jl

The script deliberately preserves the original representation.  It only:
  * replaces Nullables with Union{Nothing,T};
  * updates a few removed Base APIs;
  * updates type aliases to const aliases;
  * repairs three small legacy bugs exposed by the compatibility pass;
  * restores a minimal modern iterator and reduce implementation;
  * creates Project.toml and a deterministic Pkg.test() test suite;
  * removes REQUIRE.
"""

from pathlib import Path
import sys

ROOT = Path.cwd()
SRC = ROOT / "src" / "FingerTrees.jl"
TEST = ROOT / "test" / "runtests.jl"
PROJECT = ROOT / "Project.toml"
REQUIRE = ROOT / "REQUIRE"

if not SRC.exists() or not TEST.exists():
    raise SystemExit(
        "Run this script from the root of the original FingerTrees.jl checkout "
        "(expected src/FingerTrees.jl and test/runtests.jl)."
    )
if PROJECT.exists():
    raise SystemExit("Project.toml already exists; refusing to overwrite it.")

text = SRC.read_text()


def replace_once(old: str, new: str, label: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one match, found {count}")
    text = text.replace(old, new, 1)


# Nullable -> the standard Julia 1.x optional-value representation.
replace_once("using Nullables\n", "", "Nullables import")
replace_once("    c::Nullable{T}\n", "    c::Union{Nothing,T}\n", "Leaf23 nullable field")
replace_once(
    "        new{T}(a, b, Nullable{T}(), len(a)+len(b), dep(a)+1)\n",
    "        new{T}(a, b, nothing, len(a)+len(b), dep(a)+1)\n",
    "Leaf23 empty third child",
)
replace_once(
    "    c::Nullable{Tree23{T}}\n",
    "    c::Union{Nothing,Tree23{T}}\n",
    "Node23 nullable field",
)
replace_once(
    "        new{T}(a, b, Nullable{Tree23}(), len(a)+len(b), dep(a)+1)\n",
    "        new{T}(a, b, nothing, len(a)+len(b), dep(a)+1)\n",
    "Node23 empty third child",
)

# Parametric aliases are global constants in modern Julia.
for n in range(1, 5):
    replace_once(
        f"DigitFT{n}{{T}} = DigitFT{{T,{n}}}\n",
        f"const DigitFT{n}{{T}} = DigitFT{{T,{n}}}\n",
        f"DigitFT{n} alias",
    )
replace_once(
    "NonEmptyFT{T} = Union{SingleFT{T},DeepFT{T}}\n",
    "const NonEmptyFT{T} = Union{SingleFT{T},DeepFT{T}}\n",
    "NonEmptyFT alias",
)

# Obvious legacy bug: width must be 2 or 3, not length(2/3).
replace_once(
    "width(n::Tree23) = length(isnull(n.c) ? 3 : 2)\n",
    "width(n::Tree23) = isnothing(n.c) ? 2 : 3\n",
    "Tree23 width",
)

# Remaining Nullable operations.
text = text.replace("isnull(n.c)", "isnothing(n.c)")
text = text.replace("get(n.c)", "something(n.c)")

# Removed/changed Base APIs.
replace_once(
    "     v = Array(eltype(xs), len(xs))\n",
    "     v = Vector{eltype(xs)}(undef, len(xs))\n",
    "Vector allocation",
)
replace_once("    i = start(r)\n", "    i = first(r)\n", "UnitRange start")

# The old three-argument reduce protocol is no longer the public reduction API.
old_reduce = """Base.reduce(op::Function, v, ::EmptyFT) = v
Base.reduce(op::Function, v, t::SingleFT) = reduce(op, v, ft.a)
function Base.reduce(op::Function, v, d::DigitFT)
    for k in 1:width(d)
        v = reduce(op, v, d.child[k])
    end
    v
end
function Base.reduce(op::Function, v, n::Tree23)
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
"""
new_reduce = """_reduce(op::Function, v, a) = op(v, a)
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
"""
replace_once(old_reduce, new_reduce, "legacy reduce block")

# Add type-level eltype and a simple persistent-state iterator.  The old
# start/next/done iterator is commented out in the repository, while perf.jl
# still benchmarks iteration.
replace_once(
    "eltype(b::FingerTree{T}) where {T} = T\neltype(b::DigitFT{T}) where {T} = T\n",
    "eltype(b::FingerTree{T}) where {T} = T\n"
    "eltype(b::DigitFT{T}) where {T} = T\n"
    "Base.eltype(::Type{<:FingerTree{T}}) where {T} = T\n",
    "type-level eltype",
)

iterator_block = """
Base.iterate(::EmptyFT) = nothing
function Base.iterate(ft::FingerTree)
    x, rest = splitl(ft)
    x, rest
end
Base.iterate(::FingerTree, ::EmptyFT) = nothing
function Base.iterate(::FingerTree, rest::FingerTree)
    x, tail = splitl(rest)
    x, tail
end

"""
replace_once(
    "traverse(op, ft) = (traverse(op, ft, 1);)\n",
    "traverse(op, ft) = (traverse(op, ft, 1);)\n" + iterator_block,
    "modern iterator insertion",
)

# show(io, ...) must not write the long-tree placeholder to stdout.
text = text.replace(': print(" ... ")', ': print(io, " ... ")')

# Sanity checks: these should survive only inside the large commented legacy
# iterator block, if at all.
for forbidden in ("Nullable{", "using Nullables", "isnull(n.c)", "get(n.c)",
                  "Array(eltype(xs), len(xs))", "i = start(r)"):
    if forbidden in text:
        raise RuntimeError(f"compatibility token still present: {forbidden!r}")

SRC.write_text(text)

PROJECT.write_text("""name = "FingerTrees"
uuid = "3d24749a-0845-4c16-a2f2-051d7e3c7003"
version = "0.1.0"

[compat]
julia = "1.10"

[extras]
Random = "9a3f8284-a2c9-5f02-9a11-845980a1fd5c"
Test = "8dfed614-e22c-5e08-85e1-65c5234f0b40"

[targets]
test = ["Random", "Test"]
""")

TEST.write_text(r'''using FingerTrees
using Random
using Test

function randomft(N, start=1, verb=false)
    ft = EmptyFT{Int}()
    b = bitrand(N)
    l = sum(b) + start - 1
    u = l + 1
    for i in 1:N
        if b[i]
            ft = conjl(l, ft)
            l -= 1
        else
            ft = conjr(ft, u)
            u += 1
        end
        verb && println(ft)
    end
    ft
end

function torture(N, verb=false)
    ft = randomft(N, 1, verb)

    for i in 1:N
        @test ft[i] == i
    end

    b = bitrand(N)
    l = 1
    u = N
    for i in 1:N
        if b[i]
            k, ft = splitl(ft)
            @test k == l
            l += 1
        else
            ft, k = splitr(ft)
            @test k == u
            u -= 1
        end
        verb && println(k, " ", i, " ", ft)
    end
    @test isempty(ft)

    n = N
    ft = FingerTrees.concat(randomft(n), randomft(n, n + 1))
    traverse((x, _) -> @test(x isa Int), ft)

    i = rand(1:N)
    a, j, b = FingerTrees.split(randomft(N), i)
    for k in 1:i-1
        @test a[k] == k
    end
    @test i == j
    for k in i+1:N
        @test b[k-i] == k
    end
end

@testset "legacy FingerTrees operations" begin
    Random.seed!(0x5eed)
    for N in (3, 10, 100)
        torture(N)
    end
end

@testset "Julia 1.x compatibility" begin
    ft = FingerTree(1:100)
    @test length(ft) == 100
    @test collect(ft) == collect(1:100)
    @test [x for x in ft] == collect(1:100)
    @test reduce(+, ft) == sum(1:100)

    left, x, right = FingerTrees.split(ft, 50)
    @test collect(left) == collect(1:49)
    @test x == 50
    @test collect(right) == collect(51:100)

    ft2 = assoc(ft, -1, 50)
    @test ft2[50] == -1
    @test ft[50] == 50  # persistence
end
''')

if REQUIRE.exists():
    REQUIRE.unlink()

print("Modernization applied.")
print("Next run:")
print("  julia --project=. -e 'using Pkg; Pkg.test()'")
