using FingerTrees
using Random
using Test

const FT = FingerTrees

struct MinimumSecond <: FT.Measure end
Base.identity(::MinimumSecond) = typemax(Int)
FT.measure(::MinimumSecond, value::Pair) = last(value)
FT.combine(::MinimumSecond, left::Int, right::Int) = min(left, right)

struct ConcatenateMeasure <: FT.Measure end
Base.identity(::ConcatenateMeasure) = ""
FT.measure(::ConcatenateMeasure, value) = string(value)
FT.combine(::ConcatenateMeasure, left::String, right::String) = left * right

struct CountingLength <: FT.Measure
    calls::Base.RefValue{Int}
end
Base.identity(::CountingLength) = 0
function FT.measure(op::CountingLength, _)
    op.calls[] += 1
    1
end
FT.combine(::CountingLength, left::Int, right::Int) = left + right
include("check_invariants.jl")

"Build the same sequence while exercising both persistent end operations."
function mixed_tree(values, rng)
    tree = FingerTree(eltype(values))
    choices = rand(rng, Bool, length(values))
    left = firstindex(values) + count(choices) - 1
    right = left + 1

    for insert_left in choices
        if insert_left
            tree = conjl(values[left], tree)
            left -= 1
        else
            tree = conjr(tree, values[right])
            right += 1
        end
    end

    tree
end

@testset "construction and collection interface" begin
    empty_tree = FingerTree(Int)
    @test empty_tree isa EmptyFT{Int}
    @test eltype(empty_tree) === Int
    @test isempty(empty_tree)
    @test length(empty_tree) == 0
    @test [x for x in empty_tree] == Int[]
    @test eachindex(empty_tree) == Base.OneTo(0)
    @test keys(empty_tree) == Base.OneTo(0)
    @test copy(empty_tree) === empty_tree
    @test empty(empty_tree) isa EmptyFT{Int}
    check_invariants(empty_tree)

    tree = FingerTree(1:100)
    @test eltype(tree) === Int
    @test length(tree) == 100
    @test !isempty(tree)
    @test first(tree) == 1
    @test last(tree) == 100
    @test firstindex(tree) == 1
    @test lastindex(tree) == 100
    @test eachindex(tree) == Base.OneTo(100)
    @test keys(tree) == Base.OneTo(100)
    @test copy(tree) === tree
    @test empty(tree) isa EmptyFT{Int}
    @test tree == FingerTree(1:100)
    @test tree != FingerTree(2:101)
    @test tree != FingerTree(1:99)
    check_invariants(tree)

    converted = FingerTree(Float64, 1:4)
    @test eltype(converted) === Float64
    @test collect(converted) == [1.0, 2.0, 3.0, 4.0]
    check_invariants(converted)

    strings = FingerTree(["alpha", "beta", "gamma"])
    @test collect(strings) == ["alpha", "beta", "gamma"]
    check_invariants(strings)
end

@testset "measured finger tree" begin
    tree = MeasuredFingerTree(1:64, LengthMeasure())

    @test tree isa MeasuredFingerTree{Int,LengthMeasure,Int}
    @test measure(tree) == 64
    check_measured_invariants(tree)
    @test length(tree) == 64
    @test collect(tree) == collect(1:64)
    @test tree[17] == 17
    @test collect(tree[10:14]) == collect(10:14)
    @test measure(tree[10:14]) == 5

    root = FingerTree(1:64)
    wrapped = MeasuredFingerTree(root, LengthMeasure())
    @test FingerTree(wrapped) == root
    @test measure(wrapped) == 64

    extended = conjr(conjl(0, tree), 65)
    @test measure(extended) == 66
    @test first(extended) == 0
    @test last(extended) == 65
    check_measured_invariants(extended)

    left, value, right = split(tree, 32)
    @test value == 32
    @test measure(left) == 31
    @test measure(right) == 32
    @test collect(concat(left, conjl(value, right))) == collect(1:64)
    check_measured_invariants(left)
    check_measured_invariants(right)

    empty_left, first_value, after_first = split(tree, 1)
    before_last, last_value, empty_right = split(tree, length(tree))
    @test isempty(empty_left) && measure(empty_left) == 0
    @test first_value == 1 && collect(after_first) == collect(2:64)
    @test collect(before_last) == collect(1:63) && last_value == 64
    @test isempty(empty_right) && measure(empty_right) == 0

    prefix, found, suffix = split_measure(summary -> summary >= 17, tree)
    @test measure(prefix) == 16
    @test found == 17
    @test first(suffix) == 18
    @test_throws BoundsError split_measure(summary -> summary > 64, tree)

    updated = assoc(tree, -32, 32)
    @test updated[32] == -32
    @test measure(updated) == 64
    @test measure(empty(tree)) == 0
    check_measured_invariants(updated)

    priorities = [:a => 5, :b => 3, :c => 7, :d => 1]
    queue = MeasuredFingerTree(priorities, MinimumSecond())
    @test measure(queue) == 1

    before, event, after = split_measure(summary -> summary <= 3, queue)
    @test collect(before) == [:a => 5]
    @test event == (:b => 3)
    @test collect(after) == [:c => 7, :d => 1]

    changed = assoc(queue, :d => 9, 4)
    @test measure(changed) == 3
    check_measured_invariants(queue)
    check_measured_invariants(changed)

    ordered = MeasuredFingerTree(1:4, ConcatenateMeasure())
    @test measure(ordered) == "1234"
    ordered_left, ordered_value, ordered_right =
        split_measure(summary -> ncodeunits(summary) >= 3, ordered)
    @test measure(ordered_left) == "12"
    @test ordered_value == 3
    @test measure(ordered_right) == "4"
    check_measured_invariants(ordered)

    calls = Ref(0)
    counting = MeasuredFingerTree(1:4096, CountingLength(calls))
    calls[] = 0
    counted_left, counted_value, counted_right =
        split_measure(summary -> summary >= 2048, counting)
    @test counted_value == 2048
    @test length(counted_left) == 2047
    @test length(counted_right) == 2048
    @test calls[] < 100
    check_measured_invariants(counting)

    counted_left, counted_value, counted_right = split(counting, 2048)
    calls[] = 0
    rejoined = concat(conjr(counted_left, counted_value), counted_right)
    @test collect(rejoined) == collect(1:4096)
    @test measure(rejoined) == 4096
    @test calls[] < 20
    check_measured_invariants(rejoined)
end

@testset "persistent priority queue" begin
    empty_queue = PriorityQueue(Symbol, Int)
    @test isempty(empty_queue)
    @test length(empty_queue) == 0
    @test eltype(empty_queue) == Pair{Symbol,Int}
    @test copy(empty_queue) === empty_queue
    @test isempty(empty(empty_queue))
    @test_throws BoundsError peek(empty_queue)
    @test_throws BoundsError dequeue(empty_queue)

    queue = PriorityQueue([:a => 5, :b => 3, :c => 3, :d => 1])
    @test length(queue) == 4
    @test peek(queue) == (:d => 1)
    @test first(queue) == (:d => 1)
    @test peekpriority(queue) == 1
    @test collect(queue) == [:d => 1, :b => 3, :c => 3, :a => 5]
    check_measured_invariants(queue.tree)

    entry, remaining = dequeue(queue)
    @test entry == (:d => 1)
    @test collect(remaining) == [:b => 3, :c => 3, :a => 5]
    @test collect(queue) == [:d => 1, :b => 3, :c => 3, :a => 5]
    check_measured_invariants(remaining.tree)

    string_priorities = PriorityQueue([:later => "z", :earlier => "a"])
    @test peek(string_priorities) == (:earlier => "a")

    extended = enqueue(queue, :e, 0)
    extended = enqueue(extended, :f => 3)
    @test peek(extended) == (:e => 0)
    @test length(queue) == 4
    @test collect(extended) == [:e => 0, :d => 1, :b => 3, :c => 3, :f => 3, :a => 5]

    rng = MersenneTwister(0xdeadbeef)
    random_queue = PriorityQueue(Int, Int)
    inserted = Pair{Int,Int}[]
    for value in 1:500
        priority = rand(rng, -20:20)
        random_queue = enqueue(random_queue, value, priority)
        push!(inserted, value => priority)
    end

    expected = sort(inserted; by=last, alg=Base.Sort.MergeSort)
    @test collect(random_queue) == expected
    check_measured_invariants(random_queue.tree)

    for expected_entry in expected
        actual_entry, random_queue = dequeue(random_queue)
        @test actual_entry == expected_entry
    end
    @test isempty(random_queue)
end

@testset "persistent end operations" begin
    original = FingerTree(1:20)
    extended = conjl(0, original)
    extended = conjr(extended, 21)

    @test collect(original) == collect(1:20)
    @test collect(extended) == collect(0:21)
    check_invariants(original)
    check_invariants(extended)

    left_value, left_rest = splitl(extended)
    right_rest, right_value = splitr(extended)
    @test left_value == 0
    @test collect(left_rest) == collect(1:21)
    @test right_value == 21
    @test collect(right_rest) == collect(0:20)
    @test collect(extended) == collect(0:21)
    check_invariants(left_rest)
    check_invariants(right_rest)
    check_invariants(extended)

    @test_throws BoundsError splitl(FingerTree(Int))
    @test_throws BoundsError splitr(FingerTree(Int))
end

@testset "indexing and ranges" begin
    tree = FingerTree(1:64)
    check_invariants(tree)

    for i in eachindex(tree)
        @test tree[i] == i
        @test tree[Int32(i)] == i
    end

    @test_throws BoundsError tree[0]
    @test_throws BoundsError tree[65]
    @test_throws BoundsError FingerTree(Int)[1]

    for first_index in (1, 2, 17, 64), last_index in (first_index, 64)
        slice = tree[first_index:last_index]
        @test collect(slice) == collect(first_index:last_index)
        check_invariants(slice)
    end
    empty_slice = tree[10:9]
    @test collect(empty_slice) == Int[]
    check_invariants(empty_slice)
    @test_throws BoundsError tree[0:1]
    @test_throws BoundsError tree[1:65]
end

@testset "split, update, and concatenation" begin
    tree = FingerTree(1:64)
    check_invariants(tree)

    for i in (1, 2, 17, 32, 63, 64)
        left, value, right = split(tree, i)
        @test collect(left) == collect(1:i-1)
        @test value == i
        @test collect(right) == collect(i+1:64)
        check_invariants(left)
        check_invariants(right)

        updated = assoc(tree, -i, i)
        @test updated[i] == -i
        @test tree[i] == i
        @test length(updated) == length(tree)
        check_invariants(updated)
        check_invariants(tree)
    end

    @test_throws BoundsError split(tree, 0)
    @test_throws BoundsError split(tree, 65)
    @test_throws BoundsError assoc(tree, 0, 0)
    @test_throws BoundsError assoc(tree, 0, 65)

    for left_length in (0, 1, 2, 3, 8, 31), right_length in (0, 1, 2, 5, 16, 33)
        left = FingerTree(1:left_length)
        right = FingerTree(left_length+1:left_length+right_length)
        expected = collect(1:left_length+right_length)

        joined = concat(left, right)
        @test collect(joined) == expected
        check_invariants(joined)

        joined_with_middle = FT.concat(
            left,
            left_length + 1,
            FingerTree(left_length+2:left_length+right_length+1),
        )
        @test collect(joined_with_middle) == collect(1:left_length+right_length+1)
        check_invariants(joined_with_middle)
    end

    empty_tree = FingerTree(Int)
    @test concat(empty_tree, empty_tree) === empty_tree

    right_joined = concat(empty_tree, tree)
    left_joined = concat(tree, empty_tree)
    @test collect(right_joined) == collect(1:64)
    @test collect(left_joined) == collect(1:64)
    check_invariants(right_joined)
    check_invariants(left_joined)
end

@testset "iteration and reduction" begin
    tree = FingerTree(1:1024)
    @test [x for x in tree] == collect(1:1024)
    @test [x for x in Iterators.take(tree, 17)] == collect(1:17)
    @test reduce(+, tree) == sum(1:1024)
    check_invariants(tree)

    mixed = mixed_tree(collect(1:1024), MersenneTwister(0x5eed))
    @test [x for x in mixed] == collect(1:1024)
    check_invariants(mixed)
end

@testset "representation invariants" begin
    rng = MersenneTwister(0xf17e)

    for n in (0, 1, 2, 3, 8, 32, 127, 1024)
        tree = mixed_tree(collect(1:n), rng)
        @test collect(tree) == collect(1:n)
        check_invariants(tree)

        if n <= 127
            left_rest = tree
            right_rest = tree
            for i in 1:n
                value, left_rest = splitl(left_rest)
                @test value == i
                check_invariants(left_rest)

                right_rest, value = splitr(right_rest)
                @test value == n - i + 1
                check_invariants(right_rest)
            end
            @test isempty(left_rest)
            @test isempty(right_rest)
        end
    end
end

@testset "assoc" begin
    for n in (1, 2, 3, 10, 100, 1024)
        ft = FingerTree(1:n)
        check_invariants(ft)

        for i in unique((1, max(1, n ÷ 2), n))
            replacement = -i
            updated = assoc(ft, replacement, i)

            expected = collect(1:n)
            expected[i] = replacement

            @test collect(updated) == expected
            @test collect(ft) == collect(1:n)   # persistence
            @test length(updated) == n
            check_invariants(updated)
            check_invariants(ft)
        end
    end

    ft = FingerTree(1:10)
    @test_throws BoundsError assoc(ft, 0, 0)
    @test_throws BoundsError assoc(ft, 0, 11)
end

@testset "batched assoc and update" begin
    rng = MersenneTwister(0xba7c4)

    for n in (1, 2, 3, 10, 100, 1024)
        tree = FingerTree(1:n)
        count = min(n, 17)
        indices = sort!(randperm(rng, n)[1:count])
        values = -indices

        updated = multiassoc(tree, reverse(indices), reverse(values))
        expected = collect(1:n)
        expected[indices] = values
        @test collect(updated) == expected
        @test collect(tree) == collect(1:n)
        check_invariants(updated)
        check_invariants(tree)

        presorted = multiassoc(tree, indices, values; presorted=true)
        @test collect(presorted) == expected
        check_invariants(presorted)

        calls = Tuple{Int,Int}[]
        transformed = multiupdate(tree, indices; presorted=true) do index, old
            push!(calls, (index, old))
            old + 10index
        end
        transformed_expected = collect(1:n)
        transformed_expected[indices] .+= 10 .* indices
        @test collect(transformed) == transformed_expected
        @test calls == [(index, index) for index in indices]
        check_invariants(transformed)
    end

    measured = MeasuredFingerTree(1:128, ConcatenateMeasure())
    measured_updated = multiassoc(measured, [100, 1, 64], [-100, -1, -64])
    expected = collect(1:128)
    expected[[100, 1, 64]] = [-100, -1, -64]
    @test collect(measured_updated) == expected
    @test measure(measured_updated) == join(expected)
    @test collect(measured) == collect(1:128)
    check_measured_invariants(measured_updated)
    check_measured_invariants(measured)

    transformed = multiupdate(measured, [1, 64, 128], (index, old) -> old - index;
                              presorted=true)
    expected = collect(1:128)
    expected[[1, 64, 128]] .= 0
    @test collect(transformed) == expected
    @test measure(transformed) == join(expected)
    check_measured_invariants(transformed)

    tree = FingerTree(1:10)
    measured_tree = MeasuredFingerTree(1:10, LengthMeasure())
    @test multiassoc(tree, Int[], Int[]) === tree
    @test multiupdate(tree, Int[], +) === tree
    @test multiassoc(measured_tree, Int[], Int[]) === measured_tree
    @test multiupdate(measured_tree, Int[], +) === measured_tree

    @test_throws DimensionMismatch multiassoc(tree, [1, 2], [10])
    @test_throws ArgumentError multiassoc(tree, [2, 2], [20, 21])
    @test_throws ArgumentError multiassoc(tree, [2, 1], [20, 10]; presorted=true)
    @test_throws ArgumentError multiupdate(tree, [2, 2], (_, old) -> old)
    @test_throws BoundsError multiassoc(tree, [0], [1])
    @test_throws BoundsError multiassoc(tree, [11], [1])
    @test_throws BoundsError multiupdate(tree, [0], (_, old) -> old)
    @test_throws InexactError multiassoc(tree, [1], [1.5])
end
