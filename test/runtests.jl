using FingerTrees
using Random
using Test

const FT = FingerTrees

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

"Check cached measures and balancing invariants throughout the representation."
function check_invariants(node)
    if node isa FT.EmptyFT
        @test FT.len(node) == 0
        @test FT.dep(node) == 0
    elseif node isa FT.SingleFT
        check_invariants(node.a)
        @test FT.len(node) == FT.len(node.a)
        @test FT.dep(node) == FT.dep(node.a)
    elseif node isa FT.DeepFT
        check_invariants(node.left)
        check_invariants(node.succ)
        check_invariants(node.right)
        @test FT.len(node) == FT.len(node.left) + FT.len(node.succ) + FT.len(node.right)
        @test FT.dep(node.left) == FT.dep(node.right)
        @test isempty(node.succ) || FT.dep(node.succ) == FT.dep(node.left) + 1
    elseif node isa FT.DigitFT
        foreach(check_invariants, node.child)
        @test FT.len(node) == sum(FT.len, node.child)
        @test 1 <= FT.width(node) <= 4
    elseif node isa FT.Tree23
        children = FT.astuple(node)
        foreach(check_invariants, children)
        @test FT.len(node) == sum(FT.len, children)
        @test all(==(FT.dep(first(children))), FT.dep.(children))
        @test FT.width(node) in (2, 3)
    else
        @test FT.len(node) == 1
        @test FT.dep(node) == 0
    end

    nothing
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

    converted = FingerTree(Float64, 1:4)
    @test eltype(converted) === Float64
    @test collect(converted) == [1.0, 2.0, 3.0, 4.0]

    strings = FingerTree(["alpha", "beta", "gamma"])
    @test collect(strings) == ["alpha", "beta", "gamma"]
end

@testset "persistent end operations" begin
    original = FingerTree(1:20)
    extended = conjl(0, original)
    extended = conjr(extended, 21)

    @test collect(original) == collect(1:20)
    @test collect(extended) == collect(0:21)

    left_value, left_rest = splitl(extended)
    right_rest, right_value = splitr(extended)
    @test left_value == 0
    @test collect(left_rest) == collect(1:21)
    @test right_value == 21
    @test collect(right_rest) == collect(0:20)
    @test collect(extended) == collect(0:21)

    @test_throws BoundsError splitl(FingerTree(Int))
    @test_throws BoundsError splitr(FingerTree(Int))
end

@testset "indexing and ranges" begin
    tree = FingerTree(1:64)

    for i in eachindex(tree)
        @test tree[i] == i
        @test tree[Int32(i)] == i
    end

    @test_throws BoundsError tree[0]
    @test_throws BoundsError tree[65]
    @test_throws BoundsError FingerTree(Int)[1]

    for first_index in (1, 2, 17, 64), last_index in (first_index, 64)
        @test collect(tree[first_index:last_index]) == collect(first_index:last_index)
    end
    @test collect(tree[10:9]) == Int[]
    @test_throws BoundsError tree[0:1]
    @test_throws BoundsError tree[1:65]
end

@testset "split, update, and concatenation" begin
    tree = FingerTree(1:64)

    for i in (1, 2, 17, 32, 63, 64)
        left, value, right = split(tree, i)
        @test collect(left) == collect(1:i-1)
        @test value == i
        @test collect(right) == collect(i+1:64)

        updated = assoc(tree, -i, i)
        @test updated[i] == -i
        @test tree[i] == i
        @test length(updated) == length(tree)
    end

    @test_throws BoundsError split(tree, 0)
    @test_throws BoundsError split(tree, 65)
    @test_throws BoundsError assoc(tree, 0, 0)
    @test_throws BoundsError assoc(tree, 0, 65)

    for left_length in (0, 1, 2, 3, 8, 31), right_length in (0, 1, 2, 5, 16, 33)
        left = FingerTree(1:left_length)
        right = FingerTree(left_length+1:left_length+right_length)
        expected = collect(1:left_length+right_length)
        @test collect(concat(left, right)) == expected
        @test collect(FT.concat(left, left_length + 1, FingerTree(left_length+2:left_length+right_length+1))) ==
              collect(1:left_length+right_length+1)
    end

    empty_tree = FingerTree(Int)
    @test concat(empty_tree, empty_tree) === empty_tree
    @test collect(concat(empty_tree, tree)) == collect(1:64)
    @test collect(concat(tree, empty_tree)) == collect(1:64)
end

@testset "iteration and reduction" begin
    tree = FingerTree(1:1024)
    @test [x for x in tree] == collect(1:1024)
    @test [x for x in Iterators.take(tree, 17)] == collect(1:17)
    @test reduce(+, tree) == sum(1:1024)

    mixed = mixed_tree(collect(1:1024), MersenneTwister(0x5eed))
    @test [x for x in mixed] == collect(1:1024)
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
                right_rest, value = splitr(right_rest)
                @test value == n - i + 1
            end
            @test isempty(left_rest)
            @test isempty(right_rest)
        end
    end
end
