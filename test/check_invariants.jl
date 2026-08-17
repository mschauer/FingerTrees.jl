"""
    check_invariants(node)

Recursively verify the structural invariants and cached measures of a finger tree.
Lengths and depths are recomputed bottom-up from the representation, so a
consistent error in several cached fields cannot make the check pass.
"""
function check_invariants(node)
    _, _ = _check_invariants(node)
    nothing
end

function _check_invariants(node)
    if node isa FT.EmptyFT
        @test FT.len(node) == 0
        @test FT.dep(node) == 0
        return 0, 0

    elseif node isa FT.SingleFT
        child_len, child_depth = _check_invariants(node.a)
        @test FT.len(node) == child_len
        @test FT.dep(node) == child_depth
        return child_len, child_depth

    elseif node isa FT.DeepFT
        left_len, left_depth = _check_invariants(node.left)
        middle_len, middle_depth = _check_invariants(node.succ)
        right_len, right_depth = _check_invariants(node.right)

        total_len = left_len + middle_len + right_len
        @test FT.len(node) == total_len
        @test FT.dep(node) == left_depth
        @test left_depth == right_depth
        if isempty(node.succ)
            @test middle_len == 0
        else
            @test middle_depth == left_depth + 1
        end
        return total_len, left_depth

    elseif node isa FT.DigitFT
        @test 1 <= FT.width(node) <= 4
        @test length(node.child) == FT.width(node)

        results = map(_check_invariants, node.child)
        lengths = first.(results)
        depths = last.(results)
        total_len = sum(lengths)
        child_depth = first(depths)

        @test all(==(child_depth), depths)
        @test FT.len(node) == total_len
        @test FT.dep(node) == child_depth
        return total_len, child_depth

    elseif node isa FT.Tree23
        children = FT.astuple(node)
        @test length(children) in (2, 3)
        @test FT.width(node) == length(children)

        results = map(_check_invariants, children)
        lengths = first.(results)
        depths = last.(results)
        total_len = sum(lengths)
        child_depth = first(depths)
        node_depth = child_depth + 1

        @test all(==(child_depth), depths)
        @test FT.len(node) == total_len
        @test FT.dep(node) == node_depth
        return total_len, node_depth

    else
        @test FT.len(node) == 1
        @test FT.dep(node) == 0
        return 1, 0
    end
end
