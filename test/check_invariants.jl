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

"Recursively verify every cached user measure in a measured tree."
function check_measured_invariants(tree::FT.MeasuredFingerTree)
    _, value = _check_measured_invariants(tree.root, tree.measureop)
    @test value == FT.measure(tree)
    nothing
end

function _check_measured_invariants(node, op)
    if node isa FT.EmptyFT
        return 0, Base.identity(op)
    elseif node isa FT.SingleFT
        child_len, child_value = _check_measured_invariants(node.a, op)
        @test node.value == child_value
        return child_len, child_value
    elseif node isa FT.DeepFT
        parts = map(child -> _check_measured_invariants(child, op),
                    (node.left, node.succ, node.right))
    elseif node isa FT.DigitFT
        parts = map(child -> _check_measured_invariants(child, op), node.child)
    elseif node isa FT.Tree23
        parts = map(child -> _check_measured_invariants(child, op), FT.astuple(node))
    else
        return 1, FT.measure(op, node)
    end

    total_len = sum(first, parts)
    total_value = foldl((left, right) -> FT.combine(op, left, last(right)),
                        parts; init=Base.identity(op))
    @test FT.len(node) == total_len
    @test node.value == total_value
    total_len, total_value
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
