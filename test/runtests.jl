using FingerTrees
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
    @test [x for x in EmptyFT{Int}()] == Int[]
    @test [x for x in FingerTree([42])] == [42]
    @test [x for x in Iterators.take(ft, 17)] == collect(1:17)

    deepft = FingerTree(1:1024)
    @test [x for x in deepft] == collect(1:1024)
    mixedft = randomft(1024)
    @test [x for x in mixedft] == collect(1:1024)
    @test reduce(+, ft) == sum(1:100)

    left, x, right = FingerTrees.split(ft, 50)
    @test collect(left) == collect(1:49)
    @test x == 50
    @test collect(right) == collect(51:100)

    ft2 = assoc(ft, -1, 50)
    @test ft2[50] == -1
    @test ft[50] == 50  # persistence
end
