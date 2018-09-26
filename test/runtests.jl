include(joinpath("../src/FingerTrees.jl"))

if VERSION < v"0.7"
    using Base.Test
else
    using Test, Random
end
function updown(E)
    ft = FingerTrees.EmptyFT{Char}()
    for i in 'A':E
        ft = FingerTrees.conjr(ft,i)
        println(ft)
    end
    for i in 'A':E
            k , ft = FingerTrees.splitl(ft)
            println(k, "\t", ft)
    end
end
ft = updown('E')
#ft = updown('Z')


function randomft(N, start = 1, verb = false)
    ft = FingerTrees.EmptyFT{Int}()
    b = bitrand(N)
    l = sum(b) + start - 1
    u = l+1
    i = 1
    for i in 1:N
        if b[i]
            ft = FingerTrees.conjl(l, ft)
            l -= 1
        else
            ft = FingerTrees.conjr(ft,u)
            u += 1
        end
        verb &&     println(ft)

    end
    ft
end

randomft(12, true)

function torture(N, verb=false)
    ft = randomft(N, 1, verb)


    # checks integrity
    for i in 1:N
        @test ft[i] == i
    end


    b = bitrand(N)
    l = 1
    u = N
    for i in 1:N
        if b[i]
            k, ft = FingerTrees.splitl(ft)
            @test k == l
            l += 1
        else
            ft, k = FingerTrees.splitr(ft)
            @test k == u
            u -= 1
        end
verb &&     println(k, " ",i, ft)
    end
    @assert(FingerTrees.isempty(ft))
    n = N
    ft = FingerTrees.concat(randomft(n), randomft(n,n+1))
    FingerTrees.traverse((x,l)->@test(isa(x, Int)), ft)
#=    j = 1
    for i in ft
        @test j==i
        j += 1
    end
=#
    i = rand(1:N)
    println("split $N at $i")
    a, j, b = FingerTrees.split(randomft(N), i)
    for k in 1:i-1
        @test a[k] == k
    end
    @test i==j
    for k in i+1:N
        @test b[k-i] == k
    end

end


torture(3); torture(10); torture(100);
@time for i in 1:100; torture(3); torture(10); torture(100); end
println("done")
ft = FingerTrees.concat(randomft(10), randomft(10,11));
