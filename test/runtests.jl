include(joinpath("../src/ft.jl"))
using Base.Test
using FT

ft = FT.EmptyFT()
E = 'F'
if false
for i in 'A':E
    ft = FT.conj(ft,i)
    println(ft)
end
for i in 'A':E
        k , ft = FT.splitl(ft)
        println(k, "\t", ft)
end
end

function randomft(N, start = 1, verb = false)
    ft = FT.EmptyFT()
    b = randbool(N)
    l = sum(b) + start - 1
    u = l+1
    i = 1
    for i in 1:N
        if b[i] 
            ft = FT.conj(l, ft)
            l -= 1
        else 
            ft = FT.conj(ft,u)
            u += 1
        end
        verb &&     println(ft)

    end
    ft
end

function torture(N, verb=false)
    ft = randomft(N, 1, verb)
        
    for i in 1:N
        assert(ft[i] == i)
    end
    
    b = randbool(N)
    l = 1
    u = N
    for i in 1:N
        if b[i]
            k, ft = FT.splitl(ft)
            @test k == l
            l += 1
        else
            k, ft = FT.splitr(ft)
            @test k == u
            u -= 1
        end        
verb &&     println(k, " ",i, ft)
    end
    
end


for i in 1:50; torture(100); end
