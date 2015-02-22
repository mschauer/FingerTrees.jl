using FingerTrees
using FunctionalCollections
const FT = FingerTrees
const FC = FunctionalCollections


function fctest(N, n, verbose=true)                                     
    verbose && println("PersistentVector")

    x = PersistentVector(1:n)
    verbose && println("construct")
    @time for i in 1:N
        x = PersistentVector(1:n)
    end
    x = append(x, n+1)
    verbose && println("append")
    @time for i in 2:n
        x = append(x, n+i)
    end
    x = assoc(x, 1, n)
    x = assoc(x, n, 1)
    verbose && println("assoc")
    @time for i in 1:N
        x = assoc(x, n-i, n+i)
        x = assoc(x, n+i, n-i)
    end
    verbose && println("getindex")
    y = 0
    @time for i in 1:N
        y += x[mod1(n+i, 2n)]
    end
    verbose && println("iterator")
    @time for i in x
        y += i
    end
    verbose && println("reduce")
    @time for i in 1:N
        y += reduce(+, x)
    end
    verbose && println("reduce and subset")
    @time for i in 1:N
        y += reduce(+, PersistentVector([x[k] for k in N:n-N]))
    end
    verbose && println(y)
    
end
                                                                
function fttest(N, n, verbose=true)                             
    verbose && println("FingerTree")
    x = FingerTree(1:n)
    verbose && println("construct")
    @time for i in 1:N
        x = FingerTree(1:n)
    end
    x = x |> (n+1)
    verbose && println("append")
    @time for i in 2:n
        x = x |> (n+i)
    end
    x = FT.assoc(x, 1, n)
    x = FT.assoc(x, n, 1)
    verbose && println("assoc")
    @time for i in 1:N
        x = FT.assoc(x, n-i, n+i)
        x = FT.assoc(x, n+i, n-i)
    end
    y = 0
    verbose && println("getindex")
    @time for i in 1:N
        y += x[mod1(n+i, 2n)]
    end
    verbose && println("iterator")
    @time for i in x
        y += i
    end
    verbose && println("reduce")
    @time for i in 1:N
        y += reduce(+, x)
    end
    verbose && println("reduce and subset")
    @time for i in 1:N
        y += reduce(+, x[N:n-N])
    end
    verbose && println(y)
    
end
fttest(1, 10, false)
fctest(1, 10, false)

fttest(100, 1000)
fctest(100, 1000)

