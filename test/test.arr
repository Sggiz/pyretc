
fun f(x :: Any) -> Any block: 
    1
end

fun dam(x :: Number) -> Number: "a" end

lam(x :: Number) -> Number: "a" end

cases (b) 1 block:
| a => 1
| b => 2
| c =>3
end

lam(x :: Number) -> Number: cases (a) 1: | x => 2 end end

fun f<a>(x :: a) -> a: x end

