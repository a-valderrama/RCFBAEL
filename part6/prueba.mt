(+ 2 4) 
(equal-lst? (list #\h #\o #\l #\a) (list #\a #\l #\o #\h))
(iszero? 6)
(if (iszero? 3) "cond1" "cond2")
(if #f "adios")
(let ([y Int 5] [z Int (+ y 2)]) (< y z))
(begin (+ 1 3) (list 4 5 6 7) (empty? (list 1)))
(let ([x Int 0]) (++ x))
(list #\c #\o)