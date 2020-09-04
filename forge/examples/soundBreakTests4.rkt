#lang forge

option verbosity 10
--option show 0

--sig A { f : set B }
--sig B { g : set A, h : set C }
--sig C extends A {}
--
--/*$
--(pred char
--    (some ((A0 C)) (some ((B2 B)) (some ((A3 C)) (some ((B3 B)) 
--        (some ((B0 B)) (some ((A1 A)) (some ((B1 B)) (some ((A2 A)) (and 
--            (! (= B0 B1)) (! (= B0 B2)) (! (= B0 B3)) (! (= B1 B0)) 
--            (! (= B1 B2)) (! (= B1 B3)) (! (= B2 B0)) (! (= B2 B1)) 
--            (! (= B2 B3)) (! (= B3 B0)) (! (= B3 B1)) (! (= B3 B2)) 
--            (! (= A0 A3)) (! (= A3 A0)) (! (= A0 A1)) (! (= A0 A2)) 
--            (! (= A0 A3)) (! (= A1 A0)) (! (= A1 A2)) (! (= A1 A3)) 
--            (! (= A2 A0)) (! (= A2 A1)) (! (= A2 A3)) (! (= A3 A0)) 
--            (! (= A3 A1)) (! (= A3 A2)) 
--            (= g (+ (-> B0 A3) (-> B1 A0) (-> B2 A2) (-> B3 A0))) 
--            (= h (+ (-> B0 A0) (-> B1 A3) (-> B2 A0) (-> B3 A0))) 
--            (= B (+ B0 B1 B2 B3)) 
--            (= C (+ A0 A3)) 
--            (= f (+ (-> A0 B0) (-> A1 B2) (-> A2 B1) (-> A3 B2))) 
--            (= A (+ A0 A1 A2 A3)))))))))))
--)
--*/
--
--run {char} for {
--    f is default
--    g is default
--    h is default
   
--    f is func
--    g is func
--    h is func
--}

sig A { f : set B }
sig B { g : set A }

/*$
(pred char
(some ((A0 A)) (some ((B0 B)) (some ((A1 A)) (some ((B1 B)) (and (! (= B0 B1)) (! (= B1 B0)) (! (= A0 A1)) (! (= A1 A0)) (= g (+ (-> B0 A1) (-> B1 A0))) (= B (+ B0 B1)) (= f (+ (-> A0 B1) (-> A1 B0))) (= A (+ A0 A1)))))))
)
*/

run { char } for {
    #A = 2
    #B = 2
--    f is default
--    g is default
    f is bij
    g is bij
}

