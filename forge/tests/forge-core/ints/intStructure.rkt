#lang forge/core

(require (prefix-in @ racket))

(pred SuccStructure
    (all ([i Int]) ; partial function
        (lone (join i succ)))

    (some ([i Int]) ; everything reachable from init
        (= (join i (* succ))
           Int))

    (some ([i Int]) ; there is a term
        (no (join i succ))))

(check succStructure1
       #:preds [SuccStructure]
       #:scope ([Int 1]))
(check succStructure2
       #:preds [SuccStructure]
       #:scope ([Int 2]))
(check succStructure3
       #:preds [SuccStructure]
       #:scope ([Int 3]))
(check succStructure4
       #:preds [SuccStructure]
       #:scope ([Int 4]))
(check succStructure5
       #:preds [SuccStructure]
       #:scope ([Int 5]))


(define (make-n n)
    (cond
      [(@= n 0) (sing (node/int/constant 0))]
      [(@< n 0) (join succ (make-n (add1 n)))]
      [(@> n 0) (join (make-n (sub1 n)) succ)]))

(pred (Size lower upper)
    ; lower
    (no (make-n (sub1 lower)))
    (some (make-n lower))

    ; upper
    (some (make-n upper))
    (no (make-n (add1 upper))))

(check size1
       #:preds [(Size -1 0)]
       #:scope ([Int 1]))

(check size2
       #:preds [(Size -2 1)]
       #:scope ([Int 2]))

(check size3
       #:preds [(Size -4 3)]
       #:scope ([Int 3]))

(check size4
       #:preds [(Size -8 7)]
       #:scope ([Int 4]))

(check size5
       #:preds [(Size -16 15)]
       #:scope ([Int 5]))