#lang forge/core

(set-option! 'verbose 0)

(sig A)
(relation otherA (A A))

(sig B)
(relation otherB (B A))

(inst relations
    (is otherA func)
    (is otherB func))

(pred ComprehensionsOnSigs
    (= (set ([a A])
           (in (-> a a) otherA))
       (join A (& otherA iden))))

(pred ComprehensionsOnSets
    (= (set ([x (+ A B)])
           (some ([y A])
               (or (= (join x otherA)
                      y)
                   (= (join x otherB)
                      y))))
       (join (+ otherA otherB)
             A)))

(pred MultiComprehension
    (= (set ([b B] [a A])
           (some ([c A])
               (and (in (-> b c)
                        otherB)
                    (in (-> c a)
                        otherA))))
       (join otherB otherA)))

(test comprehensionsOnSigs 
      #:preds [ComprehensionsOnSigs]
      #:bounds [relations]
      #:expect theorem)
(test comprehensionsOnSets
      #:preds [ComprehensionsOnSets]
      #:bounds [relations]
      #:expect theorem)
(test multiComprehension
      #:preds [MultiComprehension]
      #:bounds [relations]
      #:expect theorem)