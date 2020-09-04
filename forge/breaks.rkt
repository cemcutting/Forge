#lang racket

(require "lang/bounds.rkt" (prefix-in @ "lang/ast.rkt"))
(require predicates)
(require "shared.rkt")

(provide constrain-bounds (rename-out [break-rel break]) break-bound break-formulas)
(provide constrain-formulas)
(provide (rename-out [add-instance instance]) clear-breaker-state)
(provide make-exact-sbound)
(provide sbound sbound-lower sbound-upper)
(provide cons!)

;;;;;;;;;;;;;;
;;;; util ;;;;
;;;;;;;;;;;;;;

(define-syntax-rule (cons! xs x) (set! xs (cons x xs)))
(define-syntax-rule (add1! x)    (begin (set! x  (add1 x)) x))

;;;;;;;;;;;;;;;;
;;;; breaks ;;;;
;;;;;;;;;;;;;;;;

(struct sbound (relation lower upper) #:transparent)
(define (make-sbound relation lower [upper false]) (sbound relation lower upper))
(define (make-exact-sbound relation s) (sbound relation s s))
(struct break (sbound formulas) #:transparent)
(define (make-break sbound [formulas (set)]) (break sbound formulas))

; sigs  :: set<sig>
; edges :: set<set<sig>>
(struct break-graph (sigs edges) #:transparent)

; pri               :: Nat
; break-graph       :: break-graph
; make-break        :: () -> break
; make-default      :: () -> break
(struct breaker (pri break-graph make-break make-default) #:transparent)

(define (bound->sbound bound) 
    (make-sbound (bound-relation bound)
                (list->set (bound-lower bound))
                (list->set (bound-upper bound))))
(define (sbound->bound sbound) 
    (make-bound (sbound-relation sbound)
                (set->list (sbound-lower sbound))
                (set->list (sbound-upper sbound))))
(define (bound->break bound) (break (bound->sbound bound) (set)))
(define break-lower    (compose sbound-lower    break-sbound))
(define break-upper    (compose sbound-upper    break-sbound))
(define break-relation (compose sbound-relation break-sbound))
(define break-bound    (compose sbound->bound   break-sbound))

(define (sbound+ . sbounds)
    (make-bound (break-relation (first sbounds)) ; TODO: assert all same relations
                (apply set-union     (map break-lower sbounds))
                (apply set-intersect (map break-lower sbounds)))
)
(define (break+ . breaks)
    (make-break (apply sbound+ breaks)
                (apply set-union (map break-formulas breaks)))
)

(define (make-exact-break relation contents [formulas (set)])
  (break (sbound relation contents contents) formulas))
(define (make-upper-break relation contents [formulas (set)])
  (break (sbound relation (set) contents) formulas))
(define (make-lower-break relation contents atom-lists [formulas (set)])
  (break (sbound relation contents (apply cartesian-product atom-lists)) formulas))

;;;;;;;;;;;;;;
;;;; data ;;;;
;;;;;;;;;;;;;;

; symbol |-> (pri rel bound atom-lists rel-list) -> breaker
(define strategies (make-hash))
; compos[{a₀,...,aᵢ}] = b => a₀+...+aᵢ = b
(define compos (make-hash))
; a ∈ upsets[b] => a > b
(define upsets (make-hash))
; a ∈ downsets[b] => a < b
(define downsets (make-hash))

; list of partial instance breakers
(define instances (list))
; a ∈ rel-breaks[r] => "user wants to break r with a"
(define rel-breaks (make-hash))
; rel-break-pri[r][a] = i => "breaking r with a has priority i"
(define rel-break-pri (make-hash))
; priority counter
(define pri_c 0)

; clear all state
(define (clear-breaker-state)
    (set! instances empty)
    (set! rel-breaks (make-hash))
    (set! rel-break-pri (make-hash))
    (set! pri_c 0)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; methods for defining breaks ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; h :: type(k) |-> set<type(v)>
(define (hash-add! h k v)
    (if (hash-has-key? h k)
        (set-add! (hash-ref h k) v)
        (hash-set! h k (mutable-set v))))

; h :: type(k1) |-> type(k2) |-> type(v)
(define (hash-add-set! h k1 k2 v)
    (unless (hash-has-key? h k1) (hash-set! h k1 (make-hash)))
    (define h_k1 (hash-ref h k1))
    (unless (hash-has-key? h_k1 k2) (hash-set! h_k1 k2 pri_c)))

; strategy :: () -> breaker
(define (add-strategy a strategy)
    (hash-set! strategies a strategy)
    (hash-add! upsets a a)      ;; a > a
    (hash-add! downsets a a))   ;; a < a
(define (equiv a . bs) 
    (hash-set! compos (apply set bs) a)
    (apply stricter a bs)
    ; TODO: if no fn defined for a, default to naively doing all bs
    #|(unless (hash-has-key? strategies a)
            (hash-set! strategies a (λ (rel atom-lists rel-list)
                (apply break+ (for ([b bs]) 
                    ((hash-ref strategies b) atom-lists)
                ))
            )))|#
)
(define (dominate a b)  
    (define upa (hash-ref upsets a))
    (define downb (hash-ref downsets b))
    (for ([x (in-set upa)])             ;; x > a
        (hash-add! upsets b x)          ;; x > b
        (hash-add! downsets x b)        ;; b < x
        (hash-set! compos (set b x) x)  ;; x = x + b
    )
    (for ([x (in-set downb)])           ;; x < b
        (hash-add! downsets a x)        ;; x < a
        (hash-add! upsets x a)          ;; a > x
        (hash-set! compos (set a x) a)  ;; a = a + x
    )
)
(define (stricter a . bs) (for ([b bs]) (dominate a b)))
(define (weaker a . bs) (for ([b bs]) (dominate b a)))

; TODO: allow syntax like (declare 'a 'b > 'c 'd > 'e 'f)
(define-syntax declare
  (syntax-rules (> < =)
    [(_ a > bs ...) (stricter a bs ...)]
    [(_ a < bs ...) (weaker a bs ...)]
    [(_ a = bs ...) (equiv a bs ...)]))


(define (min-breaks! breaks break-pris)
    (define changed false)
    (hash-for-each compos (λ (k v)
        (when (subset? k breaks)
              (set-subtract! breaks k)
              (set-add! breaks v)
              ; new break should have priority of highest priority component
              (define max-pri (apply min 
                (set-map k (lambda (s) (hash-ref break-pris s)))))
              (hash-set! break-pris v max-pri)
              (set! changed true))
    ))
    (when changed (min-breaks! breaks break-pris))
)

(define (break-rel rel . breaks) ; renamed-out to 'break for use in forge
    (for ([break breaks]) 
        (unless (hash-has-key? strategies break) (error "break not implemented:" break))
        (hash-add! rel-breaks rel break)
        (hash-add-set! rel-break-pri rel break (add1! pri_c))))
(define (add-instance i) (cons! instances i))

;; constrain bounds using only formula breaks
(define (constrain-formulas bounds-store relations-store)
    (when (>= (get-verbosity) VERBOSITY_HIGH)
        (println "DOING FORMULA BREAKS"))

    (define formulas (mutable-set))
    (for ([(rel breaks) (in-hash rel-breaks)])
        (define rel-list (hash-ref relations-store rel))
        (define atom-lists (map (λ (b) (hash-ref bounds-store b)) rel-list))
        (for ([sym (set->list breaks)]) 
            (define strategy (hash-ref strategies sym))
            (define breaker (strategy 0 rel bound atom-lists rel-list))
            (define default ((breaker-make-default breaker)))
            (set-union! formulas (break-formulas default))
        )
    )
    (set->list formulas)
)

(define (constrain-bounds total-bounds sigs bounds-store relations-store extensions-store) 
    (define name-to-rel (make-hash))
    (hash-for-each relations-store (λ (k v) (hash-set! name-to-rel (@node/expr/relation-name k) k)))
    (for ([s sigs]) (hash-set! name-to-rel (@node/expr/relation-name s) s))
    ; returns (values new-total-bounds (set->list formulas))
    (define new-total-bounds (list))
    (define formulas (mutable-set))
    ; unextended sets
    (set! sigs (list->mutable-set sigs))

    ; maintain non-transitive reachability relation 
    (define reachable (make-hash))
    (hash-set! reachable 'broken (mutable-set 'broken))
    (for ([sig sigs]) (hash-set! reachable sig (mutable-set sig)))

    (hash-for-each extensions-store (λ (k v) (set-remove! sigs v)))    

    ; First add all partial instances.
    (define instance-bounds (append* (for/list ([i instances]) 
        (if (sbound? i) (list i) (xml->breakers i name-to-rel)))))
    (define defined-relations (mutable-set))
    (for ([b instance-bounds])
        ;(printf "constraining bounds: ~v~n" b)
        (cons! new-total-bounds (sbound->bound b))
        (define rel (sbound-relation b))
        (set-add! defined-relations rel)
        (define typelist (@node/expr/relation-typelist rel))
        (for ([t typelist]) (when (hash-has-key? name-to-rel t)
            (set-remove! sigs (hash-ref name-to-rel t))))
    )

    ; proposed breakers from each relation
    (define candidates (list))
    (define cand->rel (make-hash))

    (for ([bound total-bounds])
        ; get declared breaks for the relation associated with this bound        
        (define rel (bound-relation bound))
        (define breaks (hash-ref rel-breaks rel (set)))
        (define break-pris (hash-ref rel-break-pri rel (make-hash)))
        ; compose breaks
        (min-breaks! breaks break-pris)

        (define defined (set-member? defined-relations rel))
        (cond [(set-empty? breaks)
            (unless defined (cons! new-total-bounds bound))
        ][else
            (define rel-list (hash-ref relations-store rel))
            (define atom-lists (map (λ (b) (hash-ref bounds-store b)) rel-list))

            ; make all breakers
            (define breakers (for/list ([sym (set->list breaks)]) 
                (define strategy (hash-ref strategies sym))
                (define pri (hash-ref break-pris sym))
                (strategy pri rel bound atom-lists rel-list)
            ))
            (set! breakers (sort breakers < #:key breaker-pri))

            ; propose highest pri breaker that breaks only leaf sigs
            ; break the rest the default way (with get-formulas)
            (define broken defined)
            (for ([breaker breakers])
                (cond [broken
                    (define default ((breaker-make-default breaker)))
                    (set-union! formulas (break-formulas default))
                ][else
                    (define break-graph (breaker-break-graph breaker))
                    (define broken-sigs (break-graph-sigs break-graph))
                    (cond [(subset? broken-sigs sigs)
                        (cons! candidates breaker)
                        (hash-set! cand->rel breaker rel)
                        (set! broken #t)
                    ][else
                        (define default ((breaker-make-default breaker)))
                        (set-union! formulas (break-formulas default))
                    ])
                ])
            )
            (unless (or broken defined) (cons! new-total-bounds bound))
        ])     
    )
    
    #|
        Now we try to use candidate breakers, starting with highest priority.

        We maintain a reachability relation. If applying a breaker would create a loop,
        the breaker isn't applied and the default formulas are used instead.
        Otherwise, we do the break and update the relation.

        The implementation may seem wrong but the relation is intentionally non-transitive.
        Consider: sig A { fs: B->C }, so that fs: A->B->C is a set of functions.
        Information can flow between B<~>C and A<~>C, but not A<~>B!
        This is important to get right because of our design principle of wrapping instances
            (fs in this case) inside solution sigs (A in this case)

        Paths between broken sigs can also break soundness.
        Broken sigs are given an edge to a unique 'broken "sig", so we only need to check for loops.
    |#

    (set! candidates (sort candidates < #:key breaker-pri))

    ;; build simplified edge-only break-graphs
    ;; cand->edges :: breaker |-> set<pair<sig>> (but actually undirected)
    (define cand->edges (make-hash))
    (for ([breaker candidates])
        (define break-graph (breaker-break-graph breaker))
        (define broken-sigs (break-graph-sigs break-graph))
        (define broken-edges (break-graph-edges break-graph))

        (define edges (mutable-set))
        ; reduce broken sigs to broken edges between those sigs and the auxiliary 'broken symbol
        ; TODO: replace 'broken with univ
        (for ([sig broken-sigs]) (set-add! edges (cons sig 'broken)))
        ; get all pairs from sets
        (for ([edge broken-edges])
            ; TODO: make functional
            (set! edge (set->list edge))
            (define L (length edge))
            (for* ([i (in-range 0 (- L 1))]
                   [j (in-range (+ i 1) L)])
                (set-add! edges (cons (list-ref edge i) (list-ref edge j)))
            )
        )

        (hash-set! cand->edges breaker edges)
    )

    ;; build the order of which witness functions must be constructed after which in the hypothetical isomorphism construction
    ;; before :: breaker |-> set<breaker>
    ;; B ∈ after[A] <=> A ∈ before[B] => "A must happen before B"
    (define before (for/hash ([c candidates]) (values c (mutable-set))))
    (define after  (for/hash ([c candidates]) (values c (mutable-set))))
    (for* ([breaker1 candidates] [breaker2 candidates] #:when (not (equal? breaker1 breaker2)))
        (define edges1 (hash-ref cand->edges breaker1))
        (define rel2 (hash-ref cand->rel breaker2))
        (define sigs2 (set-add (list->set (hash-ref relations-store rel2)) 'broken))

        ; breaker2 should be after breaker1 if breaker1 has an edge between 2 of breaker2's sigs
        (for* ([A sigs2] [B sigs2] #:when (not (equal? A B)))
            (when (set-member? edges1 (cons A B)) 
                (set-add! (hash-ref after  breaker1) breaker2)
                (set-add! (hash-ref before breaker2) breaker1)
            )
        )
    )

    (when (>= (get-verbosity) VERBOSITY_HIGH)
        (displayln "AFTER:")
        (for* ([(x ys) (in-hash after)] [y ys])
            (printf "  ~v >> ~v~n" (hash-ref cand->rel x) (hash-ref cand->rel y))
        )
        ;(displayln "BEFORE:")
        ;(for* ([(x ys) (in-hash before)] [y ys])
        ;    (printf "  ~v << ~v~n" (hash-ref cand->rel x) (hash-ref cand->rel y))
        ;)
    )

    ;; boundsy break subset of candidates s.t. restriction of `after` to them is acyclic (*after)
    ;; this guarantees that we can start somewhere and construct a full isomorphism

    (for ([c candidates])
        (set-add! (hash-ref before c) c)
        (set-add! (hash-ref after  c) c)
    )

    (define boundsy (mutable-set))
    (define *before (for/hash ([c candidates]) (values c (mutable-set))))
    (define *after  (for/hash ([c candidates]) (values c (mutable-set))))
    (for ([B candidates])
        (define As (hash-ref before B))
        (define Cs (hash-ref after  B))

        (define acceptable (for*/and ([A As] [C Cs])
            (not (set-member? (hash-ref *after C) A))
        ))

        (cond [acceptable
            ;; update boundsy, *before, and *after
            (set-add! boundsy B)

            (define newAs (set-copy As))
            (for ([A As]) (set-union! newAs (hash-ref *before A)))
            (set-intersect! newAs boundsy)
            (define newCs (set-copy Cs))
            (for ([C Cs]) (set-union! newCs (hash-ref *after C)))
            (set-intersect! newCs boundsy)

            (for ([A newAs]) (set-union! (hash-ref *after  A) newCs))
            (for ([C newCs]) (set-union! (hash-ref *before C) newAs))

            ; do boundsy break
            (define break ((breaker-make-break B)))
            (cons! new-total-bounds (break-bound break))
            (set-union! formulas (break-formulas break))

            (when (>= (get-verbosity) VERBOSITY_HIGH)
                (printf "BOUNDSY BROKE : ~v~n" (hash-ref cand->rel B))
            )
        ][else
            ; do default break
            (define default ((breaker-make-default B)))
            (cons! new-total-bounds (break-sbound default))
            (set-union! formulas (break-formulas default))

            (when (>= (get-verbosity) VERBOSITY_HIGH)
                (printf "DEFAULT BROKE : ~v~n" (hash-ref cand->rel B))
            )
        ])
        ;(when (>= (get-verbosity) VERBOSITY_HIGH)
        ;    (displayln "BOUNDSY:")
        ;    (for ([b boundsy])
        ;        (printf "  ~v~n" (hash-ref cand->rel b))
        ;    )
        ;    (displayln "*AFTER:")
        ;    (for* ([(x ys) (in-hash *after)] [y ys])
        ;        (printf "  ~v >>> ~v~n" (hash-ref cand->rel x) (hash-ref cand->rel y))
        ;    )
        ;    (displayln "*BEFORE:")
        ;    (for* ([(x ys) (in-hash *before)] [y ys])
        ;        (printf "  ~v <<< ~v~n" (hash-ref cand->rel x) (hash-ref cand->rel y))
        ;    )
        ;)
    )




    #|(for ([breaker candidates])
        (define break-graph (breaker-break-graph breaker))
        (define broken-sigs (break-graph-sigs break-graph))
        (define broken-edges (break-graph-edges break-graph))

        (define edges (list))
        ; reduce broken sigs to broken edges between those sigs and the auxiliary 'broken symbol
        ; TODO: replace 'broken with univ
        (for ([sig broken-sigs]) (cons! edges (cons sig 'broken)))
        ; get all pairs from sets
        (for ([edge broken-edges])
            ; TODO: make functional
            (set! edge (set->list edge))
            (define L (length edge))
            (for* ([i (in-range 0 (- L 1))]
                   [j (in-range (+ i 1) L)])
                (cons! edges (cons (list-ref edge i) (list-ref edge j)))
            )
        )
    
        ; acceptable :<-> doesn't create loops <-> no edges already exist
        (define acceptable (for/and ([edge edges])
            (define A (car edge))
            (define B (cdr edge))
            (not (set-member? (hash-ref reachable A) B))
        ))

        (cond [acceptable
            ; update reachability. do all edges in parallel
            (define new-reachable (make-hash))
            (for ([edge edges])
                (define A (car edge))
                (define B (cdr edge))
                (when (not (hash-has-key? new-reachable A)) 
                        (hash-set! new-reachable A (mutable-set)))
                (when (not (hash-has-key? new-reachable B)) 
                        (hash-set! new-reachable B (mutable-set)))
                (set-union! (hash-ref new-reachable A) (hash-ref reachable B))
                (set-union! (hash-ref new-reachable B) (hash-ref reachable A))
            )
            (hash-for-each new-reachable (λ (sig newset)
                ; set new sigs reachable from sig and vice versa
                (define oldset (hash-ref reachable sig))
                (set-subtract! newset oldset)
                (for ([sig2 newset])
                    (define oldset2 (hash-ref reachable sig2))
                    (set-add! oldset sig2)
                    (set-add! oldset2 sig)
                )
            ))

            ; do break
            (define break ((breaker-make-break breaker)))
            (when (>= (get-verbosity) VERBOSITY_HIGH)
                (define rel (hash-ref cand->rel breaker))
                (printf "BOUNDSY BROKE: ~a~n" rel)
            )
            (cons! new-total-bounds (break-bound break))
            (set-union! formulas (break-formulas break))
        ][else
            ; do default break
            (define default ((breaker-make-default breaker)))
            (cons! new-total-bounds (break-sbound default))
            (set-union! formulas (break-formulas default))
        ])
    )|#

    (values new-total-bounds (set->list formulas))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Strategy Combinators ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; turn a strategy on n-ary relations into one on arbitrary arity relations
; ex: (f:B->C) => (g:A->B->C) where f is declared 'foo
; we will declare with formulas that g[a] is 'foo for all a in A
; but we will only enforce this with bounds for a single a in A
(define (variadic n f)
    (λ (pri rel bound atom-lists rel-list)
        (cond [(= (length rel-list) n)
            (f pri rel bound atom-lists rel-list)
        ][else
            (define prefix (drop-right rel-list n))
            (define postfix (take-right rel-list n))
            (define prefix-lists (drop-right atom-lists n))
            (define postfix-lists (take-right atom-lists n))

            (define vars (for/list ([p prefix]) 
                (@node/expr/quantifier-var 1 (gensym "v"))
            ))
            (define new-rel (foldl @join rel vars))   ; rel[a][b]...
            (define sub-breaker (f pri new-rel bound postfix-lists postfix))
            
            (define sub-break-graph (breaker-break-graph sub-breaker))
            (define sigs (break-graph-sigs sub-break-graph))
            (define edges (break-graph-edges sub-break-graph))
            (define new-break-graph (break-graph
                sigs
                (set-union edges (for/set ([sig sigs] [p prefix]) (set sig p)))
            ))

            (breaker pri
                new-break-graph
                (λ ()
                    ; unpack results of sub-breaker
                    (define sub-break ((breaker-make-break sub-breaker)))
                    (define sub-sbound (break-sbound sub-break))
                    (define sub-lower (sbound-lower sub-sbound))
                    (define sub-upper (sbound-upper sub-sbound))

                    (cond [(set-empty? sigs)
                        ; no sigs are broken, so use sub-bounds for ALL instances
                        (define cart-pref (apply cartesian-product prefix-lists))
                        (define lower (for*/set ([c cart-pref] [l sub-lower]) (append c l)))
                        (define upper (for*/set ([c cart-pref] [u sub-upper]) (append c u)))
                        (define bound (sbound rel lower upper))

                        (define sub-formulas (break-formulas sub-break))
                        (define formulas (for/set ([f sub-formulas])
                            (@quantified-formula 'all (map cons vars prefix) f)
                        ))

                        (break bound formulas)
                    ][else
                        ; just use the sub-bounds for a single instance of prefix
                        (define cars (map car prefix-lists))
                        (define cdrs (map cdr prefix-lists))
                        (define lower (for/set ([l sub-lower]) (append cars l)))
                        (define upper (set-union
                            (for/set ([u sub-upper]) (append cars u))
                            (list->set (apply cartesian-product (append cdrs postfix-lists)))
                        ))
                        (define bound (sbound rel lower upper))

                        ; use default formulas unless single instance
                        (define sub-formulas (if (> (apply * (map length prefix-lists)) 1)
                            (break-formulas ((breaker-make-default sub-breaker)))
                            (break-formulas sub-break)
                        ))
                        ; wrap each formula in foralls for each prefix rel
                        (define formulas (for/set ([f sub-formulas])
                            (@quantified-formula 'all (map cons vars prefix) f)
                        ))

                        (break bound formulas)
                    ])
                )
                (λ ()
                    (define sub-break ((breaker-make-default sub-breaker)));
                    (define sub-formulas (break-formulas sub-break))
                    (define formulas (for/set ([f sub-formulas])
                        (@quantified-formula 'all (map cons vars prefix) f)
                    ))
                    (break bound formulas)
                )
            )
        ])
    )
)

(define (co f)
    (λ (pri rel bound atom-lists rel-list)
        (define sub-breaker (f pri (@~ rel) bound (reverse atom-lists) (reverse rel-list)))
        (breaker pri
            (breaker-break-graph sub-breaker)
            (λ () 
                ; unpack results of sub-breaker
                (define sub-break ((breaker-make-break sub-breaker)))
                (define sub-formulas (break-formulas sub-break))
                (define sub-sbound (break-sbound sub-break))
                (define sub-lower (sbound-lower sub-sbound))
                (define sub-upper (sbound-upper sub-sbound))
                ; reverse all tuples in sbounds 
                (define lower (for/set ([l sub-lower]) (reverse l)))
                (define upper (for/set ([l sub-upper]) (reverse l)))
                (define bound (sbound rel lower upper))

                (break bound sub-formulas)
            )
            (λ ()
                ((breaker-make-default sub-breaker))
            )
        )
    )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; define breaks and compositions ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A->A Strategies ;;;
(add-strategy 'irref (λ (pri rel bound atom-lists rel-list) 
    (define atoms (first atom-lists))
    (define sig (first rel-list))
    (breaker pri
        (break-graph (set) (set))
        (λ () 
            (make-upper-break rel
                            (filter-not (lambda (x) (equal? (first x) (second x)))
                                        (apply cartesian-product atom-lists))))
        (λ () (break bound (set
            (@no (@& @iden rel))
        )))
    )
))
(add-strategy 'ref (λ (pri rel bound atom-lists rel-list) 
    (define atoms (first atom-lists))
    (define sig (first rel-list))
    (breaker pri
        (break-graph (set) (set))
        (λ () 
            (make-lower-break rel
                            (filter     (lambda (x) (equal? (first x) (second x)))
                                        (apply cartesian-product atom-lists))
                            atom-lists))
        (λ () (break bound (set
            (@all ([x sig])
                (@in x (@join x rel))
            )
        )))
    )
))
(add-strategy 'linear (λ (pri rel bound atom-lists rel-list) 
    (define atoms (first atom-lists))
    (define sig (first rel-list))
    (breaker pri
        (break-graph (set sig) (set))
        (λ () (make-exact-break rel (map list (drop-right atoms 1) (cdr atoms))))
        (λ () (break bound (set
            (@some ([init sig]) (@and
                (@no (@join rel init))
                (@all ([x (@- sig init)]) (@one (@join rel x)))
                (@= (@join init (@* rel)) sig)
            ))
            (@some ([term sig]) (@and
                (@no (@join term rel))
                (@all ([x (@- sig term)]) (@one (@join x rel)))
                (@= (@join (@* rel) term) sig)
            ))
        )))
    )
))
(add-strategy 'acyclic (λ (pri rel bound atom-lists rel-list) 
    (define atoms (first atom-lists))
    (define sig (first rel-list))
    (breaker pri
        (break-graph (set) (set))
        (λ ()
            (make-upper-break rel
                            (for*/list ([i (length atoms)]
                                        [j (length atoms)]
                                        #:when (< i j))
                                    (list (list-ref atoms i) (list-ref atoms j)))))
        (λ () (break bound (set
            (@no ([x sig])
                (@in x (@join x (@^ rel)))
            )
        )))
    )
))
(add-strategy 'tree (λ (pri rel bound atom-lists rel-list) 
    (define atoms (first atom-lists))
    (define sig (first rel-list))
    (breaker pri
        (break-graph (set) (set))
        (λ ()
            (make-break 
                (bound->sbound (make-upper-bound rel
                            (for*/list ([i (length atoms)]
                                        [j (length atoms)]
                                        #:when (< i j))
                                    (list (list-ref atoms i) (list-ref atoms j)))))
                (set
                    (@some ([n sig]) (@and
                        (@= (@join n (@^ rel)) (@- sig n))
                        (@all ([m (@- sig n)]) 
                            (@one (@join rel m))
                        )
                    ))
                )))
        (λ () (break bound (set
            (@some ([n sig]) (@and
                ;@no (@join rel n))
                (@= (@join n (@^ rel)) (@- sig n))  ; n.^rel = sig-n
                (@all ([m (@- sig n)]) 
                    (@one (@join rel m))    ; one rel.m
                )
            ))
        )))
    )
))
(add-strategy 'plinear (λ (pri rel bound atom-lists rel-list) 
    (define atoms (first atom-lists))
    (define sig (first rel-list))
    (breaker pri
        (break-graph (set sig) (set))
        (λ () (break
            (sbound rel 
                (set) ;(set (take atoms 2))
                (map list (drop-right atoms 1) (cdr atoms))
            )
            (set
                (@lone ([init sig]) (@and
                    (@no (@join rel init))
                    (@some (@join init rel))
                ))
            )
        ))
        (λ () (break bound (set
            (@lone (@- (@join rel sig) (@join sig rel)))    ; lone init
            (@lone (@- (@join sig rel) (@join rel sig)))    ; lone term
            (@no (@& @iden (@^ rel)))   ; acyclic
            (@all ([x sig]) (@and       ; all x have
                (@lone (@join x rel))   ; lone successor
                (@lone (@join rel x))   ; lone predecessor
            ))
        )))
    )
))

;;; A->B Strategies ;;;
(add-strategy 'func (λ (pri rel bound atom-lists rel-list) 
    (define A (first rel-list))
    (define B (second rel-list))
    (define As (first atom-lists))
    (define Bs (second atom-lists))  
    (define formulas (set 
        (@all ([a A]) (@one (@join a rel)))    ; @one
    ))
    (if (equal? A B)
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set A) (set))
            (λ () (break ;(bound->sbound bound) formulas))
                (sbound rel
                    (set)
                    ;(for*/set ([a (length As)]
                    ;           [b (length Bs)] #:when (<= b (+ a 1)))
                    ;    (list (list-ref As a) (list-ref Bs b))))
                    (set-add (cartesian-product (cdr As) Bs) (list (car As) (car Bs))))
                formulas))
            (λ () (break bound formulas))
        )
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set B) (set (set A B)))   ; breaks B and {A,B}
            (λ () 
                ; assume wlog f(a) = b for some a in A, b in B
                (break 
                    (sbound rel
                        (set (list (car As) (car Bs)))
                        (set-add (cartesian-product (cdr As) Bs) (list (car As) (car Bs))))
                    formulas))
            (λ () (break bound formulas))
        )
    )
))
(add-strategy 'surj (λ (pri rel bound atom-lists rel-list) 
    (define A (first rel-list))
    (define B (second rel-list))
    (define As (first atom-lists))
    (define Bs (second atom-lists))  
    (define formulas (set 
        (@all ([a A]) (@one  (@join a rel)))    ; @one
        (@all ([b B]) (@some (@join rel b)))    ; @some
    ))
    (if (equal? A B)
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set) (set))
            (λ () (break (bound->sbound bound) formulas))
            (λ () (break bound formulas))
        )
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set) (set (set A B)))   ; breaks only {A,B}
            (λ () 
                ; assume wlog f(a) = b for some a in A, b in B
                (break 
                    (sbound rel
                        (set (list (car As) (car Bs)))
                        (set-add (cartesian-product (cdr As) Bs) (list (car As) (car Bs))))
                    formulas))
            (λ () (break bound formulas))
        )
    )
))
(add-strategy 'inj (λ (pri rel bound atom-lists rel-list) 
    (define A (first rel-list))
    (define B (second rel-list))
    (define As (first atom-lists))
    (define Bs (second atom-lists))  
    (define formulas (set 
        (@all ([a A]) (@one  (@join a rel)))    ; @one
        (@all ([b B]) (@lone (@join rel b)))    ; @lone
    ))
    (if (equal? A B)
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set) (set))
            (λ () (break (bound->sbound bound) formulas))
            (λ () (break bound formulas))
        )
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set B) (set (set A B)))   ; breaks B and {A,B}
            (λ () 
                ; assume wlog f(a) = b for some a in A, b in B
                (break 
                    (sbound rel
                        (set (list (car As) (car Bs)))
                        (set-add (cartesian-product (cdr As) (cdr Bs)) (list (car As) (car Bs))))
                    formulas))
            (λ () (break bound formulas))
        )
    )
))
(add-strategy 'bij (λ (pri rel bound atom-lists rel-list) 
    (define A (first rel-list))
    (define B (second rel-list))
    (define As (first atom-lists))
    (define Bs (second atom-lists))  
    (define formulas (set 
        (@all ([a A]) (@one  (@join a rel)))    ; @one
        (@all ([b B]) (@one  (@join rel b)))    ; @one
    ))
    (if (equal? A B)
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set) (set))
            (λ () (break (bound->sbound bound) formulas))
            (λ () (break bound formulas))
        )
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set) (set (set A B)))   ; breaks only {A,B}
            (λ () (make-exact-break rel (map list As Bs)))
            (λ () (break bound formulas))
        )
    )
))
(add-strategy 'pbij (λ (pri rel bound atom-lists rel-list) 
    (define A (first rel-list))
    (define B (second rel-list))
    (define As (first atom-lists))
    (define Bs (second atom-lists))  
    (define LA (length As))
    (define LB (length Bs))
    (define broken (cond [(> LA LB) (set A)]
                         [(< LA LB) (set B)]
                         [else (set)]))
    ;(printf "broken : ~v~n" broken)
    (define formulas (set 
        (@all ([a A]) (@one  (@join a rel)))    ; @one
        (@all ([b B]) (@one  (@join rel b)))    ; @one
    ))
    (if (equal? A B)
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph (set) (set))
            (λ () (break (bound->sbound bound) formulas))
            (λ () (break bound formulas))
        )
        (breaker pri ; TODO: can improve, but need better symmetry-breaking predicates
            (break-graph broken (set (set A B)))   ; breaks only {A,B}
            (λ () (make-upper-break rel (for/list ([a As][b Bs]) (list a b)) formulas))
            (λ () (break bound formulas))
        )
    )
))

; use to prevent breaks
(add-strategy 'default (λ (pri rel bound atom-lists rel-list) (breaker pri
    (break-graph (set) (set))
    (λ () 
        (make-upper-break rel (apply cartesian-product atom-lists)))
    (λ () (break bound (set)))
)))



(add-strategy 'cotree (variadic 2 (co (hash-ref strategies 'tree))))
(add-strategy 'cofunc (variadic 2 (co (hash-ref strategies 'func))))
(add-strategy 'cosurj (variadic 2 (co (hash-ref strategies 'surj))))
(add-strategy 'coinj (variadic 2 (co (hash-ref strategies 'inj))))

(add-strategy 'irref (variadic 2 (hash-ref strategies 'irref)))
(add-strategy 'ref (variadic 2 (hash-ref strategies 'ref)))
(add-strategy 'linear (variadic 2 (hash-ref strategies 'linear)))
(add-strategy 'plinear (variadic 2 (hash-ref strategies 'plinear)))
(add-strategy 'acyclic (variadic 2 (hash-ref strategies 'acyclic)))
(add-strategy 'tree (variadic 2 (hash-ref strategies 'tree)))
(add-strategy 'func (variadic 2 (hash-ref strategies 'func)))
(add-strategy 'surj (variadic 2 (hash-ref strategies 'surj)))
(add-strategy 'inj (variadic 2 (hash-ref strategies 'inj)))
(add-strategy 'bij (variadic 2 (hash-ref strategies 'bij)))
(add-strategy 'pbij (variadic 2 (hash-ref strategies 'pbij)))


;;; Domination Order ;;;
(declare 'linear > 'tree)
(declare 'tree > 'acyclic)
(declare 'acyclic > 'irref)
(declare 'func < 'surj 'inj)
(declare 'bij = 'surj 'inj)
(declare 'linear = 'tree 'cotree)
(declare 'bij = 'func 'cofunc)
(declare 'cofunc < 'cosurj 'coinj)
(declare 'bij = 'cosurj 'coinj)

(provide get-co)
(define co-map (make-hash))
(hash-set! co-map 'tree 'cotree)
(hash-set! co-map 'func 'cofunc)
(hash-set! co-map 'surj 'cosurj)
(hash-set! co-map 'inj 'coinj)
(hash-set! co-map 'tree 'cotree)
(for ([(k v) (in-hash co-map)]) (hash-set! co-map v k))
(for ([sym '('bij 'pbij 'linear 'plinear 'ref 'irref 'acyclic)]) (hash-set! co-map sym sym))
(define (get-co sym) (hash-ref co-map sym))



#|
ADDING BREAKS
- add breaks here with using add-strategy and the declare forms:
    - (declare a > bs ...)
    - (declare a < bs ...)
    - (declare a = bs ...)
- note that your break can likely compose with either 'ref or 'irref because they don't break syms
    - so don't forget to declare that
- declarations will be inferred automatically when possible:
    - a > b        |- a = a + b
    - a > b, b > c |- a > c
- note, however:
    - a = a + b   !|- a > b   

TODO:
- prove correctness
- add extra formulas to further break symmetries because kodkod can't once we've broken bounds
    - improve all functional strategies (see func A->A case for commented working example)
- allow strategies to be passed multiple values, return values, split sigs
- strategy combinators
    - naive equiv strategies
        - can be used to combine many strats with ref/irref, even variadic ones
        - use in equiv if sum isn't defined
- more strats
    - lasso
    - loop
    - loops
    - unique init/term
    - unique init/term + acyclic
    - has init/term
    - more partial breaks
|#


(require (except-in xml attribute))
(define (xml->breakers xml name-to-rel)
    (set! xml (xml->xexpr (document-element (read-xml (open-input-string xml)))))
    (define (read-label info)
        (define label #f)
        (define builtin #f)
        (for/list ([i info]) (match i
            [(list 'label l) (set! label l)]
            [(list 'builtin "yes") (set! builtin #t)]
            [else #f]
        ))
        (if builtin #f (hash-ref name-to-rel label))
    )
    (define (read-atoms atoms) 
        (filter identity (for/list ([a atoms]) (match a
            [(list atom (list (list 'label l))) (string->symbol l)]
            [else #f]
        )))
    )
    (define (read-tuples tuples)
        (list->set (filter identity (for/list ([t tuples]) (match t
            [(list 'tuple atoms ...) (read-atoms atoms)]
            [else #f]
        ))))
    )
    (define (read-rel x) (match x
        [(list 'sig info atoms ...) 
            (define sig (read-label info))
            (if sig (make-exact-sbound sig (map list (read-atoms atoms))) #f)]
        [(list 'field info tuples ...) (make-exact-sbound (read-label info) (read-tuples tuples))]
        [else #f]
    ))

    (when (equal? (first xml) 'alloy) (for ([x xml]) (match x
        [(list 'instance _ ...) (set! xml x)]
        [else #f]
    )))
    (match xml
        [(list 'instance _ ...)  (filter identity (for/list ([x xml]) (read-rel x)))]
        [else (list (read-rel xml))]
    )
)