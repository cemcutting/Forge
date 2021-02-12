#lang racket ;forge/core

;(set-verbosity 1)

(require forge/amalgam/desugar/desugar)
(require forge/amalgam/lift-bounds/lift-bounds)
(require forge/send-to-kodkod)

;(require "amalgam/tests/forge_ex.rkt")
;(require "amalgam/userStudies/KittyBacon.rkt")
(require racket/hash)
(require (prefix-in @ racket/set))
(require (prefix-in @ (only-in racket -> >= >)))

(require (only-in "amalgam/desugar/desugar_helpers.rkt" tup2Expr))
(require forge/sigs-structs
         forge/lang/ast
         forge/evaluator
         (only-in forge/breaks sbound))
(require forge/shared)
(require pretty-format)

; TODO: Comment this out later 
;(run udt
;     #:preds[isUndirectedTree]
;     #:scope[(Node 4)])

;(run KB
;     #:preds[KittyBaconIsAFancyFeline]
;     #:scope[(Cat 4)])

; Entry point for Amalgam from forge/core
;  This is a sketch for the moment

(provide build-provenances
         get-locally-necessary-list)

(struct provenanceNode (annotations) #:transparent)
(struct contraLeaf provenanceNode (fmla) #:transparent)
(struct alphaLeaf provenanceNode (alpha) #:transparent)
(struct desugarStep provenanceNode (provNode) #:transparent)
(struct ANDProof provenanceNode (provTrees) #:transparent)
(struct ORProof provenanceNode (alphas obligations) #:transparent)


(define (build-alternate-run orig-run F scope bounds)
  ; We have the orig-run without using the run macro
  ; which means we have its Run-spec
  ; which is post-processing by the run macro
  (define modified-run-spec (struct-copy Run-spec (Run-run-spec orig-run) [scope scope] [bounds bounds]))
  (define-values (run-result atoms server-ports kodkod-currents kodkod-bounds) (send-to-kodkod modified-run-spec))        
  (Run (Run-name orig-run) (Run-command orig-run) modified-run-spec run-result server-ports atoms kodkod-currents kodkod-bounds))

; takes a hash-table representation of an instance and a tuple and flips the truth of
;  that tuple in the instance. The tuple is <t> in <raw-r>.
(define (flip-tuple a-hash t raw-r)
  (define r (cond [(string? raw-r) (string->symbol raw-r)]
                  [(symbol? raw-r) raw-r]
                  [else (error (format "amalgam: unexpected type for relation name: ~a" raw-r))]))
  (unless (hash-has-key? a-hash r)
    (error (format "amalgam: failed to find ~a in ~a" r (hash-keys a-hash))))
  (if (member t (hash-ref a-hash r))
      ; update functionally, return immutable map
      (hash-set a-hash r (remove t (hash-ref a-hash r)))
      (hash-set a-hash r (cons t (hash-ref a-hash r)))))

; input:
;        A - a set of sets
;        B - a set of sets
;
; output: the union product of A and B which is defined as:
;         {a_i ∪ b_j |1 ≤ i ≤ n, 1 ≤ j ≤ m}
;            where n and m are the sizes of A and B respectively
; build set cartesian product of A and B
; map over the cartesian product of A and B a lambda that takes the union
; of these two things.
; 
;(define/contract (union-product A B)
;  (@-> set? set? set?)  
;  (foldl set-union (@set) (set->list (for/set ([i A]) (for/set ([j B]) (list i j))))))
;
;(define/contract (new-union-product A B)
;  (@-> set? set? set?)
;  (foldl set-union (@set)
;         (set->list 
;          (for/set ([i A])
;            (foldl set-union (@set)
;                   (set->list 
;                    (for/set ([k B])
;                      (foldl set-union (@set)
;                             (set->list 
;                              (for/set ([j i])
;                                (for/set ([h k])
;                                  (list j h))))))))))))

(define/contract (isLiteralIn fmla)
  (@-> node/formula? boolean?)

  (define args (node/formula/op-children fmla))
  (define LHS (first args))
  (define RHS (second args))

  ; Check if LHS is just a simple tuple 
  (define evalLHS
    (cond
      [(node/expr/op/->? LHS)
       (define children (node/expr/op-children LHS))
       ((listof node/expr/atom?) children)]
      [(node/expr/atom? LHS) #t]))

  ; Check if RHS is either a relation name, atom, the int constant, or other
  ; expression constants
  (define evalRHS
    (or
     (node/expr/relation? RHS)
     (node/expr/atom? RHS)
     (node/expr/constant? RHS)
     (node/expr/constant? RHS)))
  (and evalLHS evalRHS))

; L is the target of the provenance query
; fmla is the current target of blame
(define/contract (amalgam-descent fmla orig-run alt-run L currSign)
  (@-> node/formula? Run? Run? pair? boolean? (or/c provenanceNode? exn:fail?))

  ; Invariant: instance from orig-run satisfies fmla
  ;            instance from alt-run does not satisfy fmla
  ; For debugging purposes, fail noisily if this invariant is violated
  (unless (or (and currSign (evaluate orig-run 'unused fmla))
              (and (not currSign) (not (evaluate orig-run 'unused fmla))))
    (error (pretty-format "amalgam-descent (sign=~a): original instance failed to satisfy ~a~n" currSign fmla)))
  (when (or (and currSign (evaluate alt-run 'unused fmla))
            (and (not currSign) (not (evaluate alt-run 'unused fmla))))
    (error (pretty-format "amalgam-descent (sign=~a): L-alternate (L=~a) instance satisfied ~a~n" currSign L fmla)))  

  (define (handleAND info args)
    ; *every* arg must have satisfied the orig instance
    ; but not every arg necessarily fails in L-alt instance
    ; each failed arg is its own new provenance-set, which we union together
    (define failed-args (filter
                         (lambda (arg)
                           (if currSign
                               (not (evaluate alt-run 'unused arg))     ; real "and"
                               (evaluate alt-run 'unused arg))) args))  ; negated "or"

    ; Each call to amalgam-descent is returning a version of the provenanceNode.
    ; In this case, we are getting the provenances for all of the arguments that
    ; failed to evaluate to #t. 
    (define prov-trees (map
                       (lambda (arg)
                         (amalgam-descent arg orig-run alt-run L currSign)) failed-args))

    (if (equal? (length prov-trees) 1)
        (first prov-trees)
        (ANDProof 'andProof prov-trees)))
  
  (define (handleOR info args)
    ; orig instance satisfies at least one arg (not necessarily all, but not zero)
    ; L-alt instance satisfies no args
    (define-values (orig-true-args orig-false-args) ; filter but return #f args as 2nd value
      (partition
       (lambda (arg)
         (if currSign 
             (evaluate orig-run 'unused arg)
             (not (evaluate orig-run 'unused arg)))) args))

    ; This is a big OR, so we can think of it as an implication.
    ;  furthermore, we're free to shuffle args to the left or right of the => as we see fit
    ; So specialize to the original instance: NOT OR[orig-false-args] ==> OR[orig-true-args]
    (define prov-sets
      (map (lambda (arg)
             (amalgam-descent arg orig-run alt-run L currSign)) orig-true-args))

    ; we only negate if currSign is true, if false, we don't negate 
    (define alphas
      (map (lambda (arg)
             (alphaLeaf 'alphaLeaf
                        (if currSign
                            (!/info info (list arg))
                            arg))) orig-false-args))

    (ORProof 'orProof alphas prov-sets))
    ;;;;;;;; Older comments 
    ; We need *ALL* of orig-true-args to fail, and may have multiple justifications for each (union product)
    ; TODO: Remove the call to union-product since that isn't what we're doing anymore 
    ;(define failure-reasons (list (foldl (lambda (x acc) (new-union-product x acc)) (first prov-sets) (rest prov-sets))))
    ; add prov-sets to each failure-reasons + return 
    ;(list->set (map (lambda (reason) (set-union new-alpha-set reason)) failure-reasons)))
  
  (match fmla
    ; base case: AND 
    [(node/formula/op/&& info args)
     (if currSign (handleAND info args) (handleOR info args))]

    ; base case: OR 
    [(node/formula/op/|| info args)
     (if currSign (handleOR info args) (handleAND info args))]

    ; base case: positive literal
    [(node/formula/op/in info args)
     ; Check that the formula is the simplest case of IN, or take it to desugar
     #:when (isLiteralIn fmla)
     ; TODO: How can I check if we got to a contradiction? -- we can trust this
     ; based on the invariant 
      (cond
        [currSign (contraLeaf 'contraLeafCurrSignTrue fmla)]
        [else (contraLeaf 'contraLeafCurrSignFalse (not fmla))])]

    ; base case: negation
    [(node/formula/op/! info args)     
     (amalgam-descent (first args) orig-run alt-run L (not currSign))]

    [else
     (define desugarPair (desugarFormula fmla '() orig-run))
     (define desugarProvNode (amalgam-descent (first desugarPair) orig-run alt-run L currSign))
     (desugarStep (second desugarPair) desugarProvNode)]))

; pair<list<atom>, string>, Run -> Boolean
; caller of this helper is get-locally-nescessary-list
; used to generate list of locally necessary literals
(define (is-locally-necessary tup orig-run)
  (define spec (Run-run-spec orig-run))
  (define Fs (Run-spec-preds spec))

  ; and together all of your predicates to get our formula F
  (define F (foldl (lambda (f acc) (and f acc)) (first Fs) (rest Fs)))
  (when (equal? (car tup) '(NetworkUser1 NetworkUser0))
      (printf "*** LN : F=~a~n" F))
  
  (define state (Run-spec-state spec))
  (define orig-scope (Run-spec-scope spec))
  (define orig-bounds (Run-spec-bounds spec))
  (define sigs (State-sigs state))

  ; relations
  (define relations (State-relations state))

  (define orig-inst (stream-first (Run-result orig-run)))
  (unless (Sat? orig-inst)
    (error "amalgam called on unsat run"))

  (define new-totals (flip-tuple (first (Sat-instances orig-inst))
                                 (car tup) (cdr tup)))
  ; no. "total bindings" is a misnomer. instead need to provide sbounds in pbindings
  ; e.g. (for fixed edge relation)

  (define (make-exact-sbound rel tups)
    (sbound rel (list->set tups) (list->set tups)))
  
  ; For reasons passing understanding, get-relation returns a symbol...
  (define (get-actual-relation relname)
    (cond [(hash-has-key? sigs relname) (Sig-rel (hash-ref sigs relname))]
          [(hash-has-key? relations relname) (Relation-rel
                                              (hash-ref relations relname))]
          [else (error "unknown relation or sig" relname)]))
 
  (define new-pbindings
    (for/hash ([k (hash-keys new-totals)]);(hash-keys orig-bounds)])
      (values (get-actual-relation k)
              (make-exact-sbound (get-actual-relation k)
                                 (hash-ref new-totals k)))))
  
  (define bounds (Bound new-pbindings
                              (Bound-tbindings orig-bounds)))
  
  ; can't use inst syntax here, so construct manually
;  (define alt-inst
;    (lambda (s b) (values scope bounds)))

  ; Get the solver to produce the L-alternate for us
  ; Preserve scope and t-bounds from original run
  (define alt-run (build-alternate-run orig-run F orig-scope bounds))
  ;(run alt-run
  ;     #:preds [F]
  ;     #:bounds alt-inst)
  ; evaluate to see if tup is locally necessary
  ;(define result (not (evaluate alt-run 'unused F)))
  ;result
  (let ([result (not (is-sat? alt-run))]) 
    (close-run alt-run)
    result))


; Run -> pair of two lists, first list evaluates to true
;        second list evaluates to false
; Due to the way the evaluator works at the moment, this is always
; with respect to the current solver state for <a-run>.
(define (get-locally-necessary-list orig-run)
  (define spec (Run-run-spec orig-run))
  (define state (Run-spec-state spec))

  ;; Which atoms were actually used?
  ;; ASSUMPTION: we're only checking fields, not sig relations
  ;;   if those have to vary, this technique is too coarse
  (define evaluated-univ (evaluate orig-run 'unused univ))
  
  ; list of relations
  (define relations (hash-values (State-relations state)))

  (define un-partitioned-list (apply append (for/list ([r relations])
    (define name (Relation-name r))
                                                             
    ; we do not want to include succ or Int
    (if (or (equal? name 'succ) (equal? name 'Int))
        '()
        (let ()
          ;; these are the orig bounds (not exact)
          ;;   but when we get to building the new bounds in is-locally-necessary
          ;;   those sigs are fixed, so the extras dont exist          
          (define upper-bounds (liftBoundsExpr (Relation-rel r) '()
                                               orig-run))          
          (define curr
            (filter-map (lambda (tuple)
                          (when (@> (get-verbosity) VERBOSITY_LOW)
                            (printf "LN: considering tuple: ~a in ~a~n" tuple name))      
                          (define present
                            (andmap (lambda (atomsym) (member (list atomsym) evaluated-univ)) tuple))
                          (when (and (not present) (@> (get-verbosity) VERBOSITY_LOW))
                            (printf "LN:   disregarding tuple as some atom wasn't present in the instance's univ~n"))
                          (if (and present (is-locally-necessary (cons tuple name) orig-run))
                              (cons tuple (Relation-rel r))
                              #f))
                        upper-bounds))
          curr)))))
 
  ; partition the list
  (define-values (yes no) (partition (lambda (pair)
               
               (define formula
                 (in/info empty-nodeinfo (list (tup2Expr (car pair) orig-run empty-nodeinfo)
                     (cdr pair))))  
               (evaluate orig-run 'unused formula)) un-partitioned-list))
  (cons yes no))


;  getting rid of tuples involving unused atoms
;(define (remove-unused locally-necessary-list orig-run)
;  ; list of things in univ
;  (define evaluated-univ (evaluate orig-run 'unused univ))
;  (filter
;   ; we want to keep a pair if the nodes are used
;   (lambda (tup)
;     (define pair (car tup))
;     (andmap (lambda (elem) (member (list elem) evaluated-univ)) pair))
;   locally-necessary-list))


; pair<list<atom>, string>, boolean, Run -> provenance-set
; Due to the way the evaluator works at the moment, this is always
; with respect to the current solver state for <a-run>.
(define (build-provenances tup orig-run)
  ; get conjunction of predicates F from the run command
  (define spec (Run-run-spec orig-run))
  (define Fs (Run-spec-preds spec))
  (define F (foldl (lambda (f acc) (and f acc)) (first Fs) (rest Fs)))
  
  (define state (Run-spec-state spec))
  (define orig-scope (Run-spec-scope spec))
  (define orig-bounds (Run-spec-bounds spec))
  (define sigs (State-sigs state))
  (define relations (State-relations state))
  
  ; TODO This may only work if the solver state is the *first* instance in the stream
  ;   Confirm + discuss: what's the method by which the generator moves forward?
  (define orig-inst (stream-first (Run-result orig-run)))
  (unless (Sat? orig-inst)
    (error "amalgam called on unsat run"))
  ;(printf "~n  orig-inst: ~a~n" orig-inst)
  ;(printf "~n  orig-bounds: ~a~n" (Run-spec-bounds spec))
  ;(printf "~n  orig-scope: ~a~n" orig-scope) 
  (define new-totals (flip-tuple (first (Sat-instances orig-inst)) (car tup) (cdr tup)))
  ; no. "total bindings" is a misnomer. instead need to provide sbounds in pbindings
  ; e.g. (for fixed edge relation)
  ;Original PBindings: 
  ; #hash(((relation 2 "edges" (Node Node) Node) .
  ;   #(struct:sbound (relation 2 "edges" (Node Node) Node)
  ;   #<set: (Node0 Node1)> #<set: (Node0 Node1)>))
  ;    ...
  ;(define bounds (Bound (hash) new-totals))
  ;(define all-rels (hash-union sigs relations))
  
  (define (make-exact-sbound rel tups)
    (sbound rel (list->set tups) (list->set tups)))
  
  ; For reasons passing understanding, get-relation returns a symbol...
  (define (get-actual-relation relname)
    (cond [(hash-has-key? sigs relname) (Sig-rel (hash-ref sigs relname))]
          [(hash-has-key? relations relname) (Relation-rel (hash-ref relations relname))]
          [else (error "unknown relation or sig" relname)]))
 
  (define new-pbindings
    (for/hash ([k (hash-keys new-totals)]);(hash-keys orig-bounds)])
      (values (get-actual-relation k)
              (make-exact-sbound (get-actual-relation k)
                                 (hash-ref new-totals k)))))
  (define bounds (Bound new-pbindings (Bound-tbindings orig-bounds)))
  (define scope (Scope #f #f (hash))) ; empty
  ; can't use inst syntax here, so construct manually
  (define alt-inst
    (lambda (s b) (values scope bounds)))
  
  ;(printf "~n~n  new-pbindings: ~a~n" new-pbindings)  
  
  (define alt-run (build-alternate-run orig-run true scope bounds))
  ; Get the solver to produce the L-alternate for us
  ;(run alt-run
  ;     #:preds []
  ;     #:bounds alt-inst)
  ;(printf "~n  first alt instance: ~a~n" (stream-first (Run-result alt-run)))
  ;(printf "~n  ALT BOUNDS: ~a~n" (Run-spec-bounds (Run-run-spec alt-run)))
  ; evaluate to make sure tup is locally necessary  
  (define check-alt (evaluate alt-run 'unused F))
  ;(printf "~n  check-alt: ~a~n" check-alt)

  ; desugar F
  ; Pass in the run, not the bounds, since we may need more of the run (like atom-rels)
  ; Don't desugar first; desugar as needed in the amalgam descent
  ;(define desugared (desugarFormula F '() orig-run #t))
  
  ; do amalgam descent on desugared F
  (amalgam-descent F orig-run alt-run tup #t))


; E.g., at REPL (or in separate module that requires the forge module)
; > (require racket/stream racket/base forge/amalgam)
; > (build-provenances (cons '(Node3 Node1) "edges") #f udt)

; This will produce an error if Node1 isn't in all-atoms
;   TODO
;(build-provenances (cons '(Node1 Node1) "edges") udt)

; these are OK assuming 3, 4, 5, 6 are used
; add

; TODO: uncomment this later 
;(define test_N1N1_edges (build-provenances (cons '(Node1 Node1) "edges") udt))

;(stream-first (Run-result KB))
;(define test_local_necessity_udt (get-locally-necessary-list udt))

;(define test_local_necessity_kittyBacon (get-locally-necessary-list KB))
;(printf "LOCAL NECESSITY TEST --- ~a --- " test_local_necessity_kittyBacon)
;(build-provenances (cons '(Node4 Node5) "edges") udt) ; remove

;(desugarFormula (in (-> (atom 'Node0) (atom 'Node1)) (& iden edges)) '() udt #f)



(define (count-provenances ptree)
  (match ptree
    ; A contradiction is itself a proof
    [(contraLeaf anns f) 1]
    ; Desugaring doesn't add proofs, just enables them
    [(desugarStep anns tree) (count-provenances tree)]
    ; Each child of an AND branch provides proofs that suffice on their own
    [(ANDProof anns trees) (foldl (lambda (a-tree total) (+ total (count-provenances a-tree))) 0 trees)]
    ; A proof over an OR branch needs to contain 1 sub-proof from each obligation
    ; Thus: there are as many (not-unnecessarily-bloated) proofs are there are combinations of 1 from each
    [(ORProof anns als trees) (foldl (lambda (a-tree total) (* total (count-provenances a-tree))) 1 trees)]
    ; Should never be called on an alpha node since we're counting productive paths to contradiction
    [else (error "count-provenances bad arg type" ptree)]))

(require mischief/stream)

; Todo: we might consider building a stream of single provenance trees (i.e., trimming out AND and non-used OR options)
; https://docs.racket-lang.org/mischief/stream.html#%28def._%28%28lib._mischief%2Fstream..rkt%29._stream-cross-product%29%29
(define/contract (build-alphaset-stream ptree)
  (@-> provenanceNode? stream?)  
  (match ptree
    ; stream of only one alpha-set, which is empty
    [(contraLeaf anns f) (stream (list->set '()))]
    ; bypass desugaring
    [(desugarStep anns tree) (build-alphaset-stream tree)]
    ; each AND child is its own source of alpha-sets; build stream for each and then tie together
    [(ANDProof anns trees) (apply stream-append (map build-alphaset-stream trees))]
    ; lazily construct the cartesian-product of the child streams, lazily union-product each of them
    [(ORProof anns als trees)
     (define sub-proof-streams (map build-alphaset-stream trees))     
     ; build a lazy stream of LISTS OF ALPHA SETS, where each list can just be unioned directly
     (define cartesian (foldl (lambda (s acc) (stream-cross-product (lambda (x y) (flatten (list x y))) s acc))
                              (first sub-proof-streams)
                              (rest sub-proof-streams)))
     ;(printf "************~n cartesian: ~a~n" (stream->list cartesian))
     ; In case of only 1 subtree, above foldl will produce a stream-of-alphasets, not a list-of-streams-of-alphasets
     (stream-map/once (lambda (los) (set-union (list->set als)
                                               (if (list? los)
                                                   (apply set-union los)
                                                   los))) cartesian)]
    [else (error "build-nth-alphaset bad arg type" ptree)]))

; TODO: UNCOMMENT THIS LATER 
;(require pretty-format)
;(pretty-printf "Tree is: ~a~nCount of provenances: ~a~n"
;               test_N1N1_edges
;               (count-provenances test_N1N1_edges))
;(define test_N1_N1_edges_pstream (build-alphaset-stream test_N1N1_edges))
;(pretty-printf "Alpha sets are: ~a~n"
;               (stream->list test_N1_N1_edges_pstream))

; Sketches how you might highlight the N^th provenance from a tree
; IMPORTANT NOTE: right now the highlighting system requires
;   (1) all involved files to be open in some tab [not doing so produces a namespace error]
;   (2) only ONE DrRacket window open at a time
;(require forge/drracket-gui) ; for highlighting
;(require racket/gui/base) ; for color% objects
;(define alpha-color (make-object color% 255 255 100))
;(define (highlight-alphaset aset-stream n)
;  (for-each (lambda (alpha)
;              (do-forge-highlight (nodeinfo-loc (node-info (alphaLeaf-alpha alpha))) alpha-color 'amalgam))
;            (set->list (stream-ref aset-stream n))))
;(define (unhighlight-amalgam) (do-forge-unhighlight 'amalgam)) 
; (highlight-alphaset test_N1_N1_edges_pstream 1)
; then call
; (unhighlight-amalgam)