#lang racket

(require "lang/ast.rkt" "lang/bounds.rkt" (prefix-in @ racket) "server/forgeserver.rkt"
         "kodkod-cli/server/kks.rkt" "kodkod-cli/server/server.rkt"
         "kodkod-cli/server/server-common.rkt" "translate-to-kodkod-cli.rkt" "translate-from-kodkod-cli.rkt" racket/stxparam br/datum
         "breaks.rkt"
         "characteristic.rkt"
         "demo/life.rkt")

; racket/string needed for replacing transpose operator (~) with escaped version in error messages
(require (for-syntax racket/syntax)
         (for-syntax racket/string))
(require racket/trace)

(provide break instance quote begin println filepath set-path! let void)

(define filepath #f)
(define (set-path! path)
  (set! filepath path))

(define lower-bounds (make-hash))
(define upper-bounds (make-hash))
(define top-level-leftovers (make-hash))
(define top-extras (make-hash))

(define-for-syntax sig-to-fields (make-hash))

;Default bound
(define top-level-bound 4)
;Track what sigs exist in the universe (ints always do)
(define sigs '())
;Track singletons to instantiate an ocelot universe
(define working-universe '())
;Map from relations to lists of types
(define relations-store (make-hash))
;Map from sigs to sigs to track hierarchy
(define extensions-store (make-hash))
;Opposite direction of extensions-store
(define parents (make-hash))
;Map from relations to explicit bounds
(define bounds-store (make-hash))
;Map from relations to int bounds
(define int-bounds-store (make-hash))
;Extra constraints on the model (e.g. facts, relation constraints, etc.)
(define constraints '())
(define run-constraints '())  ; just for a single run
;Run names
(define run-names '())
;Bitwidth
(define bitwidth 4)

;Solver choice: default to MiniSat (no cores, so no proof overhead, faster than SAT4J)
; ^ Except that MiniSat isn't built for 64 bit windows, so maximize chances of working
(define solveroption 'SAT4J)
; max symmetry-breaking predicate size. Alloy's default was 20; set to 0 to disable SB
(define sboption 20)
; core granularity and log translation --- affect core quality (see kodkod docs)
(define coregranoption 0)
(define logtransoption 1)
(define showoption #t)
(define demo #f)
(define boundsyoption #t)
(define writeoption #f)
(define readoption #f)

; set of one sigs
(define one-sigs (mutable-set))
; set of abstract sigs
(define abstract-sigs (mutable-set))
; is the current command using exactly
(define is-exact #f)
(define (set-is-exact) (set! is-exact #t))
; user defined exact bindings
(define bindings (make-hash))
; user defined partial bindings
(define pbindings (make-hash))
; function and predicate datums for evaluator
(define funs-n-preds (make-hash))

(define (clear-state)
  (clear-breaker-state) ; breakers has done its job if this command had fancy-bounds; clean for next command
  (set! working-universe empty) ; clear out the working universe for next command or else "(univ X)" will grow in kk
  (set! int-bounds-store (make-hash))
  (set! is-exact #f)
  (set! lower-bounds (make-hash))
  (set! upper-bounds (make-hash))
  (set! top-level-leftovers (make-hash))
  (set! top-extras (make-hash))
  (set! run-constraints '())
  (set! bindings (make-hash))
  (set! pbindings (make-hash)))

(provide define-for-evaluator)
(define (define-for-evaluator name args block) (hash-set! funs-n-preds name (list args block)))

; For verbosity, etc. that must be shared without cyclic dependency
(require "shared.rkt")

(define-syntax-rule (debug x) (begin (printf "~a: ~a~n" 'x x) x))

; Filter options to prevent user from rewriting any global
; Note that we cannot use dash in option names
(define (set-option key val)
  ;(println key)
  ;(println val)
  (match key
    ['solver (set! solveroption val)]
    ['verbosity (set-verbosity val)]
    ['verbose (set-verbosity val)]
    ['coregranularity (set! coregranoption val)]
    ['sb (set! sboption val)]
    ['logtranslation (set! logtransoption val)]
    ['show (set! showoption (equal? val '|1|))]
    ['boundsy (set! boundsyoption (equal? val '|1|))]
    ['write (set! writeoption (equal? val '|1|))]
    ['read (set! readoption (read (open-input-string (symbol->string val))))]
    ['demo
     (match val
       ['life (set! demo 'life)]
       [else (error (format "Invalid option key: ~a" key))])]
    [else (error (format "Invalid option key: ~a" key))]))

(define process-command-line-args
  (command-line
    #:usage-help "FORGE!"
    #:once-each
    [("-v" "--verbose" "--verbosity") VERBOSITY "set verbosity" 
      (set-option 'verbosity (string->number VERBOSITY))]
    [("--show") SHOW "whether to open visualizer" 
      (set-option 'show SHOW)]
    [("--boundsy") BOUNDSY "whether to allow boundsy breaks" 
      (set-option 'boundsy (string->symbol BOUNDSY))]
    [("--write") "whether to write instances to stdout" 
      (set-option 'write '|1|)
      (set-option 'show 0)]
    [("--read") READ "input instance" 
      (set-option 'read (string->symbol READ))
      (set-option 'show 0)]
    #:args () (void)))

(define (set-bitwidth i) (set! bitwidth i))

(struct int-bound (lower upper) #:transparent)

; Deprecated - we've removed facts from the surface language and also I'm not sure they work with state-cleaning
(define (fact form)
  (set! constraints (cons form constraints)))


(provide pre-declare-sig declare-one-sig declare-sig set-top-level-bound sigs pred)
(provide run check test fact)
(provide Int iden univ none)
(provide no some one lone all two)
(provide + - ^ & ~ join !)
(provide set in )
(provide = -> * => not and or)
(provide set-bitwidth)
(provide < > int=)
(provide add subtract multiply divide sign abs remainder)
(provide card sum sing succ max min)
(provide add-relation set-option)

(define (add-relation rel types)
  (hash-set! relations-store rel types))

(define-syntax (pred stx)
  (syntax-case stx ()
    [(_ (name vars ...) form) #'(define (name vars ...) form)]
    [(_ name form) #'(define name form)]))

(define (add-constraint c) (set! constraints (cons c constraints)))
(define (add-constraints cs) (set! constraints (append cs constraints)))
(define (add-run-constraint c) (set! run-constraints (cons c run-constraints)))
(define (add-run-constraints cs) (set! run-constraints (append cs run-constraints)))

(define (add-extension child parent)
  (if (equal? parent univ)
      #f
      (if (hash-has-key? parents parent)
          (hash-set! parents parent (cons child (hash-ref parents parent)))
          (hash-set! parents parent (list child))))
  (hash-set! extensions-store child parent))

(define (update-int-bound rel new)
  ; if int-bounds are already defined, intersect the old/new intervals
  (cond [(hash-has-key? int-bounds-store rel)
         (define old (hash-ref int-bounds-store rel))
         (define lower (@max (int-bound-lower old) (int-bound-lower new)))
         (define upper (@min (int-bound-upper old) (int-bound-upper new)))
         (when (@> lower upper) (error (format "conflicting int-bounds: no [~a, ~a] & [~a, ~a]"
                                               (int-bound-lower old) (int-bound-upper old) (int-bound-lower new) (int-bound-upper new))))
         (hash-set! int-bounds-store rel (int-bound lower upper))
         ][else
           (hash-set! int-bounds-store rel new)]))

; It's possible for there to exist reference cycles in sig fields.
; The reader lifts sig declarations to the top level to ensure that
; sigs are bound before all the relation declarations occur.
(define-syntax (pre-declare-sig stx)
  (syntax-case stx ($remainder-sig$)
    [(_ name)
     #'(begin
         (define name (declare-relation (list (symbol->string 'name)) "univ" (symbol->string 'name)))
         (add-sig name))]
    [(_ name #:extends parent)
     #'(begin
         (define name (declare-relation (list (symbol->string 'name)) (symbol->string 'parent) (symbol->string 'name)))
         (add-sig name (symbol->string 'parent)))]))

(define-syntax (declare-field stx)
  (syntax-case stx (set one lone two)
    [(_ set name field r ...)
     #'(begin
         (define field (declare-relation (list (symbol->string 'name) (symbol->string 'r) ...) (symbol->string 'name) (symbol->string 'field)))
         (add-relation field (list name r ...))
         (add-constraint (in field (-> name r ...))))]
    [(_ one name field r ...)
     #'(begin
         (define field (declare-relation (list (symbol->string 'name) (symbol->string 'r) ...) (symbol->string 'name) (symbol->string 'field)))
         (add-relation field (list name r ...))
         (add-constraint (in field (-> name r ...)))
         (add-constraint (all ([n name]) (one (join n field)))))]
    [(_ two name field r ...)
     #'(begin
         (define field (declare-relation (list (symbol->string 'name) (symbol->string 'r) ...) (symbol->string 'name) (symbol->string 'field)))
         (add-relation field (list name r ...))
         (add-constraint (in field (-> name r ...)))
         (add-constraint (all ([n name]) (two (join n field)))))]
    [(_ lone name field r ...)
     #'(begin
         (define field (declare-relation (list (symbol->string 'name) (symbol->string 'r) ...) (symbol->string 'name) (symbol->string 'field)))
         (add-relation field (list name r ...))
         (add-constraint (in field (-> name r ...)))
         (add-constraint (all ([n name]) (lone (join n field)))))]))

(define-syntax (declare-sig stx)
  (syntax-case stx ()
    [(_ name ((field mult r ...) ...))
     (hash-set! sig-to-fields (syntax->datum #'name)
                (syntax->datum #'(field ...)))
     #'(begin
         (declare-field mult name field r ...) ...)]
    [(_ name ((field mult r ...) ...) #:extends parent)
     (hash-set! sig-to-fields (syntax->datum #'name)
                (append (syntax->datum #'(field ...)) (hash-ref sig-to-fields (syntax->datum #'parent))))
     #'(begin
         (declare-field mult name field r ...) ...
         (add-extension name parent)
         (add-constraint (in name parent)))]
    [(_ name)
     (hash-set! sig-to-fields (syntax->datum #'name) (list))
     #'(begin)]
    [(_ name #:extends parent)
     (hash-set! sig-to-fields (syntax->datum #'name)
                (hash-ref sig-to-fields (syntax->datum #'parent)))
     #'(begin
         (add-extension name parent)
         (add-constraint (in name parent)))]))

(define-syntax (declare-one-sig stx)
  (define result
    (syntax-case stx ()
      [(_ name ((field mult r ...) ...))
       (hash-set! sig-to-fields (syntax->datum #'name)
                  (syntax->datum #'(field ...)))
       #'(begin
           (declare-field mult name field r ...) ...
           (set-add! one-sigs name))]
      [(_ name ((field mult r ...) ...) #:extends parent)
       (hash-set! sig-to-fields (syntax->datum #'name)
                  (append (syntax->datum #'(field ...)) (hash-ref sig-to-fields (syntax->datum #'parent))))
       #'(begin
           (declare-field mult name field r ...) ...
           (set-add! one-sigs name)
           (add-extension name parent)
           (add-constraint (in name parent)))]
      [(_ name)
       (hash-set! sig-to-fields (syntax->datum #'name) (list))
       #'(begin
           (set-add! one-sigs name))]
      [(_ name #:extends parent)
       (hash-set! sig-to-fields (syntax->datum #'name)
                  (hash-ref sig-to-fields (syntax->datum #'parent)))
       #'(begin
           (set-add! one-sigs name)
           (add-extension name parent)
           (add-constraint (in name parent)))]))
  result)

(define (add-sig name [parent "univ"])
  (set! sigs (cons name sigs)))

(define (set-top-level-bound b) (set! top-level-bound b))

; Produce a list of constraints enforcing that <sigs> is pairwise disjoint
(define (disjoint-list sigs)
  (if (empty? sigs) (list true) (append (disjoint-one-list (first sigs) (rest sigs)) (disjoint-list (rest sigs)))))

; Produce a list of constraints enforcing that <sig> is disjoint from everything in <sigs>
(define (disjoint-one-list sig sigs)
  (if (empty? sigs) (list true) (cons (no (& sig (first sigs))) (disjoint-one-list sig (rest sigs)))))


; Recursively generates atoms that can possibly exist in a sig
; Depracated - use next-atoms instead
(define (generate-atoms sig lower upper)
  (define sig-name (string->symbol (relation-name sig)))
  (define syms (if (and (hash-has-key? bindings sig-name)
                        (cons? (hash-ref bindings sig-name))
                        (symbol? (caar (hash-ref bindings sig-name))))
                   (map first (hash-ref bindings sig-name))
                   (list)))

  (printf "sig : ~v~n" sig)
  (printf "syms : ~v~n" syms)

  (map
   (lambda (n)
     (if (@< n (length syms))
         (list-ref syms n)
         (string->symbol (string-append (relation-name sig) (number->string n)))))
   (range lower upper)))


; Generates the lowest n atoms for sig not already contained in lower
(define (next-atoms sig lower ind n)
  (if (@= n 0)
      '()
      (let ([name (if (and (hash-has-key? bindings sig)
                           (@< ind (length (hash-ref bindings sig))))
                      (list-ref (hash-ref bindings sig) ind)
                      (string->symbol (string-append (relation-name sig) (number->string ind))))])
        (if (member name lower)
            (next-atoms sig lower (@+ ind 1) n)
            (cons name (next-atoms sig (cons name lower) (@+ ind 1) (@- n 1)))))))

; Returns a list of symbols representing atoms
(define (compute-lower-bound parent-sig hashy-bounds)
  (if (hash-has-key? lower-bounds parent-sig) (hash-ref lower-bounds parent-sig)
      (let ()
        (define lower-bound '())
        (if (hash-has-key? parents parent-sig)
            ; If the sig is not a leaf sig, figure out all the atoms that must be in a child sig
            (begin
              (for ([child (hash-ref parents parent-sig)])
                (set! lower-bound (append (compute-lower-bound child hashy-bounds) lower-bound)))
              (let ([additional-lower-bound (int-bound-lower (get-bound parent-sig hashy-bounds))])
                (hash-set! top-extras parent-sig '())
                (when (@> additional-lower-bound (length lower-bound))
                  (let* ([extras (next-atoms parent-sig lower-bound 0 (@- additional-lower-bound (length lower-bound)))])
                    (hash-set! top-extras parent-sig extras)
                    (set! lower-bound (append extras lower-bound))
                    (set! working-universe (append extras working-universe)))))
              (hash-set! lower-bounds parent-sig lower-bound)
              lower-bound)
            ; Otherwise, return the lower bounds for this sig
            (begin
              (hash-set! top-extras parent-sig '())
              (set! lower-bound (next-atoms parent-sig '() 0 (int-bound-lower (get-bound parent-sig hashy-bounds))))
              (set! working-universe (append lower-bound working-universe))
              (hash-set! lower-bounds parent-sig lower-bound)
              lower-bound)))))

; Populates the universe with atoms up to each sig's upper bound.
; Because of the nasty stateful nature of this implementation, this
; needs to be called after compute-lower-bound :(
(define (fill-leftovers sig hashy-bounds)
  (if (hash-has-key? top-level-leftovers sig) (append (hash-ref top-extras sig) (hash-ref top-level-leftovers sig))
      ; If the sig is not top-level, get the leftovers for its parent and mooch off of them.
      ; If the sig is top-level, add atoms to the universe to represent its leftovers
      (if (hash-has-key? extensions-store sig)
          (let ([parent-leftovers (fill-leftovers (hash-ref extensions-store sig) hashy-bounds)]
                ;[how-many (@- (int-bound-upper (get-bound sig hashy-bounds)) (int-bound-lower (get-bound sig hashy-bounds)))]
                [int-upper (int-bound-upper (get-bound sig hashy-bounds))])
            (define atoms parent-leftovers)
            (hash-set! top-level-leftovers sig atoms)
            (add-run-constraint (<= (card sig) (node/int/constant int-upper)))
            (hash-set! upper-bounds sig (append atoms (hash-ref lower-bounds sig)))
            atoms)
          (let ([upper (int-bound-upper (get-bound sig hashy-bounds))] [lower (length (hash-ref lower-bounds sig))])
            (define leftovers '())
            (when (@> upper lower) (set! leftovers (next-atoms sig (hash-ref lower-bounds sig) 0 (@- upper lower))))
            (set! working-universe (append leftovers working-universe))
            (hash-set! top-level-leftovers sig leftovers)
            (hash-set! upper-bounds sig (append (hash-ref lower-bounds sig) leftovers))
            (append (hash-ref top-extras sig) leftovers)))))

; Populates the universe with atoms according to the bounds specified by a run statement
; Returns a list of bounds objects
; This is pre-erasure of unused atoms
(define (bind-sigs hashy-bounds)
  (set! lower-bounds (make-hash))
  (set! upper-bounds (make-hash))
  (set! top-level-leftovers (make-hash))

  (define out-bounds '())
  (define roots (filter (lambda (x) (@not (hash-has-key? extensions-store x))) sigs))

  (for ([root roots]) (compute-lower-bound root hashy-bounds))

  (for ([sig sigs])
    (fill-leftovers sig hashy-bounds) ; mutation!
    (set! out-bounds (cons
                      (make-bound sig
                                  (map (lambda (x) (list x)) (hash-ref lower-bounds sig))
                                  (map (lambda (x) (list x)) (hash-ref upper-bounds sig)))
                      out-bounds)))

  ; Create remainder sigs
  ; Add disjunction constraints
  (define disj-cs
    (for/fold ([cs '()]) ([par (hash-keys parents)])
      ; disjoint-list returns a list of constraints; combine all such
      (append (disjoint-list (hash-ref parents par)) cs)))
  (cons out-bounds disj-cs))

; Finds and returns the specified or implicit int-bounds object for the given sig
(define (get-bound sig hashy-bounds)
  (cond
    [(hash-has-key? hashy-bounds sig)
     (hash-ref hashy-bounds sig)]
    [(hash-has-key? int-bounds-store sig)
     (hash-ref int-bounds-store sig)]
    [else
     (int-bound 0 top-level-bound)]))

(define (strip-remainder str)
  (if (@< (string-length str) 10) str
      (if (equal? (substring str 0 10) "remainder-") (substring str 10) str)))

(define (append-run name)
  (if (member name run-names) (error (format "Non-unique run name specified: ~a" name)) (set! run-names (cons name run-names))))


(define (run-spec hashy name command filepath runtype . assumptions)
  (when (@>= (get-verbosity) VERBOSITY_HIGH) ; Racket >=
    (printf "ABSTRACT sigs known: ~a~n" abstract-sigs)
    (printf "bindings : ~v~n" bindings)
    (printf "pbindings : ~v~n" pbindings)
    (printf "int-bounds-store : ~v~n" int-bounds-store))
  (append-run name)

  (map instance (hash-values pbindings))
  (for ([(rel sb) (in-hash pbindings)])
    (hash-set! bindings rel (for/list ([tup (sbound-upper sb)]) (car tup))) ; this nonsense is just for atom names
  )

  (set! run-constraints (append constraints assumptions))

  (for ([rel (in-set one-sigs)]) (update-int-bound rel (int-bound 1 1)))
  (for ([sig (in-set abstract-sigs)]) 
    (define extenders (for/list ([(k v) (in-hash extensions-store)] #:when (equal? v sig)) k))
    ;(when (empty? extenders) (raise-syntax-error 'abstract (format "Abstract sig not extended ~a" sig)))
    (define c (in sig (for/fold ([res none]) ([x extenders]) (+ x res))))
    (set! run-constraints (cons c run-constraints))
  )
  
  (define intmax (expt 2 (sub1 bitwidth)))
  (define int-range (range (- intmax) intmax)) ; The range of integer *values* we can represent
  (define int-indices (range (expt 2 bitwidth))) ; The integer *indices* used to represent those values, in kodkod-cli, which doesn't permit negative atoms.
  (define int-range-singletons (map list int-range))


  (match-define (cons sig-bounds disj-cs) (bind-sigs hashy)) ; TODO: look here!!!!!!!!!!!!!!!
  (set! run-constraints (append run-constraints disj-cs))
  (define inty-univ (append int-range working-universe)) ; A universe of all possible atoms, including integers (actual values, not kodkod-cli indices)

  ; Add integer atoms forcefully because they always exist
  (set! sig-bounds (cons (bound Int int-range-singletons int-range-singletons) sig-bounds))
  (hash-set! bounds-store Int int-range) ; Set an exact bount on Int to contain int-range
  (hash-set! upper-bounds Int int-range)
  (hash-set! lower-bounds Int int-range)

  ; Int needs to be in upper-bounds, lower-bounds, and sig-bounds
  (define total-bounds (append (map relation->bounds (hash-keys relations-store)) sig-bounds))
  (define rels (append (hash-keys relations-store) sigs (list Int)))

  ; Add the successor relation on integers (and it's exact)
  (define successor-rel (map list (take int-range (sub1 (length int-range))) (rest int-range)))
  (set! total-bounds (append total-bounds (list (bound succ successor-rel successor-rel))))
  (set! rels (append rels (list succ)))

  (when readoption 
    (printf "chi(I) : ~v~n" (inst-to-formula readoption rels))
    (cons! run-constraints (inst-to-formula readoption rels)))

  ; Initializing our kodkod-cli process, and getting ports for communication with it
  (define kks (new server%
                   [initializer (thunk (kodkod-initializer #f))]
                   [stderr-handler (curry kodkod-stderr-handler "blank")]))
  (send kks initialize)
  (define stdin (send kks stdin))
  (define stdout (send kks stdout))

  (cmd
   [stdin]
   ; Stepper problems in kodkod-cli ignore max-solutions, and 7 is max verbosity.
   ; TODO: use our verbosity setting? (unclear how kodkod differs by verbosity)
   (configure (format ":bitwidth ~a :solver ~a :max-solutions 1 :verbosity 7 :sb ~a :core-gran ~a :log-trans ~a"
                      bitwidth solveroption sboption coregranoption logtransoption))
   (declare-univ (length inty-univ))
   (declare-ints int-range int-indices))
  (define (get-atom atom)
    (define result (index-of inty-univ atom))
    (cond [result result]
          [else (error (format "Error: reference to unknown atom: ~a. Known atoms were: ~a" atom inty-univ))]))
  (define (n-arity-none arity)
    (cond
      [(equal? arity 1) 'none]
      [(@> arity 0) (product 'none (n-arity-none (@- arity 1)))]
      [else (error "Error: Relation with negative or 0 arity specified.")]))

  (define (adj-bound accessor bound)
    ; "int-atoms" here means the int representations at the kodkod level, not Int/int integers
    (define int-atoms (map (lambda (x) (map get-atom x))
                           (accessor bound)))
    (if (empty? int-atoms)
        (n-arity-none (relation-arity (bound-relation bound)))
        (tupleset #:tuples int-atoms)))


  (if boundsyoption 
    (let-values ([(new-total-bounds new-formulas)
                  (constrain-bounds total-bounds sigs upper-bounds relations-store extensions-store)])
      (set! total-bounds new-total-bounds)
      (set! run-constraints (append run-constraints new-formulas)))
    (let ([new-formulas (constrain-formulas upper-bounds relations-store)])
      (set! run-constraints (append run-constraints new-formulas)))
  )

  (when is-exact
    (for ([b total-bounds])
      (unless (exact-bound? b) (error (format "bounds declared exactly but ~a not exact"
                                              (relation-name (bound-relation b)))))
      )
    )

  (for ([bound total-bounds])
    (cmd
     [stdin]
     (declare-rel
      (r (index-of rels (bound-relation bound)))

      (adj-bound bound-lower bound)  ; if empty, need to give proper arity emptiness
      (adj-bound bound-upper bound))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;

  (for ([c run-constraints] [i (range (length run-constraints))])
    (cmd
     [stdin]
     (print-cmd-cont (format "(f~a " i)) ; extra space in case forthcoming formula is "true" with no leading space
     (translate-to-kodkod-cli c rels '())
     (print-cmd ")")
     (print-cmd (format "(assert f~a)" i))))

  (clear-state) ; breakers has done its job if this command had fancy-bounds; clean for next command

  (match runtype
    ['test
     (cmd [stdin] (solve))
     (car (read-solution stdout))]
    [_
     (define (get-next-model)
       (cmd [stdin] (solve))
       (match-define (cons restype inst) (translate-from-kodkod-cli runtype (read-solution stdout) rels inty-univ))
       (when (and readoption inst (equal? restype 'sat)) 
        (printf "INSTANCE : ~a~n" inst))
       (when (and writeoption inst (equal? restype 'sat))
        (printf "INSTANCE : ~a~n" inst)
        ; TODO: make interactive:
        ;(sleep 0.01)
        ;(display "press enter for another... ")
        ;(define wait (read-line))
        (display-model get-next-model name command filepath bitwidth funs-n-preds showoption))
       (when (and demo (equal? restype 'sat))
         (match demo
           ['life (output-life inst)]))
       (cons restype inst))
     (display-model get-next-model name command filepath bitwidth funs-n-preds showoption)]))

(define-syntax (run stx)
  (define command (format "~a" stx))
  (syntax-case stx ()
    [(_ name ((sig lower upper) ...))
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper)))) ...
                                                                                                          (run-spec hashy name #,command filepath 'run))]
    [(_ name (preds ...) ((sig lower upper) ...))
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper)))) ...
                                                                                                          (run-spec hashy name #,command filepath 'run preds ...))]
    [(_ name)
     #`(begin
         (run-spec (make-hash) name #,command filepath 'run))]
    [(_ name (preds ...))
     #`(begin
         (run-spec (make-hash) name #,command filepath 'run preds ...))]
    [(_ name (preds ...) ((sig lower upper) ...) (facty ...))
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper)))) ...
                                                                                                          (run-spec hashy name #,command filepath 'run preds ... facty ...))]
    [(_ pred ((sig lower upper) ...)) #'(error "Run statements require a unique name specification")]
    [(_ pred) #'(error "Run statements require a unique name specification")]
    [(_) #'(error "Run statements require a unique name specification")]
    [(_ ((sig lower upper) ...)) #'(error "Run statements require a unique name specification")]))


(define-syntax (check stx)
  (define command (format "~a" stx))
  (syntax-case stx ()
    [(_ name ((sig lower upper) ...))
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper))))
         ...
         (run-spec hashy name #,command filepath 'check))]
    [(_ name (preds ...) ((sig lower upper) ...))
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper))))
         ...
         (run-spec hashy name #,command filepath 'check (or (not preds) ...)))]
    [(_ name)
     #`(begin
         (run-spec (make-hash) name #,command filepath 'check))]
    [(_ name (preds ...))
     #`(begin
         (run-spec (make-hash) name #,command filepath 'check (or (not preds) ...)))]
    [(_ name (preds ...) ((sig lower upper) ...) (facty ...))
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper))))
         ...
         (run-spec hashy name #,command filepath 'check (and (and facty ...) (or (not preds) ...))))]
    [(_ pred ((sig lower upper) ...)) #'(error "Check statements require a unique name specification")]
    [(_ pred) #'(error "Check statements require a unique name specification")]
    [(_) #'(error "Check statements require a unique name specification")]
    [(_ ((sig lower upper) ...)) #'(error "Check statements require a unique name specification")]))

(define-syntax (test stx)
  (define command (string-replace (format "~a" stx) "~" "~~" #:all? #t))
  (syntax-case stx ()
    [(_ name ((sig lower upper) ...) expect)
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper))))
         ...
         (define res (run-spec hashy name #,command filepath 'test))
         (unless (equal? res expect)
           (error (format-datum '~a-~a "test" name) (format "expected ~a, got ~a in\n ~a" expect res #,command))))]
    [(_ name (preds ...) ((sig lower upper) ...) expect)
     #`(begin
         (define hashy (make-hash))
         (if (equal? sig Int)
             (set-bitwidth upper)
             (unless (hash-has-key? int-bounds-store sig) (hash-set! hashy sig (int-bound lower upper))))
         ...
         (define res (run-spec hashy name #,command filepath 'test preds ...))
         (unless (equal? res expect)
           (error (format-datum '~a-~a "test" name) (format "expected ~a, got ~a in\n~a" expect res #,command))))]
    [(_ name expect)
     #`(begin
         (define res (run-spec (make-hash) name #,command filepath 'test))
         (unless (equal? res expect)
           (error (format-datum '~a-~a "test" name) (format "expected ~a, got ~a in\n~a" expect res #,command))))]
    [(_ name (preds ...) expect)
     #`(begin
         (define res (run-spec (make-hash) name #,command filepath 'test preds ...))
         (unless (equal? res expect)
           (error (format-datum '~a-~a "test" name) (format "expected ~a, got ~a in ~a" expect res #,command))))]
    [(_ pred ((sig lower upper) ...)) #'(error "Run statements require a unique name specification")]
    [(_ pred) #'(error "Run statements require a unique name specification")]
    [(_) #'(error "Run statements require a unique name specification")]
    [(_ ((sig lower upper) ...)) #'(error "Run statements require a unique name specification")]))


(define (relation->bounds rel)
  (make-bound rel '() (apply cartesian-product (map (lambda (x) (hash-ref upper-bounds x)) (hash-ref relations-store rel)))))


;;;;;;;;;;;;;;;;;
;;;; FORGE 2 ;;;;
;;;;;;;;;;;;;;;;;

(require syntax/parse/define)
(require (for-meta 1 racket/port racket/list))

(provide node/int/constant ModuleDecl SexprDecl Sexpr SigDecl CmdDecl TestExpectDecl TestDecl TestBlock PredDecl Block BlockOrBar
         AssertDecl BreakDecl InstanceDecl QueryDecl FunDecl ;ArrowExpr
         StateDecl TransitionDecl RelDecl OptionDecl InstDecl TraceDecl
         Expr Name QualName Const Number iff ifte >= <= ni)

;;;;

(define-for-syntax (map-stx f . stx) (datum->syntax (car stx) (apply f (map syntax->datum stx)) (car stx)))
(define-for-syntax (at stx datum) (datum->syntax stx datum stx))
(define-for-syntax (replace-ints datum)
  (cond
    [(list? datum)
     (if (equal? (car datum) 'run)
         datum
         (map replace-ints datum))]
    [(integer? datum)
     `(node/int/constant ,datum)]
    [else datum]))
(define-for-syntax (process-DeclList d)
  (define ret (syntax-case d
                (NameList Mult SigExt DeclList ArrowDeclList ArrowExpr Block ArrowMult QualName)
                [(ArrowDeclList (_ (NameList nss ...) (ArrowMult mults) (ArrowExpr (QualName ess) ...)) ...)
                 (apply append (map (lambda (ns m es) (map (lambda (n)
                                                             `(,n ,(string->symbol m) ,@es)) ns))
                                    (syntax->datum #'((nss ...) ...))
                                    (syntax->datum #'(mults ...))
                                    (syntax->datum #'((ess ...) ...))))]
                [(DeclList (_ (NameList nss ...) es) ...)
                 (apply append (map (lambda (ns e) (map (lambda (n) `(,n ,e)) ns))
                                    (syntax->datum #'((nss ...) ...))
                                    (syntax->datum #'(es ...))))]))
  ret)
(define-for-syntax (use-ctxt stx1 stx2)
  (datum->syntax stx1 (syntax->datum stx2)))

(define (process-fp fp)
  (define path (path->string (expand-user-path (string->path fp))))
  (if (string-contains? path "/")
      path
      (string-append "./" path)))

(define-syntax (OptionDecl stx)
  (map-stx (lambda (d)
             (define key (syntax-case (first (rest d)) (QualName)
                           [(QualName n) #''n]))
             (define val (syntax-case (second (rest d)) (QualName Number)
                           [(QualName n) #''n]
                           [(Number n) #'(string->number n)]
                           [fp #'(string-append "\"" (process-fp fp) "\"")]))
             `(set-option ,key ,val)) stx))

(define-syntax (ModuleDecl stx) (datum->syntax stx '(begin))) ;; nop
(define-syntax (SexprDecl stx) (map-stx cadr stx))
(define-syntax (Sexpr stx)
  (map-stx (lambda (d)
             (replace-ints (cons 'begin (port->list read (open-input-string (cadr d)))))
             ) stx))
(define-syntax (SigDecl stx)
             (define-values (abstract one names qualName decls exprs) (values #f #f '() #f '() '()))
             (for ([arg (cdr (syntax->list stx))])
               (syntax-case arg (NameList Mult SigExt ArrowDeclList Block)
                 ["abstract" (set! abstract #t)]
                 [(Mult "one") (set! one #t)]
                 [(NameList ns ...) (set! names #'(ns ...))]
                 [(SigExt "extends" qn) (set! qualName #'qn)]
                 [(ArrowDeclList _ ...) (set! decls (process-DeclList arg))]
                 [(Block es ...) (set! exprs #'(es ...))]
                 [_ #f]
                 )
               )
             (set! names (syntax->list names))
             (if qualName (set! qualName (cadr (syntax->list qualName))) #f)

             (define op (if one 'declare-one-sig 'declare-sig))
             (define ret
               (if qualName
                   (if (= 0 (length decls))
                       (cons 'begin (map (lambda (name) `(,op ,name #:extends ,qualName)) names))
                       (cons 'begin (map (lambda (name) `(,op ,name ,decls #:extends ,qualName)) names))
                       )
                   (if (= 0 (length decls))
                       (cons 'begin (map (lambda (name) `(,op ,name)) names))
                       (cons 'begin (map (lambda (name) `(,op ,name ,decls)) names)))))
             (set! ret #`(begin
               #,(at stx ret)
               #,@(if abstract (for/list ([name names]) #`(set-add! abstract-sigs #,name)) '())
             ))
             ;(printf "ret : ~v~n" ret)
             ret
             )

; See note in parser.rkt about difference between InstanceDecl and InstDecl
(define-syntax-rule (InstanceDecl i) (instance i))

(define-syntax (CmdDecl stx)
             (define-values (name cmd arg scope block bounds facty-params) (values #f #f #f '() '() '() #'()))
             (define (make-typescope x)
               (syntax-case x (Typescope)
                 [(Typescope "exactly" n things) (syntax->datum #'(things n n))]
                 [(Typescope n things) (syntax->datum #'(things 0 n))]))
             (for ([arg (cdr (syntax->list stx))])
               (syntax-case arg (Name Typescope Scope Block QualName Parameters)
                 [(Name n) (set! name (symbol->string (syntax->datum #'n)))]
                 ["run"   (set! cmd 'run)]
                 ["check" (set! cmd 'check)]
                 [(Scope s ...) (set! scope (map make-typescope (syntax->datum #'(s ...))))]
                 ;[(Block (Expr (QualName ns)) ...) (set! block #'(ns ...))]
                 [(Block b ...) (set! block #'(b ...))]
                 [(QualName n) (set! block (list #'n))]
                 [(Parameters ps ...) (set! facty-params #'(ps ...))] ; Traces should go in here - anything in params will be considered a fact in a check block.
                 [(Bounds bs ...) (set! bounds #'(bs ...))]
                 [_ #f]))
             ; Duplicate with TestDecl
             (define param-facts (for/list ([p (syntax->list facty-params)]) 
                                   (at p `(Expr (QualName ,(string->symbol (format "~a_fact" (syntax->datum p))))))))
             (define param-insts (for/list ([p (syntax->list facty-params)]) 
                                   (at p `(Expr (QualName ,(string->symbol (format "~a_inst" (syntax->datum p))))))))
             (set! bounds `(Bounds ,@param-insts ,@bounds))

             (if name #f (set! name (symbol->string (gensym))))
             (define ret (at stx `(begin
                              (void ,@(syntax->list facty-params)) ;; noop but fails early if undefined
                              ,bounds
                              (,cmd ,name ,block ,scope ,param-facts))))
             ;(printf "ret : ~v~n" ret)
             ret)

(define-syntax (TestDecl stx)
  (map-stx (lambda (d)
             (define-values (name cmd arg scope block bounds params expect) (values #f 'test #f '() '() '() #'() #f))  
             (define (make-typescope x)
               (syntax-case x (Typescope)
                 [(Typescope "exactly" n things) (syntax->datum #'(things n n))]
                 [(Typescope n things) (syntax->datum #'(things 0 n))]))
             (for ([arg (cdr d)])
               (syntax-case arg (Name Typescope Scope Block QualName Parameters)
                 [(Name n) (set! name (symbol->string (syntax->datum #'n)))]
                 ["sat" (set! expect 'sat)]
                 ["unsat" (set! expect 'unsat)]
                 [(Scope s ...) (set! scope (map make-typescope (syntax->datum #'(s ...))))]
                 [(Block (Expr (QualName ns)) ...) (set! block (syntax->datum #'(ns ...)))]
                 [(Block b ...) (set! block (syntax->datum #'(b ...)))]
                 [(QualName n) (set! block (list (syntax->datum #'n)))]
                 [(Parameters ps ...) (set! params #'(ps ...))]
                 [(Bounds bs ...) (set! bounds (syntax->datum #'(bs ...)))]
                 [_ #f]))
                                           
             ; Duplicate with CmdDecl
             (define param-facts (for/list ([p (syntax->datum params)]) 
                                   `(Expr (QualName ,(string->symbol (format "~a_fact" p))))))
             (define param-insts (for/list ([p (syntax->datum params)]) 
                                   `(Expr (QualName ,(string->symbol (format "~a_inst" p))))))
                                         
             (set! block (append block param-facts))
             (set! bounds `(Bounds ,@param-insts ,@bounds))
                                         
             (if name #f (set! name (symbol->string (gensym))))
             (define datum (if bounds  ; copied from CmdDecl
                               `(begin
                                  ,bounds
                                  (,cmd ,name ,block ,scope ',expect))
                               `(,cmd ,name ,block ,scope ',expect)))
             datum) stx))

(define-syntax (TestExpectDecl stx)
  (map-stx (lambda (d)
             (define-values (name active? block) (values #f #f '()))
             (for ([arg (cdr d)])
               (syntax-case arg (Name TestBlock)
                 [(Name n) (set! name (symbol->string (syntax->datum #'n)))]
                 ["test" (set! active? #t)]
                 [(TestBlock bs ...) (set! block #'(bs ...))]
                 [_ #f]))
             (if name #f (set! name (symbol->string (gensym))))
             (when active?
               (define datum `(begin ,@(syntax->datum block)))
               datum)) stx))

(define-syntax (PredDecl stx)
             (define-values (name paras block) (values #f '() '()))
             (for ([arg (cdr (syntax->list stx))])
               (syntax-case arg (Name ParaDecls Decl NameList Block)
                 [(Name n) (set! name (syntax->datum #'n))]
                 [(ParaDecls (Decl (NameList ps) _ ...) ...)
                  (set! paras (flatten (syntax->datum #'(ps ...))))]
                 [(Block bs ...) (set! block #'(bs ...))]
                 [_ #f]))
             (define datum (if (empty? paras)
                   (at stx `(begin 
                     (pred ,name (and ,@(syntax->list block)))
                     (define-for-evaluator ',name '() '(Block ,@(syntax->datum block)))))
                   (at stx `(begin
                     (pred (,name ,@paras) (and ,@(syntax->list block)))
                     (define-for-evaluator ',name ',paras '(Block ,@(syntax->datum block)))))))
             datum)

(define-syntax (AssertDecl stx)
  (map-stx (lambda (d)
             (define-values (name paras block) (values #f '() '()))
             (for ([arg (cdr d)])
               (syntax-case arg (Name ParaDecls Decl NameList Block)
                 [(Name n) (set! name (syntax->datum #'n))]
                 [(ParaDecls (Decl (NameList ps) _ ...) ...)
                  (set! paras (flatten (syntax->datum #'(ps ...))))]
                 [(Block bs ...) (set! block #'(bs ...))]
                 [_ #f]))
             (define datum (if (empty? paras)
                               `(assert ,name (and ,@(syntax->datum block)))
                               `(assert (,name ,@paras) (and ,@(syntax->datum block)))))
             datum) stx))

(define-syntax (FunDecl stx)
  (map-stx (lambda (d)
             (define-values (name paras block) (values #f '() '()))
             (for ([arg (cdr d)])
               (syntax-case arg (Name ParaDecls Decl NameList Block)
                 [(Name n) (set! name (syntax->datum #'n))]
                 [(ParaDecls (Decl (NameList ps) _ ...) ...)
                  (set! paras (flatten (syntax->datum #'(ps ...))))]
                 [(Block bs ...) (set! block #'(bs ...))]
                 [_ #f]))

             (define datum (if (empty? paras)
                               `(begin 
                                  (pred ,name (and ,@(syntax->datum block)))
                                  (define-for-evaluator ',name '() ',(car (syntax->datum block))))
                               `(begin
                                  (pred (,name ,@paras) (and ,@(syntax->datum block)))
                                  (define-for-evaluator ',name ',paras ',(car (syntax->datum block))))))
             datum) stx))

(define-syntax (StateDecl stx)
             (define-values (name paras block sig) (values #f '() '() #f))
             (for ([arg (cdr (syntax->list stx))])
               (syntax-case arg (Name ParaDecls Decl NameList Block QualName)
                 [(Name n) (set! name (syntax->datum #'n))]
                 [(QualName n) (set! sig (syntax->datum #'n))]
                 [(ParaDecls (Decl (NameList ps) _ ...) ...)
                  (set! paras (flatten (syntax->datum #'(ps ...))))]
                 [(Block bs ...) (set! block #'(bs ...))]
                 [_ #f]))

             (unless (hash-has-key? sig-to-fields sig)
               (raise-user-error (format "Unknown sig in state predicate (~a) declaration: ~a" name sig)))
             (define fields (hash-ref sig-to-fields sig))
             (define (at- f) (string->symbol (string-append "@" (symbol->string f))))
             (define lets (append
                           (for/list ([f fields]) `[,f (join this ,f)])
                           (for/list ([f fields]) `[,(at- f) ,f])))
             (define ret (at stx 
              `(pred (,name this ,@paras) (let ,lets (and ,@(syntax->list block))))))
             ret)

(define-syntax (TransitionDecl stx)
             (define-values (name paras block sig) (values #f '() '() #f))
             (for ([arg (cdr (syntax->list stx))])
               (syntax-case arg (Name ParaDecls Decl NameList Block QualName)
                 [(Name n) (set! name (syntax->datum #'n))]
                 [(QualName n) (set! sig (syntax->datum #'n))]
                 [(ParaDecls (Decl (NameList ps) _ ...) ...)
                  (set! paras (flatten (syntax->datum #'(ps ...))))]
                 [(Block bs ...) (set! block #'(bs ...))]
                 [_ #f]))

             (define fields (hash-ref sig-to-fields sig))
             (define (post f) (string->symbol (string-append (symbol->string f) "'")))
             (define (at- f) (string->symbol (string-append "@" (symbol->string f))))
             (define posts (map post fields))
             (define lets (append* (for/list ([f fields] [p posts])
                                     (list
                                      `[,f (join  this   ,f)]
                                      `[,p (join |this'| ,f)]
                                      `[,(at- f) ,f]
                                      ))))
             (define ret (at stx 
               `(pred (,name this |this'| ,@paras) (let ,lets (and ,@(syntax->list block))))))

             ; require either this' or all f', g', ... to be used in block
             ; this is checked at macro-expansion, but raised at run-time
             (define (find-syms term)
               (define syms (list))
               (define (find-syms b)
                 (syntax-case b (QualName)
                   [(QualName n) (set! syms (cons (syntax->datum #'n) syms))]
                   [(_ ...) (map find-syms b)]
                   [_ #f]
                   ))
               (find-syms term)
               syms)
             (define syms (find-syms (syntax->datum block)))
             (unless (or (member '|this'| syms) (for/and ([f posts]) (member f syms)))
               (define unspec (for/list ([f posts] #:unless (member f syms)) f))
               (raise-syntax-error name
                (format "Underspecified transition predicate. Please specify these fields: ~a" unspec)
                stx))

             ;; DON'T DELETE! Just temporarily commenting out until we decide on behavior.  
             ;(for ([clause block])
             ;  (define syms (find-syms clause))
             ;  (unless (or (member '|this'| syms)
             ;              (foldl (λ (x y) (or x y)) #f (for/list ([s syms])
             ;                                             (or (member s posts) (member s paras)))))
             ;    (raise (string-append "Irrelevant clause in: " (symbol->string name)))))
             ;(printf "ret : ~v~n" ret)
             ret)

(define-for-syntax using-traces #f)
(define-syntax (TraceDecl stx)
             (define-values (name paras block sig params strat) (values #f '() '() #f #f 'plinear))
             (for ([arg (cdr (syntax->list stx))])
               (syntax-case arg (Name ParaDecls Decl NameList Block QualName Parameters Expr)
                 [(Name n) (set! name (syntax->datum #'n))]
                 [(QualName n) (set! sig (syntax->datum #'n))]
                 [(ParaDecls (Decl (NameList ps) _ ...) ...)
                  (set! paras (flatten (syntax->datum #'(ps ...))))]
                 [(Parameters ps ...) (set! params (syntax->datum #'(ps ...)))]
                 [(Block bs ...) (set! block #'(bs ...))]
                 [(Expr (QualName s)) (set! strat (syntax->datum #'s))]
                 [_ #f]
                 )
               )

             (define L (length params))
             (define S      (if (> L 0) (list-ref params 0) (error 'trace "no state sig specified for ~a" name)))
             (define S_init (if (> L 1) (list-ref params 1) '_))
             (define S_tran (if (> L 2) (list-ref params 2) '_))
             (define S_term (if (> L 3) (list-ref params 3) '_))
             (define S_inva (if (> L 4) (list-ref params 4) '_))

             (define T name)
             (define T_pred (string->symbol (format "~a_pred" name)))
             (define T_fact (string->symbol (format "~a_fact" name)))
             (define T_inst (string->symbol (format "~a_inst" name)))

             (define init 'init)
             (define tran 'tran)
             (define term 'term)

             (define ret
               (at stx `(begin
                  ,@(if using-traces '() `(
                    (pre-declare-sig TraceBase #:extends univ)
                    (SigDecl 
                      "abstract"
                      (NameList TraceBase)
                      (ArrowDeclList 
                        (ArrowDecl (NameList ,init) (ArrowMult "set") (ArrowExpr (QualName ,S))) 
                        (ArrowDecl (NameList ,tran) (ArrowMult "set") (ArrowExpr (QualName ,S) (QualName ,S))) 
                        (ArrowDecl (NameList ,term) (ArrowMult "set") (ArrowExpr (QualName ,S)))))))
                  (pre-declare-sig ,T #:extends TraceBase)
                  (SigDecl (Mult "one") (NameList ,T) (SigExt "extends" (QualName TraceBase)))
                  (StateDecl
                   "facts"
                   (QualName ,T)
                   (Name ,T_pred)
                   (Block 
                    ,@(syntax->list block)
                    (Expr (Expr4 "some" (Expr8 (QualName ,tran))) 
                          "=>" (Expr3 (Block 
                                       (Expr (Expr6 (QualName ,S)) (CompareOp "=") 
                                             (Expr7 (Expr8 (Expr15 (QualName ,tran)) "." (Expr16 (QualName ,S))) "+" 
                                                    (Expr10 (Expr15 (QualName ,S)) "." (Expr16 (QualName ,tran))))) 
                                       (Expr (Expr6 (QualName ,init)) (CompareOp "=") 
                                             (Expr7 (Expr8 (Expr15 (QualName ,tran)) "." (Expr16 (QualName ,S))) "-" 
                                                    (Expr10 (Expr15 (QualName ,S)) "." (Expr16 (QualName ,tran))))) 
                                       (Expr (Expr6 (QualName ,term)) (CompareOp "=") 
                                             (Expr7 (Expr8 (Expr15 (QualName ,S)) "." (Expr16 (QualName ,tran))) "-" 
                                                    (Expr10 (Expr15 (QualName ,tran)) "." (Expr16 (QualName ,S))))))) 
                          "else" (Expr3 (Block 
                                         (Expr "one" (Expr8 (QualName ,S))) 
                                         (Expr (Expr6 (QualName ,init)) (CompareOp "=") (Expr7 (QualName ,S))) 
                                         (Expr (Expr6 (QualName ,term)) (CompareOp "=") (Expr7 (QualName ,S)))))) 
                    ,@(if (equal? S_init '_) '()
                          `((Expr (Quant "all") (DeclList (Decl (NameList s) (Expr (QualName ,init)))) 
                                  (BlockOrBar "|" (Expr (Expr14 (QualName ,S_init)) 
                                                        "[" (ExprList (Expr (QualName s))) "]"))))) 
                    ,@(if (equal? S_tran '_) '()
                          `((Expr (Quant "all") (DeclList 
                                                 (Decl (NameList s) (Expr (QualName ,S))) 
                                                 (Decl (NameList |s'|) (Expr (Expr15 (QualName s)) "." (Expr16 (QualName ,tran))))) 
                                  (BlockOrBar "|" (Expr (Expr14 (QualName ,S_tran)) 
                                                        "[" (ExprList (Expr (QualName s)) (Expr (QualName |s'|))) "]")))))
                    ,@(if (equal? S_term '_) '()
                          `((Expr (Quant "all") (DeclList (Decl (NameList s) (Expr (QualName ,term)))) 
                                  (BlockOrBar "|" (Expr (Expr14 (QualName ,S_term)) 
                                                        "[" (ExprList (Expr (QualName s))) "]")))))
                    ,@(if (equal? S_inva '_) '()
                          `((Expr (Quant "all") (DeclList (Decl (NameList s) (Expr (QualName ,S)))) 
                                  (BlockOrBar "|" (Expr (Expr14 (QualName ,S_inva)) 
                                                        "[" (ExprList (Expr (QualName s))) "]")))))))
                  (PredDecl (Name ,T_fact) (Block 
                                            (Expr (Quant "all") (DeclList (Decl (NameList t) (Expr (QualName ,T)))) 
                                                  (BlockOrBar "|" (Expr (Expr14 (QualName ,T_pred)) 
                                                                        "[" (ExprList (Expr (QualName t))) "]")))))
                  (InstDecl (Name ,T_inst) (Bounds 
                                            (Expr (Expr6 (QualName ,tran)) (CompareOp "is") (Expr7 (QualName ,strat))))))))
             (set! using-traces #t)
             ;(printf "ret : ~v~n" ret)
             ret)

(define-syntax (RelDecl stx)
  (define ret (syntax-case stx (set one lone ArrowDecl NameList ArrowMult)
                [(_ (ArrowDecl (NameList name) (ArrowMult "set") (ArrowExpr r ...)))
                 #`(begin
                     (define rel (declare-relation (list r ...) "univ" name))
                     (add-relation rel (list r ...)))]
                [(_ (ArrowDecl (NameList name) (ArrowMult "one") (ArrowExpr r ...)))
                 #`(begin
                     (define rel (declare-relation (list r ...) "univ" name))
                     (add-relation rel (list r ...))
                     (add-constraint (one rel)))]
                [(_ (ArrowDecl (NameList name) (ArrowMult "lone") (ArrowExpr r ...)))
                 #`(begin
                     (define rel (declare-relation (list r ...) "univ" name))
                     (add-relation rel (list r ...))
                     (add-constraint (lone rel)))]))
  ret)

(define-syntax (TestBlock stx)
  (define ret (syntax-case stx ()
                [(_ b ...) #'(begin b ...)]))
  ret)

(define-syntax (Block stx)
  (define ret (syntax-case stx ()
                [(_ a ...) #'(and a ...)]))
  ret)
(define-syntax (BlockOrBar stx)
  (define ret (syntax-case stx (Block)
                [(_ (Block a ...)) #'(Block a ...)]
                [(_ BAR-TOK e) #'e]))
  ret)

(define-syntax-rule (BreakDecl x ys ...) (break x 'ys ...))

(define-syntax (QueryDecl stx) (map-stx (lambda (d)
                                          (define name (second d))
                                          (define type (third d))
                                          (define expr (fourth d))
                                          (define rel (string->symbol (string-append "_" (symbol->string name))))
                                          (define datum `(begin
                                                           (pre-declare-sig ,name)
                                                           (SigDecl (NameList ,name) (ArrowDeclList (ArrowDecl (NameList ,rel) (ArrowMult "set") ,type)))
                                                           (fact (one ,name))
                                                           (fact (= (join ,name ,rel) ,expr))))
                                          datum) stx))


(define-for-syntax (sym n)  (map-stx string->symbol n))

(define-syntax (Q stx)
  (define ret (syntax-case stx (sum)
                [(_ "all" n e a) (syntax/loc stx (all ([n e]) a))]
                [(_ "no" n e a) (syntax/loc stx (no ([n e]) a))]
                [(_ "lone" n e a) (syntax/loc stx (lone ([n e]) a))]
                [(_ "some" n e a) (syntax/loc stx (some ([n e]) a))]
                [(_ "one" n e a) (syntax/loc stx (one ([n e]) a))]
                [(_ "two" n e a) (syntax/loc stx (two ([n e]) a))]
                [(_ sum n e a) (syntax/loc stx (sum-quant ([n e]) a))]
                [(_ q n "set" e a)
                 (raise-syntax-error (string->symbol (syntax->datum #'q)) 
                  "Higher-order quantification not supported" stx)]))
  ret)

(define-syntax (Expr stx)
  ;(printf "stx : ~v~n" stx)
  (define ret (syntax-case stx (Quant DeclList Decl NameList CompareOp ArrowOp ExprList QualName
                                      LetDeclList LetDecl)
                [(_ "let" (LetDeclList (LetDecl n e) ...) block) 
                 (syntax/loc stx (let ([n e] ...) block))]
                [(_ "bind" (LetDeclList (LetDecl n e) ...) block) 
                 (syntax/loc stx (bind ([n e] ...) block))]
                [(_ "{" (DeclList (Decl (NameList n) e) ...) block "}") 
                 (syntax/loc stx (set ([n e] ...) block))]

                [(_ (Quant q) (DeclList (Decl (NameList n) e ...)) a)
                 (syntax/loc stx (Q q n e ... a))]
                [(_ (Quant q) (DeclList (Decl (NameList n) e ...) ds ...) a)
                 (syntax/loc stx (Q q n e ... (Expr (Quant q) (DeclList ds ...) a)))]
                [(_ (Quant q) (DeclList (Decl (NameList n ns ...) e ...) ds ...) a)
                 (syntax/loc stx (Q q n e ... (Expr (Quant q) (DeclList (Decl (NameList ns ...) e ...) ds ...) a)))]

                [(_ a "or" b) (syntax/loc stx (or a b))]
                [(_ a "||" b) (syntax/loc stx (or a b))]
                [(_ a "iff" b) (syntax/loc stx (iff a b))]
                [(_ a "<=>" b) (syntax/loc stx (iff a b))]
                [(_ a "implies" b "else" c) (syntax/loc stx (ifte a b c))]
                [(_ a "=>" b "else" c) (syntax/loc stx (ifte a b c))]
                [(_ a "implies" b) (syntax/loc stx (=> a b))]
                [(_ a "=>" b) (syntax/loc stx (=> a b))]
                [(_ a "and" b) (syntax/loc stx (and a b))]
                [(_ a "&&" b) (syntax/loc stx (and a b))]
                [(_ "!" a) (syntax/loc stx (! a))]
                [(_ "not" a) (syntax/loc stx (! a))]
                [(_ a "!" (CompareOp op) b) (syntax/loc stx (! (Expr a (CompareOp op) b)))]
                [(_ a "not" (CompareOp op) b) (syntax/loc stx (! (Expr a (CompareOp op) b)))]
                [(_ a (CompareOp op) b) (quasisyntax/loc stx (#,(sym #'op) a b))]
                [(_ "no" a) (syntax/loc stx (no a))]
                [(_ "some" a) (syntax/loc stx (some a))]
                [(_ "lone" a) (syntax/loc stx (lone a))]
                [(_ "one" a) (syntax/loc stx (one a))]
                [(_ "two" a) (syntax/loc stx (two a))]
                [(_ "set" a) (syntax/loc stx (set a))]
                [(_ a "+" b) (syntax/loc stx (+ a b))]
                [(_ a "-" b) (syntax/loc stx (- a b))]
                [(_ "#" a) (syntax/loc stx (card a))]
                [(_ a "++" b) (syntax/loc stx (++ a b))]
                [(_ a "&" b) (syntax/loc stx (& a b))]
                [(_ a (ArrowOp _ ...) b) (syntax/loc stx (-> a b))]
                [(_ a "<:" b) (syntax/loc stx (<: a b))]
                [(_ a ":>" b) (syntax/loc stx (<: b a))]
                [(_ a "[" (ExprList bs ...) "]") (syntax/loc stx (a bs ...))]
                [(_ a "." b) (syntax/loc stx (join a b))]
                [(_ "~" a) (syntax/loc stx (~ a))]
                [(_ "^" a) (syntax/loc stx (^ a))]
                [(_ "*" a) (syntax/loc stx (* a))]
                [(_ a) (syntax/loc stx a)]))
  ;(printf "ret : ~v~n" ret)
  ret)

(provide Expr1  Expr2  Expr3  Expr4  Expr5  Expr6  Expr7  Expr8
         Expr9  Expr10 Expr11 Expr12 Expr13 Expr14 Expr15 Expr16 Expr17)
(define-syntax-rule (Expr1  x ...) (Expr x ...))
(define-syntax-rule (Expr2  x ...) (Expr x ...))
(define-syntax-rule (Expr3  x ...) (Expr x ...))
(define-syntax-rule (Expr4  x ...) (Expr x ...))
(define-syntax-rule (Expr5  x ...) (Expr x ...))
(define-syntax-rule (Expr6  x ...) (Expr x ...))
(define-syntax-rule (Expr7  x ...) (Expr x ...))
(define-syntax-rule (Expr8  x ...) (Expr x ...))
(define-syntax-rule (Expr9  x ...) (Expr x ...))
(define-syntax-rule (Expr10 x ...) (Expr x ...))
(define-syntax-rule (Expr11 x ...) (Expr x ...))
(define-syntax-rule (Expr12 x ...) (Expr x ...))
(define-syntax-rule (Expr13 x ...) (Expr x ...))
(define-syntax-rule (Expr14 x ...) (Expr x ...))
(define-syntax-rule (Expr15 x ...) (Expr x ...))
(define-syntax-rule (Expr16 x ...) (Expr x ...))
(define-syntax-rule (Expr17 x ...) (Expr x ...))

(define-syntax-rule (Name n) n)
(define-syntax-rule (QualName n) n)
(define-syntax (Number stx)
  (syntax-case stx ()
    [(_ n) (map-stx (lambda (d) (string->number (cadr d))) stx)]))
(define-syntax (Const stx)
  (syntax-case stx ()
    [(_ (Number n)) #'(node/int/constant (Number n))]
    [(_ "-" (Number n)) #'(node/int/constant (* -1 (Number n)))]
    [(_ c) (datum->syntax stx (string->symbol (syntax->datum #'c)))]))

(define-simple-macro (iff a b) (and (=> a b) (=> b a)))
(define-simple-macro (ifte a b c) (and (=> a b) (=> (not a) c)))
(define-simple-macro (>= a b) (or (> a b) (int= a b)))
(define-simple-macro (<= a b) (or (< a b) (int= a b)))
(define-simple-macro (ni a b) (in b a))

(require "server/eval-model.rkt")
(provide make-exact-sbound Bounds make-hash printf)
(define-syntax-rule (bind ([rel expr] ...) block)
  (let ([bind (make-hash)])
    (let ([tups (eval-exp (alloy->kodkod 'expr) bind 8 #f)])
      (instance (make-exact-sbound rel tups))
      (hash-set! bind 'rel tups)
      ) ...
    block))

(define (update-bindings rel lower [upper #f])
  (set! lower (list->set lower))
  (when upper (set! upper (list->set upper)))
  (if (hash-has-key? pbindings rel)
      (let ([old (hash-ref pbindings rel)])
        (set! lower (set-union lower (sbound-lower old)))
        (set! upper (if upper
                        (set-intersect upper (sbound-upper old))
                        (sbound-upper old))))
      (unless upper (begin
        (let* ([uppers (for/list ([type (hash-ref relations-store rel)]) 
                (for/list ([tup (sbound-upper (hash-ref pbindings type))]) (car tup))
              )]
             [cart (list->set (apply cartesian-product uppers))])
          (set! upper cart)))))
  (hash-set! pbindings rel (sbound rel lower upper))
  ;; when exact bounds, put in bindings
  (when (equal? lower upper) 
    (hash-set! bindings (string->symbol (relation-name rel)) (set->list lower))
  )
)
(define (update-bindings-at rel focus lower [upper #f])
  (set! lower (for/set ([tup lower]) (cons focus tup)))
  (when upper (set! upper (for/set ([tup upper]) (cons focus tup))))
  (if (hash-has-key? pbindings rel)
      (let ([old (hash-ref pbindings rel)])
        (set! lower (set-union lower (sbound-lower old)))
        (set! upper (if upper
                        (for/list ([tup (sbound-upper old)] #:when 
                          (or (@not (equal? (car tup) focus))
                              (set-member? upper tup))
                          ) tup)
                        (sbound-upper old))))
      (let* ([uppers (for/list ([type (hash-ref relations-store rel)]) 
                (for/list ([tup (sbound-upper (hash-ref pbindings type))]) (car tup))
              )]
             [cart (list->set (apply cartesian-product uppers))])
        (set! upper (if upper 
                        (for/list ([tup cart] #:when
                          (or (@not (equal? (car tup) focus))
                              (set-member? upper tup))
                          ) tup)
                        cart))))
  (hash-set! pbindings rel (sbound rel lower upper))
  ;; when exact bounds, put in bindings
  (when (equal? lower upper) 
    (hash-set! bindings (string->symbol (relation-name rel)) (set->list lower))
  )
)
(define (rel-is-exact rel) (hash-has-key? bindings (string->symbol (relation-name rel))))

(define-syntax (Bounds stx)
  (define ret (syntax-case stx ()
                  [(_ "exactly" lines ...)
                   #'(begin
                       (Bind lines) ...
                       (set-is-exact))]
                  [(_ lines ...)
                   #'(begin (Bind lines) ...)]))
  ret)
(define-syntax-rule (InstDecl (Name name) (Bounds lines ...))
  (define (name B)
    (Bind lines) ...))
(define-syntax (Bind stx)
  (set! stx (second (syntax-e stx)))
  (define datum (syntax-case stx (CompareOp QualName Const)
                  [(_ "no" rel) (syntax/loc stx (Bind (Expr rel (CompareOp "=") none)))]
                  [(_ "one" rel) 
                   (syntax/loc stx (Bind (Expr (Expr "#" rel) (CompareOp "=") (Expr (Const (Number "1"))))))]
                  [(_ "two" rel) 
                   (syntax/loc stx (Bind (Expr (Expr "#" rel) (CompareOp "=") (Expr (Const (Number "2"))))))]
                  [(_ "lone" rel) 
                   (syntax/loc stx (Bind (Expr (Expr "#" rel) (CompareOp "<=") (Expr (Const (Number "1"))))))]
                  [(_ (_ "#" (_ (QualName rel))) (CompareOp "=") expr) (syntax/loc stx (begin 
                    (define exact (caar (eval-exp (alloy->kodkod 'expr) bindings 8 #f)))
                    (update-int-bound rel (int-bound exact exact)) ))]
                    ;(define dummies (for/list ([i exact]) (list i))) ;; dummy atoms so #rel works
                    ;(update-bindings rel dummies dummies)))]
                  [(_ (_ "#" (_ (QualName rel))) (CompareOp "<=") expr) (syntax/loc stx (begin 
                    (define upper (caar (eval-exp (alloy->kodkod 'expr) bindings 8 #f)))
                    (update-int-bound rel (int-bound 0 upper)) ))]
                    ;(define dummies (for/set ([i upper]) (list i))) ;; dummy atoms so #rel works
                    ;(update-bindings rel (@set) dummies)))]
                  [(_ (_ expr1 (CompareOp "<=") (_ "#" (_ (QualName rel)))) (CompareOp "<=") expr2)
                   (syntax/loc stx (begin 
                    (define lower (caar (eval-exp (alloy->kodkod 'expr1) bindings 8 #f)))
                    (define upper (caar (eval-exp (alloy->kodkod 'expr2) bindings 8 #f)))
                    (update-int-bound rel (int-bound lower upper)) ))]
                    ;(define ldummies (for/set ([i lower]) (list i))) ;; dummy atoms so #rel works
                    ;(define udummies (for/set ([i upper]) (list i))) ;; dummy atoms so #rel works
                    ;(update-bindings rel ldummies udummies)))]
                  [(_ (_ "~" rel) (CompareOp "is") (_ (QualName strat))) 
                   (syntax/loc stx (break rel (get-co 'strat)))]
                  [(_ rel (CompareOp "is") (_ (QualName strat))) (syntax/loc stx (break rel 'strat))]
                  [(_ (QualName f)) (syntax/loc stx (f bindings))]
                  [(_ (_ (QualName rel)) (CompareOp cmp) expr)
                   (syntax/loc stx (let ([tups (eval-exp (alloy->kodkod 'expr) bindings 8 #f)])
                      ;(set! tups (for/list ([tup tups]) (for/list ([e tup]) 
                      ;  (if (int-atom? e) (int-atom-n e) e)
                      ;)))
                      (when (equal? (relation-arity rel) 1)
                        ;; make sure all sub-sigs exactly defined
                        (for ([(sub sup) (in-hash extensions-store)] #:when (equal? sup rel))
                          (unless (rel-is-exact sub)
                            (error 'inst "sub-sig ~a must be exactly specified before super-sig ~a" 
                              (relation-name sub) (relation-name sup))))
                        (let ([exact (length tups)]) (update-int-bound rel (int-bound exact exact)))
                      )
                      (when (equal? cmp "=")  (update-bindings rel tups tups))
                      (when (equal? cmp "in") (update-bindings rel (@set) tups))
                      (when (equal? cmp "ni") (update-bindings rel tups))
                    ))]
                  [(_ (_ (_ (QualName A)) "." (_ (QualName B))) (CompareOp cmp) expr)
                    (syntax/loc stx (let ([tups (eval-exp (alloy->kodkod 'expr) bindings 8 #f)])

                      #| FIXME: this is intentionally wrong to maintain backwards compatibility during
                          the L4S final projects. I accidentally got the join backwards, so the
                          implementation below swaps A and B to do `foc.rel = ...` depending on which
                          of A/B is the relation. This can be fixed after the final as just:

                          (when (equal? cmp "=")  (update-bindings-at B 'A tups tups))
                          (when (equal? cmp "in") (update-bindings-at B 'A (@set) tups))
                          (when (equal? cmp "ni") (update-bindings-at B 'A tups))

                          or `update-bindings-at` can be generalized to allow `rel.foc = ...`
                      |#

                      (define nameA (symbol->string 'A))
                      (define nameB (symbol->string 'B))
                      (define rels (hash-keys relations-store))
                      (define relA (findf (λ (x) (equal? (relation-name x) nameA)) rels))
                      (define relB (findf (λ (x) (equal? (relation-name x) nameB)) rels))
                      (match-define-values (rel foc) (cond
                        [relA (values relA 'B)]
                        [relB (values relB 'A)]
                        [else (error 'inst "one of ~a or ~a must be a relation" 'A 'B)]))

                      (when (equal? cmp "=")  (update-bindings-at rel foc tups tups))
                      (when (equal? cmp "in") (update-bindings-at rel foc (@set) tups))
                      (when (equal? cmp "ni") (update-bindings-at rel foc tups))
                  ))]
                  [(_ (_ (QualName Int)) "[" (_ (_ (Const (Number i)))) "]")
                   (quasisyntax/loc stx (set-bitwidth #,(string->number (syntax-e #'i))))]
                  [(_ a "and" b) (syntax/loc stx (begin (Bind a) (Bind b)))]
                  [x (raise-syntax-error 'inst (format "Not allowed in bounds constraint") stx)]))
  datum)

(define-syntax (two stx)
  (syntax-case stx ()
    [(_ ([v0 e0]) pred) (syntax/loc stx 
     (some ([v0 e0]) (and pred 
      (one ([v1 (- e0 v0)]) (let ([v0 v1]) pred))
     )))]
    [(_ expr) (syntax/loc stx 
     (some ([x expr]) (one (- expr x))))]))
