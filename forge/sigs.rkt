#lang racket

(require (prefix-in @ racket) 
         (prefix-in @ racket/set))
(require syntax/parse/define)
(require racket/match)
(require (for-syntax racket/match syntax/srcloc))

(require "shared.rkt")
(require "lang/ast.rkt"
         "lang/bounds.rkt"
         "breaks.rkt")
(require (only-in "lang/reader.rkt" [read-syntax read-surface-syntax]))
(require "server/eval-model.rkt")
(require "server/forgeserver.rkt") ; v long
(require (prefix-in kodkod: "kodkod-cli/server/kks.rkt")
         (prefix-in kodkod: "kodkod-cli/server/server.rkt")
         (prefix-in kodkod: "kodkod-cli/server/server-common.rkt"))
(require (prefix-in pardinus: "pardinus-cli/server/kks.rkt")
         (prefix-in pardinus: "pardinus-cli/server/server.rkt")
         (prefix-in pardinus: "pardinus-cli/server/server-common.rkt"))
(require "translate-to-kodkod-cli.rkt"
         "translate-from-kodkod-cli.rkt"
         "last-checker.rkt"
         "sigs-structs.rkt")

; Commands
(provide sig relation fun const pred inst)
(provide run check test example display with evaluate)
(provide instance-diff)

; Instance analysis functions
(provide is-sat? is-unsat?)

; export AST macros and struct definitions (for matching)
; Make sure that nothing is double-provided
(provide (all-from-out "lang/ast.rkt"))

; Racket stuff
(provide let quote)

; Technical stuff
(provide set-verbosity VERBOSITY_LOW VERBOSITY_HIGH)
(provide set-path!)
(provide set-option!)
(define (set-path! path) #f)

; Data structures
(provide (prefix-out forge: (struct-out Sig))
         (prefix-out forge: (struct-out Relation))
         (prefix-out forge: (struct-out Range))
         (prefix-out forge: (struct-out Scope))
         (prefix-out forge: (struct-out Bound))
         (prefix-out forge: (struct-out Options))
         (prefix-out forge: (struct-out State))
         (prefix-out forge: (struct-out Run-spec))
         (prefix-out forge: (struct-out Run))         
         (prefix-out forge: (struct-out sbound)))

(provide (prefix-out forge: (all-from-out "sigs-structs.rkt")))


; Export everything for doing scripting
(provide (prefix-out forge: (all-defined-out)))
(provide (prefix-out forge: (struct-out bound)))
(provide (prefix-out forge: relation-name))

(provide (prefix-out forge: curr-state)
         (prefix-out forge: update-state!))

(provide (struct-out Sat)
         (struct-out Unsat))


; get-stdin :: Run -> input-port?
(define (get-stdin run)
  (assert-is-running run)
  (Server-ports-stdin (Run-server-ports run)))

; get-stdin :: Run -> output-port?
(define (get-stdout run)
  (assert-is-running run)
  (Server-ports-stdout (Run-server-ports run)))

; close-run :: Run -> void
(define (close-run run)
  (assert-is-running run)
  ((Server-ports-shutdown (Run-server-ports run))))

; is-running :: Run -> Boolean
(define (is-running? run)
  ((Server-ports-is-running? (Run-server-ports run))))

(define (assert-is-running run)
  (unless (is-running? run)
    (raise "KodKod server is not running.")))

; get-option :: Run-or-state Symbol -> Any
(define (get-option run-or-state option)
  (define state (get-state run-or-state))
  (define symbol->proc
    (hash 'solver Options-solver
          'backend Options-backend
          'sb Options-sb
          'coregranularity Options-coregranularity
          'logtranslation Options-logtranslation
          'min_tracelength Options-min_tracelength
          'max_tracelength Options-max_tracelength
          'problem_type Options-problem_type          
          'target_mode Options-target_mode
          'core_minimization Options-core_minimization
          'skolem_depth Options-skolem_depth
          ))
  ((hash-ref symbol->proc option) (State-options state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; State Updaters  ;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sig-add-extender :: Sig, Symbol -> Sig
; Adds a new extender to the given Sig.
(define (sig-add-extender sig extender)
  (define new-extenders (append (Sig-extenders sig) (list extender)))
  (struct-copy Sig sig
               [extenders new-extenders]))

; state-add-runmap :: State, symbol, Run -> State
(define (state-add-runmap state name r)
  (struct-copy State state
               [runmap (hash-set (State-runmap state) name r)]))

; state-add-sig :: State, Symbol, bool, bool, (Symbol | #f) -> State
; Adds a new Sig to the given State; if new Sig extends some
; other Sig, then updates that Sig with extension.
(define (state-add-sig state name rel one abstract extends)
  (when (member name (State-sig-order state))
    (error (format "tried to add sig ~a, but it already existed" name)))
  (define new-sig (Sig name rel one abstract extends empty))
  (when (@and extends (@not (member extends (State-sig-order state))))
    (raise "Can't extend nonexistent sig."))

  (define sigs-with-new-sig (hash-set (State-sigs state) name new-sig))
  (define new-state-sigs
    (if extends
        (hash-set sigs-with-new-sig extends 
                                    (sig-add-extender (hash-ref (State-sigs state) extends) name))
        sigs-with-new-sig))
  (define new-state-sig-order (append (State-sig-order state) (list name)))

  (struct-copy State state
               [sigs new-state-sigs]
               [sig-order new-state-sig-order]))

; state-add-relation :: State, Symbol, List<Sig>, Symbol?-> State
; Adds a new relation to the given State.
(define (state-add-relation state name rel rel-sigs [breaker #f])
  (when (member name (State-relation-order state))
    (error (format "tried to add relation ~a, but it already existed" name)))
  (define new-relation (Relation name rel rel-sigs breaker))
  (define new-state-relations (hash-set (State-relations state) name new-relation))
  (define new-state-relation-order (append (State-relation-order state) (list name)))
  (struct-copy State state
               [relations new-state-relations]
               [relation-order new-state-relation-order]))

; state-add-pred :: State, Symbol, Predicate -> State
; Adds a new predicate to the given State.
(define (state-add-pred state name pred)
  (define new-state-pred-map (hash-set (State-pred-map state) name pred))
  (struct-copy State state
               [pred-map new-state-pred-map]))

; state-add-fun :: State, Symbol, Function -> State
; Adds a new function to the given State.
(define (state-add-fun state name fun)
  (define new-state-fun-map (hash-set (State-fun-map state) name fun))
  (struct-copy State state
               [fun-map new-state-fun-map]))

; state-add-const :: State, Symbol, Constant -> State
; Adds a new constant to the given State.
(define (state-add-const state name const)
  (define new-state-const-map (hash-set (State-const-map state) name const))
  (struct-copy State state
               [const-map new-state-const-map]))

; state-add-inst :: State, Symbol, Inst -> State
; Adds a new inst to the given State.
(define (state-add-inst state name inst)
  (define new-state-inst-map (hash-set (State-inst-map state) name inst))
  (struct-copy State state
               [inst-map new-state-inst-map]))

(define (set-option! option value)
  (cond [(or (equal? option 'verbosity)
             (equal? option 'verbose))
         (set-verbosity value)]
        [else
         (update-state! (state-set-option curr-state option value))]))

; state-set-option :: State, Symbol, Symbol -> State
; Sets option to value for state.
(define (state-set-option state option value)
  (define options (State-options state))

  (define option-types
    (hash 'solver (lambda (x) (or (symbol? x) (string? x))) ; allow for custom solver path
          'backend symbol?
          ; 'verbosity exact-nonnegative-integer?
          'sb exact-nonnegative-integer?
          'coregranularity exact-nonnegative-integer?
          'logtranslation exact-nonnegative-integer?
          'min_tracelength exact-positive-integer?
          'max_tracelength exact-positive-integer?
          'problem_type symbol?
          'target_mode symbol?
          'core_minimization symbol?
          'skolem_depth exact-integer?))
  (unless ((hash-ref option-types option) value)
    (raise-user-error (format "Setting option ~a requires ~a; received ~a"
                              option (hash-ref option-types option) value)))

  (define new-options
    (cond
      [(equal? option 'solver)
       (struct-copy Options options
                    [solver value])]
      [(equal? option 'backend)
       (struct-copy Options options
                    [backend value])]
      [(equal? option 'sb)
       (struct-copy Options options
                    [sb value])]
      [(equal? option 'coregranularity)
       (struct-copy Options options
                    [coregranularity value])]
      [(equal? option 'logtranslation)
       (struct-copy Options options
                    [logtranslation value])]
      [(equal? option 'min_tracelength)
       (let ([max-trace-length (get-option state 'max_tracelength)])
         (if (@> value max-trace-length)
             (raise-user-error (format "Cannot set min_tracelength to ~a because min_tracelength cannot be greater than max_tracelength. Current max_tracelength is ~a."
                                       value max-trace-length))
             (struct-copy Options options
                          [min_tracelength value])))]
      [(equal? option 'max_tracelength)
       (let ([min-trace-length (get-option state 'min_tracelength)])
         (if (@< value min-trace-length)
             (raise-user-error (format "Cannot set max_tracelength to ~a because max_tracelength cannot be less than min_tracelength. Current min_tracelength is ~a."
                                       value min-trace-length))
             (struct-copy Options options
                          [max_tracelength value])))]
      [(equal? option 'problem_type)
       (struct-copy Options options
                    [problem_type value])]
      [(equal? option 'target_mode)
       (struct-copy Options options
                    [target_mode value])]
      [(equal? option 'core_minimization)
       (struct-copy Options options
                    [core_minimization value])]
      [(equal? option 'skolem_depth)
       (struct-copy Options options
                    [skolem_depth value])]))

  (struct-copy State state
               [options new-options]))

;; Added sugar over the AST
;; It is vital to PRESERVE SOURCE LOCATION in these, or else errors and highlighting may focus on the macro definition point
(provide implies iff <=> ifte >= <= ni != !in !ni)

(define-syntax (implies stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx  (=>/info (nodeinfo #,(build-source-location stx)) a b))]))
(define-syntax (iff stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (&&/info (nodeinfo #,(build-source-location stx))
                                                                (=>/info (nodeinfo #,(build-source-location stx)) a b)
                                                                (=>/info (nodeinfo #,(build-source-location stx)) b a)))]))
(define-syntax (<=> stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (&&/info (nodeinfo #,(build-source-location stx))
                                                                (=>/info (nodeinfo #,(build-source-location stx)) a b)
                                                                (=>/info (nodeinfo #,(build-source-location stx)) b a)))]))

; for ifte, use struct type to decide whether this is a formula (sugar) or expression form (which has its own AST node)
(define-syntax (ifte stx) (syntax-case stx () [(_ a b c) (quasisyntax/loc stx
                                                           (if (node/formula? b)
                                                               (&&/info (nodeinfo #,(build-source-location stx))
                                                                        (=>/info (nodeinfo #,(build-source-location stx)) a b)
                                                                        (=>/info (nodeinfo #,(build-source-location stx)) (! a) c))
                                                               (ite/info (nodeinfo #,(build-source-location stx)) a b c)))]))

(define-syntax (>= stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (||/info (nodeinfo #,(build-source-location stx))
                                                              (int>/info (nodeinfo #,(build-source-location stx)) a b)
                                                              (int=/info (nodeinfo #,(build-source-location stx)) a b)))]))
(define-syntax (<= stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (||/info (nodeinfo #,(build-source-location stx))
                                                              (int</info (nodeinfo #,(build-source-location stx)) a b)
                                                              (int=/info (nodeinfo #,(build-source-location stx)) a b)))]))
(define-syntax (ni stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (in/info (nodeinfo #,(build-source-location stx)) b a))]))
(define-syntax (!= stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (!/info (nodeinfo #,(build-source-location stx))
                                                             (=/info (nodeinfo #,(build-source-location stx)) a b)))]))
(define-syntax (!in stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx  (!/info (nodeinfo #,(build-source-location stx))
                                                              (in/info (nodeinfo #,(build-source-location stx)) a b)))]))
(define-syntax (!ni stx) (syntax-case stx () [(_ a b) (quasisyntax/loc stx (!/info (nodeinfo #,(build-source-location stx))
                                                              (in/info (nodeinfo #,(build-source-location stx)) b a)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; Forge Commands  ;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The environment threaded through commands
(define curr-state init-state)
(define (update-state! new-state) 
  (set! curr-state new-state))

; check-temporal-for-var :: Boolean String -> void
; raises an error if is-var is true and the problem_type option is 'temporal
; uses the given name in the error message
; meant to only allow var sigs and relations in temporal specs
(define (check-temporal-for-var is-var name)
  (cond
    [(and is-var
          (not (equal? (get-option curr-state 'problem_type)
            'temporal)))
     (raise-user-error (format "Can't have var ~a unless problem_type option is temporal"
                               name))]))


; Declare a new sig.
; (sig name [|| [#:one] [#:abstract]] [#:is-var isv] [[|| #:in #:extends] parent])
; Extending a sig with #:in does NOT work yet,
; it's only been added here so that it throws the correct error
; when the Expander tries to do that
(define-syntax (sig stx)
  (syntax-parse stx
    ; This allows #:in and #:extends,
    ; but the parser does not currently allow "sig A in B extends C"
    ; when extendings sigs with in is implemented,
    ; I think they should be updated to be consistent
    [(sig name:id (~alt (~optional (~seq #:in super-sig:expr)) ;check if this supports "sig A in B + C + D ..."
                        (~optional (~seq #:extends parent:expr))
                        (~optional (~or (~seq (~and #:one one-kw))
                                        (~seq (~and #:abstract abstract-kw))))
                        (~optional (~seq #:is-var is-var) #:defaults ([is-var #'#f]))) ...)
    (quasisyntax/loc stx
      (begin
        (define true-name 'name)
        (define true-one (~? (~@ (or #t 'one-kw)) (~@ #f)))
        (define true-abstract (~? (~@ (or #t 'abstract-kw)) (~@ #f)))
        (define true-parent (~? (Sig-name (get-sig curr-state parent))
                                #f))
        (define name (build-relation #,(build-source-location stx)
                                       (list (symbol->string true-name))
                                       (symbol->string (or true-parent 'univ))
                                       (symbol->string true-name)
                                       is-var))
        ;make sure it isn't a var sig if not in temporal mode
        (~@ (check-temporal-for-var is-var true-name))
        ;Currently when lang/expander.rkt calls sig with #:in,
        ;super-sig is #'(raise "Extending with in not yet implemented.")
        ;This is just here for now to make sure that error is raised.
        (~? super-sig)
        (update-state! (state-add-sig curr-state true-name name true-one true-abstract true-parent))))]))

(define-syntax (relation stx)
  (syntax-parse stx
    [(relation name:id (sig1:id sig2:id sigs ...)
               (~optional (~seq #:is breaker:id))
               (~optional (~seq #:is-var is-var) #:defaults ([is-var #'#f])))
     (quasisyntax/loc stx
         (begin
       (define true-name 'name)
       (define true-sigs '(sig1 sig2 sigs ...))
       ; (define true-sigs (map (compose Sig-name ;;; Bugged since relation before sig in #lang forge
       ;                                 (curry get-sig curr-state ))
       ;                        (list sig1 sig2 sigs ...)))
       (define true-breaker (~? 'breaker #f))
       (define name (build-relation #,(build-source-location stx)
                                      (map symbol->string true-sigs)
                                      (symbol->string 'sig1)
                                      (symbol->string true-name)
                                      is-var))
       ;make sure it isn't a var sig if not in temporal mode
        (~@ (check-temporal-for-var is-var true-name))
       (update-state! (state-add-relation curr-state true-name name true-sigs true-breaker))))]))

(begin-for-syntax
  (define-splicing-syntax-class pred-type
    #:description "optional pred flag"
    #:attributes ((seal 0))
    (pattern (~datum wheat)
      #:attr seal #'make-wheat)
    (pattern (~datum chaff)
      #:attr seal #'make-chaff)
    (pattern (~seq)
      #:attr seal #'values)))

; Declare a new predicate
; (pred info name cond ...)
; (pred info (name var ...) cond ...)
;   or same without info
(define-syntax (pred stx)
  (syntax-parse stx
    [(pred t:pred-type name:id conds:expr ...+)
     (quasisyntax/loc stx
       (begin
         ; use srcloc of actual predicate, not this location in sigs
         (define name (t.seal (&&/info (nodeinfo #,(build-source-location stx)) conds ...)))
         (update-state! (state-add-pred curr-state 'name name))))]
    [(pred t:pred-type (name:id args:id ...+) conds:expr ...+)
     (quasisyntax/loc stx
       (begin
         (define (name args ...) (t.seal (&&/info (nodeinfo #,(build-source-location stx)) conds ...)))
         (update-state! (state-add-pred curr-state 'name name))))]))

; Declare a new function
; (fun (name var ...) result)
(define-syntax (fun stx)
  (syntax-parse stx
    [(fun (name:id args:id ...+) result:expr) 
      #'(begin 
        (define (name args ...) result)
        (update-state! (state-add-fun curr-state 'name name)))]))

; Declare a new constant
; (const name value)
(define-syntax (const stx)
  (syntax-parse stx
    [(const name:id value:expr) 
      #'(begin 
        (define name value)
        (update-state! (state-add-const curr-state 'name name)))]))

; Define a new bounding instance
; (inst name binding ...)
(define-syntax (inst stx)
  (syntax-parse stx
    [(inst name:id binds:expr ...)
      #'(begin
        (define (name scope bound)
          (set!-values (scope bound) (bind scope bound binds)) ...
          (values scope bound))
        (update-state! (state-add-inst curr-state 'name name)))]))

; Run a given spec
; (run name
;      [#:pred [(pred ...)]] 
;      [#:scope [((sig [lower 0] upper) ...)]]
;      [#:inst instance-name])
(define-syntax (run stx)
  (define command (format "~a" stx))

  (syntax-parse stx
    [(run name:id
          (~alt
            (~optional (~or (~seq #:preds (preds ...))
                            (~seq #:preds pred)))
            (~optional (~seq #:scope ((sig:id (~optional lower:nat #:defaults ([lower #'0])) upper:nat) ...)))
            (~optional (~or (~seq #:bounds (boundss ...))
                            (~seq #:bounds bound)))
            (~optional (~seq #:solver solver-choice))
            (~optional (~seq #:backend backend-choice))
            (~optional (~seq #:target target-instance))
            (~optional (~seq #:target-distance target-distance))
            (~optional (~or (~and #:target-compare target-compare)
                            (~and #:target-contrast target-contrast)))) ...)
      #`(begin
        (define run-name (~? (~@ 'name) (~@ 'no-name-provided)))
        (define run-state curr-state)
        (define run-preds (~? (list preds ...) (~? (list pred) (list))))

        (~? (set! run-state (state-set-option run-state 'solver 'solver-choice)))
        (~? (set! run-state (state-set-option run-state 'backend 'backend-choice)))
        

        (define sig-scopes (~? 
          (~@
            (for/hash ([name (list (Sig-name (get-sig curr-state sig)) ...)]
                       [lo (list lower ...)]
                       [hi (list upper ...)])
              (values name (Range lo hi))))
          (~@ (hash))))
        (define bitwidth (if (hash-has-key? sig-scopes 'Int)
                             (begin0 (Range-upper (hash-ref sig-scopes 'Int))
                                     (set! sig-scopes (hash-remove sig-scopes 'Int)))
                             #f))
        (define default-sig-scope (if (hash-has-key? sig-scopes 'default)
                                      (begin0 (hash-ref sig-scopes 'default)
                                              (set! sig-scopes (hash-remove sig-scopes 'default)))
                                      #f))
        (define base-scope (Scope default-sig-scope bitwidth sig-scopes))

        (define default-bound
          (let* ([max-int (expt 2 (sub1 (or bitwidth DEFAULT-BITWIDTH)))]
                 [ints (map int-atom (range (- max-int) max-int))]
                 [succs (map list (reverse (rest (reverse ints)))
                                    (rest ints))])
            (Bound (hash)
                   (hash 'Int (map list ints)
                         'succ succs))))
        (define (run-inst scope bounds)
          (for ([sigg (get-sigs run-state)])
            (when (Sig-one sigg)
              (set!-values (scope bounds) (bind scope bounds (one (Sig-rel sigg))))))
          (~? (~@ (set!-values (scope bounds) (bind scope bounds boundss)) ...)
              (~? (set!-values (scope bounds) (bind scope bounds bound))))
          (values scope bounds))
        (define-values (run-scope run-bound)
          (run-inst base-scope default-bound))

        (define run-target 
          (~? (Target (cdr target-instance)
                      (~? 'target-distance 'close))
              #f))
        (~? (unless (member 'target-distance '(close far))
              (raise (format "Target distance expected one of (close, far); got ~a." 'target-distance))))
        (when (~? (or #t 'target-contrast) #f)
          (set! run-preds (~? (list (! (and preds ...))) (~? (list (! pred)) (list false)))))


        (define run-command #,command)        
        
        (define run-spec (Run-spec run-state run-preds run-scope run-bound run-target))        
        (define-values (run-result atoms server-ports kodkod-currents kodkod-bounds) (send-to-kodkod run-spec))
        
        (define name (Run run-name run-command run-spec run-result server-ports atoms kodkod-currents kodkod-bounds))
        (update-state! (state-add-runmap curr-state 'name name)))]))

; Test that a spec is sat or unsat
; (test name
;       [#:preds [(pred ...)]] 
;       [#:scope [((sig [lower 0] upper) ...)]]
;       [#:bounds [bound ...]]
;       [|| sat unsat]))
(define-syntax-rule (test name args ... #:expect expected)
  (cond 
    [(member 'expected '(sat unsat))
     (run name args ...)
     (define first-instance (stream-first (Run-result name)))
     (unless (equal? (if (Sat? first-instance) 'sat 'unsat) 'expected)
       (raise (format "Failed test ~a. Expected ~a, got ~a.~a"
                      'name 'expected (if (Sat? first-instance) 'sat 'unsat)
                      (if (Sat? first-instance)
                          (format ". Found instance ~a" first-instance)
                          ""))))
     (close-run name)]

    [(equal? 'expected 'theorem)
     (check name args ...)
     (define first-instance (stream-first (Run-result name)))

     (when (Sat? first-instance)
       (raise (format "Theorem ~a failed. Found instance:~n~a"
                      'name first-instance)))
     (close-run name)]

    [else (raise (format "Illegal argument to test. Received ~a, expected sat, unsat, or theorem."
                         'expected))]))

(define-simple-macro (example name:id pred bounds ...)
  (test name #:preds [pred]
             #:bounds [bounds ...]
             #:expect sat))

; Checks that some predicates are always true.
; (check name
;        #:preds [(pred ...)]
;        [#:scope [((sig [lower 0] upper) ...)]]
;        [#:bounds [bound ...]]))
(define-syntax (check stx)
  (syntax-parse stx
    [(check name:id
            (~alt
              (~optional (~seq #:preds (pred ...)))
              (~optional (~seq #:scope ((sig:id (~optional lower:nat #:defaults ([lower #'0])) upper:nat) ...)))
              (~optional (~seq #:bounds (bound ...)))) ...)
     #'(run name (~? (~@ #:preds [(! (and pred ...))]))
                 (~? (~@ #:scope ([sig lower upper] ...)))
                 (~? (~@ #:bounds (bound ...))))]))


; Exprimental: Run in the context of a given external Forge spec
; (with path-to-forge-spec commands ...)
(define-syntax (with stx)
  (syntax-parse stx
    [(with (ids:id ... #:from module-name) exprs ...+)
      #'(let ([temp-state curr-state])
          (define ids (unseal-node/formula (dynamic-require module-name 'ids))) ...
          (define result
            (let () exprs ...))
          (update-state! temp-state)
          result)]))

; TODO: instance isn't used
;  always evaluates with respect to solver's current state
(define (evaluate run instance expression)
  (unless (is-sat? run)
    (raise (format "Can't evaluate on unsat run. Expression: ~a" expression)))
  (define-values (expr-name interpretter)
    (cond [(node/expr? expression) 
           (define currents (Run-kodkod-currents run))
           (define expression-number (Kodkod-current-expression currents)) 
           (set-Kodkod-current-expression! currents (add1 expression-number))
           (values (pardinus:e expression-number)
                   interpret-expr)]
          [(node/formula? expression)
           (define currents (Run-kodkod-currents run))
           (define formula-number (Kodkod-current-formula currents)) 
           (set-Kodkod-current-formula! currents (add1 formula-number))
           (values (pardinus:f formula-number)
                   interpret-formula)]
          [(node/int? expression)
           (define currents (Run-kodkod-currents run))
           (define int-number (Kodkod-current-int currents)) 
           (set-Kodkod-current-int! currents (add1 int-number))
           (values (pardinus:i int-number)
                   interpret-int)]
          [else
           (error (format "Forge: unexpected input type to evaluate: ~a" expression))]))

  (define all-rels (get-all-rels run))
  (define atom-names (Run-atoms run))

  (pardinus:cmd 
    [(get-stdin run)]
    (pardinus:print-cmd-cont "(~a " expr-name)
    (interpretter run expression all-rels atom-names '())
    (pardinus:print-cmd ")")
    (pardinus:print-cmd "(evaluate ~a)" expr-name)
    (pardinus:print-eof))

  (define run-atoms (Run-atoms run))
  (translate-evaluation-from-kodkod-cli (pardinus:read-evaluation (get-stdout run)) run-atoms))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; Result Functions ;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is-sat? :: Run -> boolean
; Checks if a given run result is 'sat
(define (is-sat? run)
  (define first-instance (stream-first (Run-result run)))
  (Sat? first-instance))

; is-unsat? :: Run -> boolean
; Checks if a given run result is 'unsat
(define (is-unsat? run)
  (define first-instance (stream-first (Run-result run)))
  (Unsat? first-instance))

; make-model-generator :: Stream<model> -> (-> model)
; Creates a thunk which generates a new model on each call.
(define (make-model-generator model-stream)
  (thunk
    (define ret (stream-first model-stream))
    (set! model-stream (stream-rest model-stream))
    ret))

; ; make-model-evaluator :: Run -> (String -> ???)
; ; Creates an evaluator function for a given Run. 
; ; Executes on the most recently generated instance.
; (define (make-model-evaluator run)
;   (lambda (command)
;     (define name (substring command 1 3))
;     (cmd [(stdin)] 
;       (print-cmd command)
;       (print-cmd "(evaluate ~a)" name)
;       (print-eof))
;     (define result (read (stdout)))
;     result))
;     ; (define u (read (open-input-string command)))
;     ; (println u)
;     ; u))

(provide (prefix-out forge: nsa))
(define nsa (make-parameter #f))
; display :: Run -> void
; Lifted function which, when provided a Run,
; generates a Sterling instance for it.
(define (display arg1 [arg2 #f])
  (if (@not (Run? arg1))
      (if arg2 (@display arg1 arg2) (@display arg1))
      (let ()
        (define run arg1)
        (define model-stream (Run-result run))
        (define get-next-model (make-model-generator model-stream))
        (define (evaluate-str str-command)
          (define pipe1 (open-input-string str-command))
          (define pipe2 (open-input-string (format "eval ~a" str-command)))

          (with-handlers ([(lambda (x) #t) 
                           (lambda (exn) (exn-message exn))])
            ; Read command as syntax from pipe
            (define expr
              (with-handlers ([(lambda (x) #t) (lambda (exn) 
                               (read-syntax 'Evaluator pipe1))])
                (last (syntax->datum (read-surface-syntax 'Evaluator pipe2)))))

            ; Evaluate command
            (define full-command (datum->syntax #f `(let
              ,(for/list ([atom (Run-atoms run)]
                          #:when (symbol? atom))
                 `[,atom (atom ',atom)])
                 ,expr)))
            (define ns (namespace-anchor->namespace (nsa)))
            (define command (eval full-command ns))
            (evaluate run '() command)))

        (define (get-contrast-model-generator model compare distance)
          (unless (member distance '(close far))
            (raise (format "Contrast model distance expected one of ('close, 'far); got ~a" distance)))
          (unless (member compare '(compare contrast))
            (raise (format "Contrast model compare expected one of ('compare, 'contrast); got ~a" compare)))

          (define new-state 
            (let ([old-state (get-state run)])
              (state-set-option (state-set-option old-state 'backend 'pardinus)
                                'solver 'TargetSATSolver)))
          (define new-preds
            (if (equal? compare 'compare)
                (Run-spec-preds (Run-run-spec run))
                (list (! (foldr (lambda (a b) (and a b))
                                  true
                                  (Run-spec-preds (Run-run-spec run)))))))
          
          (define new-target
            (if (Unsat? model) ; if satisfiable, move target
                (Run-spec-target (Run-run-spec run))
                (Target
                 (for/hash ([(key value) (first (Sat-instances model))]
                            #:when (member key (append (map Sig-rel (get-sigs new-state))
                                                       (map Relation-rel (get-relations new-state)))))
                   (values key value))
                 distance)))

          (define contrast-run-spec
            (struct-copy Run-spec (Run-run-spec run)
                         [preds new-preds]
                         [target new-target]
                         [state new-state]))
          (define-values (run-result atom-rels server-ports kodkod-currents kodkod-bounds) (send-to-kodkod contrast-run-spec))
          (define contrast-run 
            (struct-copy Run run
                         [name (string->symbol (format "~a-contrast" (Run-name run)))]
                         [run-spec contrast-run-spec]
                         [result run-result]
                         [server-ports server-ports]
                         [kodkod-currents kodkod-currents]))
          (make-model-generator (get-result contrast-run)))

        (display-model get-next-model 
                       (get-relation-map run)
                       evaluate-str
                       (Run-name run) 
                       (Run-command run) 
                       "/no-name.rkt" 
                       (get-bitwidth
                         (Run-run-spec run)) 
                       empty
                       get-contrast-model-generator))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; Scope/Bound Updaters ;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; set-bitwidth :: Scope, int -> Scope
; Updates the bitwidth for the given Scope.
(define (set-bitwidth scope n)
  (struct-copy Scope scope
               [bitwidth n]))

; update-int-bound :: Scope, node/expr/relation, Range -> Scope
; Updates the scope (range) for a given sig in scope.
(define (update-int-bound scope rel given-scope)
  (define name (string->symbol (relation-name rel)))
  (define old-scope (get-scope scope name))

  (define lower (@max (Range-lower given-scope) (Range-lower old-scope)))
  (define upper (@min (Range-upper given-scope) (Range-upper old-scope)))
  (when (@< upper lower)
    (raise "Bound conflict."))

  (define new-scope (Range lower upper))
  (define new-sig-scopes (hash-set (Scope-sig-scopes scope) name new-scope))

  (struct-copy Scope scope
               [sig-scopes new-sig-scopes]))

; update-bindings :: Bound, node/expr/relation, List<Symbol>, List<Symbol>? -> Bound
; Updates the partial binding for a given sig or relation.
; If a binding already exists, takes the intersection.
; If this results in an exact bound, adds it to the total bounds.
(define (update-bindings bound rel lower [upper #f])
  (set! lower (list->set lower))
  (when upper (set! upper (list->set upper)))

  (define old-pbindings (Bound-pbindings bound))
  (define old-tbindings (Bound-tbindings bound))

  ; New bindings can only strengthen old ones
  (when (hash-has-key? old-pbindings rel)
    (let ([old (hash-ref old-pbindings rel)])
      (set! lower (set-union lower (sbound-lower old)))
      (set! upper (cond [(@and upper (sbound-upper old))
                         (set-intersect upper (sbound-upper old))]
                        [else (@or upper (sbound-upper old))]))))
  

  (unless (@or (@not upper) (subset? lower upper))
    (raise "Bound conflict."))

  (define new-pbindings
    (hash-set old-pbindings rel (sbound rel lower upper)))

  ; when exact bounds, put in bindings
  (define new-tbindings 
    (if (equal? lower upper) 
        (hash-set old-tbindings (string->symbol (relation-name rel)) 
                                (set->list lower))
        old-tbindings))

  (define new-bound (Bound new-pbindings new-tbindings))
  new-bound)

; update-bindings-at :: Bound, node/expr/relation, node/expr/relation, 
;                       List<Symbol>, List<Symbol>? 
;                         -> Bound
; To be implemented.
; Updates the partial binding for a given focused relation.
; Example use is (ni (join Thomas mentors) (+ Tim Shriram)).
; (define (update-bindings-at bound rel foc lower [upper #f])
;   scope)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;  Bound Declarations  ;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (bind scope bound bind-expression)
(define-syntax (bind stx)
  (match-define (list b scope bound binding) (syntax-e stx))
  (syntax-parse binding #:datum-literals (no one two lone <= = card is ~ join Int CompareOp QualName Const)
    
    ; Cardinality bindings
    [(no rel) #`(bind #,scope #,bound (= rel none))]
    [(one rel) #`(bind #,scope #,bound (= (card rel) 1))]
    [(two rel) #`(bind #,scope #,bound (= (card rel) 2))]
    [(lone rel) #`(bind #,scope #,bound (<= (card rel) 1))]

    [(= (card rel) n)
     #`(let* ([exact (eval-int-expr 'n (Bound-tbindings #,bound) 8)]
              [new-scope (update-int-bound #,scope rel (Range exact exact))])
         (values new-scope #,bound))]

    [(<= (card rel) upper)
     #`(let* ([upper-val (eval-int-expr 'upper (Bound-tbindings #,bound) 8)]
              [new-scope (update-int-bound #,scope rel (Range 0 upper-val))])
         (values new-scope #,bound))]

    [(<= lower (card rel) upper)
     #`(let* ([lower-val (eval-int-expr 'lower (Bound-tbindings #,bound) 8)]
              [upper-val (eval-int-expr 'upper (Bound-tbindings #,bound) 8)]
              [new-scope (update-int-bound #,scope rel (Range lower-val upper-val))])
         (values new-scope #,bound))]

    ; Strategies
    [(is (~ rel) strat)
     #`(begin
       (break rel (get-co 'strat))
       (values #,scope #,bound))]

    [(is rel strat)
     #`(begin
       (break rel 'strat)
       (values #,scope #,bound))]

    ; Other instances
    [f:id #`(f #,scope #,bound)]

    ; Particular bounds
    [(cmp rel expr)
     #:fail-unless (member (syntax->datum #'cmp) '(= in ni)) "expected a comparator"
     #`(let ([tups (eval-exp 'expr (Bound-tbindings #,bound) 8 #f)]) ; LOOK HERE
         (define new-scope #,scope)
           ; (if (@not (equal? (relation-arity rel) 1))
           ;     #,scope
           ;     (begin
           ;       ;; make sure all sub-sigs exactly defined
           ;       ; (for ([(sub sup) (in-hash extensions-store)] #:when (equal? sup rel))
           ;       ;   (unless (rel-is-exact sub)
           ;       ;           (error 'inst "sub-sig ~a must be exactly specified before super-sig ~a" 
           ;       ;                  (relation-name sub) (relation-name sup))))
           ;       (let ([exact (length tups)]) 
           ;         (update-int-bound #,scope rel (Range exact exact))))))

         (define new-bound (cond
           [(equal? 'cmp '=)  (update-bindings #,bound rel tups tups)]
           [(equal? 'cmp 'in) (update-bindings #,bound rel (@set) tups)]
           [(equal? 'cmp 'ni) (update-bindings #,bound rel tups)]))

         (values new-scope new-bound))]

    ; [(cmp (join foc rel) expr)
    ;  #`(let ([tups (eval-exp (alloy->kodkod 'expr) bindings 8 #f)])
    ;      (define new-bound (cond
    ;        [(equal? 'cmp '=)  (update-bindings-at #,bound rel 'foc tups tups)]
    ;        [(equal? 'cmp 'in) (update-bindings-at #,bound rel 'foc (@set) tups)]
    ;        [(equal? 'cmp 'ni) (update-bindings-at #,bound rel 'foc tups)]))
    ;      (values #,scope new-bound))]

    ; Bitwidth
    [(Int n:nat)
     #'(values (set-bitwidth #,scope n) #,bound)]

    [x (raise-syntax-error 'inst (format "Not allowed in bounds constraint") binding)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;    Run Logic    ;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; send-to-kodkod :: Run-spec -> Stream<model>, List<Symbol>
; Given a Run-spec structure, processes the data and communicates it to KodKod-CLI;
; then produces a stream to produce instances generated by KodKod, 
; along with a list of all of the atom names for sig atoms.
(define (send-to-kodkod run-spec)
  ; Do relation breaks from declarations
  (define relation-constraints 
    (apply append
           (for/list ([relation (get-relations run-spec)])
             (match (Relation-breaker relation)
               [#f (list)]
               ['default (list)]
               ['pfunc (let* ([rel (Relation-rel relation)]
                              [sigs (Relation-sigs relation)]
                              [left-sig (get-sig run-spec (first sigs))]
                              [sig-rel (Sig-rel left-sig)])
                         (list (all ([s sig-rel])
                                 (lone (join s rel)))))]
               [other (break (Relation-rel relation) other)
                      (list)]))))

  ; Insert missing upper bounds of partial bindings
  (define pbindings (Bound-pbindings (Run-spec-bounds run-spec)))
  (define fixed-sigs
    (for/hash ([(rel pbinding) (in-hash pbindings)])      
      (match-define (sbound rel lower upper) pbinding)
      (when (@and (@= (relation-arity rel) 1) (@not upper))
        (define sig (get-sig run-spec (string->symbol (relation-name rel))))
        (define sig-scope (get-scope run-spec sig))
        (define new-atoms (range (set-count lower) (Range-upper sig-scope)))
        (define new-names (map (lambda (n) (list (string->symbol (format "~a~a" (Sig-name sig) n)))) new-atoms))
        (define new-upper (set-union lower (list->set new-names)))
        (set! upper new-upper))
      (values rel (sbound rel lower upper))))
  
  (define fixed-relations
    (for/hash ([(rel pbinding) (in-hash fixed-sigs)])
      (match-define (sbound rel lower upper) pbinding)
      (when (@and (@> (relation-arity rel) 1) (@not upper))
        (define relation (get-relation run-spec (string->symbol (relation-name rel))))
        (define types (get-sigs run-spec relation))
        (define type-uppers (map (compose set->list
                                          sbound-upper
                                          (curry hash-ref fixed-sigs ))
                                 types))
        (define new-upper (list->set (apply cartesian-product type-uppers)))
        (set! upper new-upper))
      (values rel (sbound rel lower upper))))
  
  (set! pbindings fixed-relations)
  ; Send user defined partial bindings to breaks
  (map instance (hash-values pbindings))

  (define tbindings 
    (let* ([init-tbindings (Bound-tbindings (Run-spec-bounds run-spec))]
           [fixed-init-tbindings (hash-remove (hash-remove init-tbindings 'Int) 'succ)])
      (for/fold ([tbindings fixed-init-tbindings])
                ([(rel sb) (in-hash pbindings)])
        ; this nonsense is just for atom names
        (define name (string->symbol (relation-name rel)))
        (hash-set tbindings name (for/list ([tup (sbound-upper sb)]) (car tup))))))

  ; Get KodKod names, min sets, and max sets of Sigs and Relations
  (define-values (sig-to-bound all-atoms) ; Map<Symbol, bound>, List<Symbol>
    (get-sig-bounds run-spec tbindings))

  (define relation-to-bound ; Map<Symbol, bound>
    (get-relation-bounds run-spec sig-to-bound))
  
  ; Get new bounds and constraints from breaks
  (define-values (total-bounds break-preds)
    (let* ([sig-bounds (map (compose (curry hash-ref sig-to-bound )
                                     Sig-name)
                            (get-sigs run-spec))]
           [relation-bounds (map (compose (curry hash-ref relation-to-bound )
                                          Relation-name)
                                 (get-relations run-spec))]
           [total-bounds (append sig-bounds relation-bounds)]
           [sigs (get-sigs run-spec)]
           [sig-rels (map Sig-rel (filter (lambda (sig) (@not (equal? (Sig-name sig) 'Int))) sigs))]
           [upper-bounds (for/hash ([sig sigs]) 
                           (values (Sig-rel sig) 
                                   (map car (bound-upper (hash-ref sig-to-bound (Sig-name sig))))))]
           [relations-store (for/hash ([relation (get-relations run-spec)]
                                       #:unless (equal? (Relation-name relation) 'succ))
                              (values (Relation-rel relation) (map Sig-rel (get-sigs run-spec relation))))]
           [extensions-store (for/hash ([sig sigs]
                                        #:when (Sig-extends sig))
                               (values (Sig-rel sig) (Sig-rel (get-sig run-spec (Sig-extends sig)))))])
      (constrain-bounds total-bounds sig-rels upper-bounds relations-store extensions-store)))
  (clear-breaker-state)

  (define sigs-and-rels
    (append (State-sig-order (Run-spec-state run-spec))
            (State-relation-order (Run-spec-state run-spec))))
  (set! total-bounds (map (lambda (name) 
                            (findf (lambda (b) 
                                     (equal? name (string->symbol (relation-name (bound-relation b)))))
                                   total-bounds)) 
                          sigs-and-rels))

  (when (@>= (get-verbosity) VERBOSITY_DEBUG)
    (displayln "--------------------------")
    (printf "Original PBindings: ~n~a~n~n" (Bound-pbindings (Run-spec-bounds run-spec)))
    (printf "Fixed PBindings: ~n~a~n~n" pbindings)
    (printf "Original TBindings: ~n~a~n~n" (Bound-tbindings (Run-spec-bounds run-spec)))
    (printf "Fixed TBindings: ~n~a~n~n" tbindings)
    (printf "sig-to-bound: ~n~a~n~n" sig-to-bound)
    (printf "relation-to-bound: ~n~a~n~n" relation-to-bound)
    (printf "all-atoms: ~n~a~n~n" all-atoms)
    (printf "total-bounds: ~n~a~n~n" total-bounds)
    (displayln "--------------------------"))


  #| Print to KodKod-CLI
    print configure
    declare univ size
    declare ints
    print Int sig (r0)
    print other sigs (r2 ... rm)
    print succ relation (r(m + 1))
    print other relations (r(m + 2) ... rn)
    print formula / assert formula (f0 ... fk)
    print solve
  |#

  ; Initializing our kodkod-cli process, and getting ports for communication with it
  (define backend (get-option run-spec 'backend))
  (define-values (stdin stdout shutdown is-running?) 
    (cond
      [(equal? backend 'kodkod)
       (kodkod:start-server)]
      [(equal? backend 'pardinus)
       (pardinus:start-server
        'stepper
        (Target? (Run-spec-target run-spec))
        (equal? 'temporal (get-option run-spec 'problem_type)))]
      [else (raise (format "Invalid backend: ~a" backend))]))

  (define-syntax-rule (kk-print lines ...)
    (kodkod:cmd 
      [stdin]
      lines ...))

  ; Print targets
  (define-syntax-rule (pardinus-print lines ...)
    (pardinus:cmd 
      [stdin]
      lines ...))

  ; Confirm that if the user is invoking a custom solver, that custom solver exists
  (define solverspec (cond [(symbol? (get-option run-spec 'solver))
                            (get-option run-spec 'solver)]
                           [else (string-append "\"" (get-option run-spec 'solver) "\"")]))
  (unless (or (symbol? (get-option run-spec 'solver))
              (file-exists? (get-option run-spec 'solver)))
    (raise-user-error (format "option solver specified custom solver (via string): ~a, but file did not exist." 
                              (get-option run-spec 'solver))))
  
  ; Print configure and declare univ size
  ; Note that target mode is passed separately, nearer to the (solve) invocation
  (define bitwidth (get-bitwidth run-spec)) 
  (pardinus-print
    (pardinus:configure (format ":bitwidth ~a :solver ~a :max-solutions 1 :verbosity 7 :skolem-depth ~a :sb ~a :core-gran ~a :core-minimization ~a :log-trans ~a ~a ~a"
                               bitwidth 
                               solverspec
                               (get-option run-spec 'skolem_depth)
                               (get-option run-spec 'sb) 
                               (get-option run-spec 'coregranularity)
                               (get-option run-spec 'core_minimization)
                               (get-option run-spec 'logtranslation)
                               (if (equal? 'temporal (get-option run-spec 'problem_type))
                                   (format ":min-trace-length ~a" (get-option run-spec 'min_tracelength))
                                   "")
                               (if (equal? 'temporal (get-option run-spec 'problem_type))
                                   (format ":max-trace-length ~a" (get-option run-spec 'max_tracelength))
                                   "")))
    (pardinus:declare-univ (length all-atoms)))

  ; Declare ints
  (define num-ints (expt 2 bitwidth))
  (pardinus-print
    (pardinus:declare-ints (range (- (/ num-ints 2)) (/ num-ints 2)) ; ints
                         (range num-ints)))                        ; indexes

  ; to-tupleset :: List<List<int>>, int -> tupleset
  (define (to-tupleset arity eles)
    (if (empty? eles)
        (if (@= arity 1)
            'none
            (pardinus:product 'none (to-tupleset (sub1 arity) eles)))
        (pardinus:tupleset #:tuples eles)))

  (define (get-atoms rel atom-names)
    (define atoms 
      (for/list ([tup atom-names])
        (for/list ([atom tup])
          ; Used to allow using ints in instances.
          (when (int-atom? atom)
            (set! atom (int-atom-n atom)))

          (unless (member atom all-atoms)
            (raise (format "atom (~a) not in all-atoms (~a)"
                           atom all-atoms)))
          (index-of all-atoms atom))))
    (define ret (to-tupleset (relation-arity rel) atoms))
    ret)

  (for ([rel (get-all-rels run-spec)]
        [bound total-bounds])    
    (pardinus-print
      (pardinus:declare-rel
       (if (node/expr/relation-is-variable rel)
           (pardinus:x (relation-name rel))
           (pardinus:r (relation-name rel)))
        (get-atoms rel (bound-lower bound))
        (get-atoms rel (bound-upper bound)))))

  ; Declare assertions
  (define all-rels (get-all-rels run-spec))

  (define (maybe-alwaysify fmla)
    (if (equal? 'temporal (get-option run-spec 'problem_type))
        (always/info (node-info fmla) fmla)
        fmla))
  
  ; Get and print predicates
  ; If in temporal mode, need to always-ify the auto-generated constraints but not the
  ;   predicates that come from users
  (define raw-implicit-constraints
    (append (get-sig-size-preds run-spec total-bounds)
            (get-relation-preds run-spec)
            (get-extender-preds run-spec)
            relation-constraints
            break-preds))
  (define conjuncts-implicit-constraints
    (apply append (map maybe-and->list raw-implicit-constraints)))
  (define implicit-constraints
    (map maybe-alwaysify conjuncts-implicit-constraints))
  (define explicit-constraints
    (apply append (map maybe-and->list (Run-spec-preds run-spec)))) 
              
  (define run-constraints 
    (append explicit-constraints implicit-constraints))

  ; Run last-minute checks for errors  
  (for-each (lambda (c) (checkFormula run-spec c '())) run-constraints) 
  
  (for ([p run-constraints]
        [assertion-number (in-naturals)])
    (pardinus-print
      (pardinus:print-cmd-cont "(~a " (pardinus:f assertion-number))
      (translate-to-kodkod-cli run-spec p all-rels all-atoms '())
      (pardinus:print-cmd ")")
      (pardinus:assert (pardinus:f assertion-number))))

  (define target (Run-spec-target run-spec))
  (when target
    (for ([(rel-name atoms) (Target-instance target)])
      (define relation (hash-ref (get-relation-map run-spec) (symbol->string rel-name)))
      (define sig-or-rel
        (if (@= (relation-arity relation) 1)
            (get-sig run-spec relation)
            (get-relation run-spec relation)))

      (pardinus-print
        (pardinus:declare-target 
          (pardinus:r (relation-name relation))
          (get-atoms relation atoms))))

    (pardinus-print
      (pardinus:print-cmd "(target-option target-mode ~a)" (Target-distance target))))

  (define (format-statistics stats)
    (let* ([vars (assoc 'size-variables stats)]
           [prim (assoc 'size-primary stats)]
           [clauses (assoc 'size-clauses stats)]
           [tt (assoc 'time-translation stats)]
           [ts (assoc 'time-solving stats)]
           [tcx (assoc 'time-core stats)]
           [tcstr (if tcx (format " Core min (ms): ~a" tcx) "")])
      (format "#vars: ~a; #primary: ~a; #clauses: ~a~nTransl (ms): ~a; Solving (ms): ~a~a"
              vars prim clauses tt ts tcstr)))
  
  ; Print solve
  (define (get-next-model)
    (unless (is-running?)
      (raise "KodKod server is not running."))
    (pardinus-print (pardinus:solve))
    (define result (translate-from-kodkod-cli
                    'run 
                    (pardinus:read-solution stdout) 
                    all-rels 
                    all-atoms))    
    (when (@>= (get-verbosity) VERBOSITY_LOW)
      (displayln (format-statistics (if (Sat? result) (Sat-stats result) (Unsat-stats result)))))
    result)

  (define (model-stream [prev #f])
    (if (and prev
             (Unsat? prev))
        (letrec ([rest (stream-cons (prev) rest)])
          rest)
        (stream-cons (get-next-model) (model-stream))))

  (values (model-stream) 
          all-atoms 
          (Server-ports stdin stdout shutdown is-running?) 
          (Kodkod-current (length run-constraints) 0 0) 
          total-bounds))

; get-sig-info :: Run-spec -> Map<Symbol, bound>, List<Symbol>
; Given a Run-spec, assigns names to each sig, assigns minimum and maximum 
; sets of atoms for each, and find the total number of atoms needed (including ints).
(define (get-sig-bounds run-spec tbindings)

  ; Map<Symbol, int>
  (define curr-atom-number (make-hash))
  ; Sig -> Symbol
  (define (get-next-name sig)
    (define atom-number (add1 (hash-ref curr-atom-number (Sig-name sig) -1)))    
    (hash-set! curr-atom-number (Sig-name sig) atom-number)
    (define default-name (string->symbol (format "~a~a" (Sig-name sig) atom-number)))
;    (if (hash-has-key? tbindings (Sig-name sig))
;        (let ([bind-names (hash-ref tbindings (Sig-name sig))])                 
;          (if (@< atom-number (length bind-names))
;              (list-ref bind-names atom-number)
;              (if (member default-name bind-names) ; Avoid clash with user atom names
;                  (get-next-name sig)
;                  default-name)))          
        default-name)
  ;)
  
  ; Sig, int -> List<Symbol>
  ; TN changed this to always use the *lowest* unused atom names first
  ;   this matters if we're manufacturing an instance I2 from an instance I1 and the bounds
  ;   need to be identical regardless of how many of a given sig appeared in I1.
  (define (get-next-names sig num)
    (define bind-names (if (hash-has-key? tbindings (Sig-name sig))
                           (hash-ref tbindings (Sig-name sig))  ; user-defined names    
                           empty))
    (define default-names (for/list ([_ (range num)]) (get-next-name sig)))
    (define new-names (remove* bind-names default-names)) ; (remove* v-lst lst) removes from lst every element of v-lst
    (define n-new-needed (- num (length bind-names)))
    ;(printf "get-next-names; num=~a, bind-names: ~a, default-names: ~a, new-names: ~a, n-new-needed ~a~n"
    ;        num bind-names default-names new-names n-new-needed)
    (append bind-names (if (@> n-new-needed 0) (take new-names n-new-needed) empty)))

  ; Map<Symbol, List<Symbol>
  (define sig-to-lower (make-hash))
  ; Sig -> List<Symbol>
  (define (fill-lower sig)
    (define own-lower-int (Range-lower (get-scope run-spec sig)))
    (define children-lower (apply append (map fill-lower (get-children run-spec sig))))

    (define own-lower
      (let ([difference (@- own-lower-int (length children-lower))])
        (if (@> difference 0)
            (append (get-next-names sig difference) children-lower)
            children-lower)))

    (hash-set! sig-to-lower (Sig-name sig) own-lower)
    own-lower)

  ; Map<Symbol, List<List<Symbol>>
  (define sig-to-upper (make-hash))
  ; Sig, List<Symbol>? -> List<Symbol>
  (define (fill-upper-top sig)
    (define own-upper-int (Range-upper (get-scope run-spec sig)))
    (define own-lower (hash-ref sig-to-lower (Sig-name sig)))
    (define difference (@- own-upper-int (length own-lower)))    
    (when (@< difference 0)
      (raise (format "Illegal bounds for sig ~a" (Sig-name sig))))

    (define new-names (get-next-names sig difference))
    (define own-upper (append own-lower new-names))
    (hash-set! sig-to-upper (Sig-name sig) own-upper)

    (for ([child (get-children run-spec sig)]) (fill-upper-extender child own-upper))
    own-upper)

  (define (fill-upper-extender sig upper)
    (hash-set! sig-to-upper (Sig-name sig) upper)
    (for ([child (get-children run-spec sig)]) (fill-upper-extender child upper)))

  (define int-atoms
    (let* ([bitwidth (get-bitwidth run-spec)]
           [max-int (expt 2 (sub1 bitwidth))])
      (range (- max-int) max-int)))
  (hash-set! sig-to-lower 'Int int-atoms)
  (hash-set! sig-to-upper 'Int int-atoms)

  ; Start: Used to allow extending Ints.
  (for ([sig (get-children run-spec Int)])
    (hash-set! sig-to-lower (Sig-name sig) '())
    (hash-set! sig-to-upper (Sig-name sig) int-atoms))
  ; End: Used to allow extending Ints.

  (define top-level-sigs (get-top-level-sigs run-spec))
  
  (define sig-atoms (apply append
    (for/list ([sig top-level-sigs] 
               #:unless (equal? (Sig-name sig) 'Int))
      (fill-lower sig)
      (fill-upper-top sig))))

  (define all-atoms (append int-atoms sig-atoms))

  ; Map<Symbol, bound>
  (define bounds-hash
    (for/hash ([sig (get-sigs run-spec)])
      (let* ([name (Sig-name sig)]
             [rel (Sig-rel sig)]
             [lower (map list (hash-ref sig-to-lower name))]
             [upper (map list (hash-ref sig-to-upper name))])
        (values name (bound rel lower upper)))))

  (values bounds-hash all-atoms))

; get-relation-info :: Run-spec -> Map<Symbol, bound>
; Given a Run-spec, the atoms assigned to each sig, the atoms assigned to each name,
; and the starting relation name, assigns names to each relation
; and minimum and maximum sets of atoms for each relation.
(define (get-relation-bounds run-spec sig-to-bound)
  (define without-succ
    (for/hash ([relation (get-relations run-spec)]
               #:unless (equal? (Relation-name relation) 'succ))
      (define sigs (get-sigs run-spec relation))
      (define sig-atoms (map (compose (curry map car )
                                      bound-upper
                                      (curry hash-ref sig-to-bound )
                                      Sig-name) 
                             sigs))
      (define upper (apply cartesian-product sig-atoms))
      (define lower empty)
      (values (Relation-name relation) 
              (bound (Relation-rel relation) lower upper))))
  (define ints (map car (bound-upper (hash-ref sig-to-bound 'Int))))
  (define succ-tuples (map list (reverse (rest (reverse ints))) (rest ints)))
  (hash-set without-succ 'succ (bound succ succ-tuples succ-tuples)))

; get-sig-size-preds :: Run-spec -> List<node/formula>
; Creates assertions for each Sig to restrict
; it to the correct lower/upper bound.
(define (get-sig-size-preds run-spec total-bounds) 
  (define max-int (expt 2 (sub1 (get-bitwidth run-spec))))
  (apply append
    (for/list ([sig (get-sigs run-spec)]
               #:unless (equal? (Sig-name sig) 'Int))
      (match-define (Range int-lower int-upper) (get-scope run-spec sig))
      
      (append
        (if (equal? int-lower 0)
            (list)
            (let ()
              (unless (@< int-lower max-int)
                (raise (format (string-append "Lower bound too large for given BitWidth; "
                                              "Sig: ~a, Lower-bound: ~a, Max-int: ~a")
                               sig int-lower (sub1 max-int))))
              (list (<= (int int-lower) (card (Sig-rel sig))))))
        (if (@not (Sig-extends sig))
            (list)
            (let ()
              (unless (@< int-upper max-int)
                (raise (format (string-append "Upper bound too large for given BitWidth; "
                                              "Sig: ~a, Upper-bound: ~a, Max-int: ~a")
                               sig int-upper (sub1 max-int))))
              (list (<= (card (Sig-rel sig)) (int int-upper)))))))))

; get-extender-preds :: Run-spec -> List<node/formula>
; Creates assertions for each Sig which has extending Sigs so that:
; - if it is abstract, then it must equal the sum of its extenders
; -                    else it must contain the sum of its extenders
; - all extenders are pair-wise disjoint.
(define (get-extender-preds run-spec)
  (define sig-constraints (for/list ([sig (get-sigs run-spec)])
    ; get children information
    (define children-rels (map Sig-rel (get-children run-spec sig)))

    ; abstract and sig1, ... extend => (= sig (+ sig1 ...))
    ; not abstract and sig is parent of sig1 => (in sig1 sig)
    ; TODO: optimize by identifying abstract sigs as sum of children
    (define (abstract sig extenders)
      (if (@= (length extenders) 1)
          (= sig (car extenders))
          (= sig (+ extenders))))
    (define (parent sig1 sig2)
      (in sig2 sig1))
    (define extends-constraints 
      (if (and (Sig-abstract sig) (cons? (Sig-extenders sig)))
          (list (abstract (Sig-rel sig) children-rels))
          (map (curry parent (Sig-rel sig)) children-rels)))

    ; sig1 and sig2 extend sig => (no (& sig1 sig2))
    (define (disjoin-pair sig1 sig2)
      (no (& sig1 sig2)))
    (define (disjoin-list a-sig a-list)
      (map (curry disjoin-pair a-sig) a-list))
    (define (disjoin a-list)
      (if (empty? a-list)
          empty
          (append (disjoin-list (first a-list) (rest a-list))
                  (disjoin (rest a-list)))))
    (define disjoint-constraints (disjoin children-rels))

    (append extends-constraints disjoint-constraints)))

  ; combine all constraints together
  (apply append sig-constraints))

; get-relation-preds :: Run-spec -> List<node/formula>
; Creates assertions for each Relation to ensure that it does not
; contain any atoms which don't populate their Sig.
(define (get-relation-preds run-spec)
  (for/list ([relation (get-relations run-spec)])
    (define sig-rels (map Sig-rel (get-sigs run-spec relation)))
    (in (Relation-rel relation) (-> sig-rels))))
