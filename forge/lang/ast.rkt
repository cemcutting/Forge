#lang racket

(require (for-syntax racket/syntax) (prefix-in @ racket) (prefix-in $ racket))
(require racket/struct)

(provide (except-out (all-defined-out) next-name @@and @@or int< int>)
         (rename-out [@@and and] [@@or or] [int< <] [int> >]))

; Ocelot ASTs are made up of expressions (which evaluate to relations) and
; formulas (which evaluate to booleans).
; All AST structs start with node/. The hierarchy is:
;   * node/expr  -- expressions
;     * node/expr/op  -- simple operators
;       * node/expr/+
;       * node/expr/-
;       * ...
;     * node/expr/comprehension  -- set comprehension
;     * node/expr/relation  -- leaf relation
;     * node/expr/constant  -- relational constant
;   * node/formula  -- formulas
;     * node/formula/op  -- simple operators
;       * node/formula/and
;       * node/formula/or
;       * ...
;     * node/formula/quantified  -- quantified formula
;     * node/formula/multiplicity  -- multiplicity formula

;; ARGUMENT CHECKS -------------------------------------------------------------

(define (check-args op args type?
                    #:same-arity? [same-arity? #f] #:arity [arity #f]
                    #:min-length [min-length 2] #:max-length [max-length #f]
                    #:join? [join? #f] #:domain? [domain? #f] #:range? [range? #f])
  (when (< (length args) min-length)
    (raise-arguments-error op "not enough arguments" "required" min-length "got" (length args)))
  (unless (false? max-length)
    (when (> (length args) max-length)
      (raise-arguments-error op "too many arguments" "maximum" max-length "got" (length args))))
  (for ([a (in-list args)])
    (unless (type? a)
      (raise-argument-error op (~v type?) a))
    (unless (false? arity)
      (unless (equal? (node/expr-arity a) arity)
        (raise-argument-error op (format "expression with arity ~v" arity) a))))
  (when same-arity?
    (let ([arity (node/expr-arity (car args))])
      (for ([a (in-list args)])
        (unless (equal? (node/expr-arity a) arity)
          (printf "~a ~n" args)
          (raise-arguments-error op "arguments must have same arity"
                                 "got" arity "and" (node/expr-arity a) ":" args)))))
  (when join?
    (when (<= (apply join-arity (for/list ([a (in-list args)]) (node/expr-arity a))) 0)
      (raise-arguments-error op (format "join would create a relation of arity 0: ~a" args))))
  (when range?
    (unless (equal? (node/expr-arity (cadr args)) 1)
      (raise-arguments-error op "second argument must have arity 1")))
  (when domain?
    (unless (equal? (node/expr-arity (car args)) 1)
      (raise-arguments-error op "first argument must have arity 1"))))


;; EXPRESSIONS -----------------------------------------------------------------

(struct node/expr (arity) #:transparent
  #:property prop:procedure (λ (r . sigs) (foldl join r sigs))
)

;; -- operators ----------------------------------------------------------------

(struct node/expr/op node/expr (children) #:transparent)

; lifted operators are defaults, for when the types aren't as expected
(define-syntax (define-expr-op stx)
  (syntax-case stx ()
    [(_ id arity checks ... #:lift @op #:type childtype)
     (with-syntax ([name (format-id #'id "node/expr/op/~a" #'id)])
       (syntax/loc stx
         (begin
           (struct name node/expr/op () #:transparent #:reflection-name 'id)
           (define id
             (lambda e
               (if ($and @op (for/and ([a (in-list e)]) ($not (node/expr? a))))
                   (apply @op e)
                   (begin
                     (check-args 'id e childtype checks ...)
                     (if arity
                         (let ([arities (for/list ([a (in-list e)]) (node/expr-arity a))])
                           (name (apply arity arities) e))
                         (name 1 e)))))))))] ; If arity is #f, assumed to be const 1
    [(_ id arity checks ... #:lift @op)
     (syntax/loc stx
       (define-expr-op id arity checks ... #:lift @op #:type node/expr?))]
    [(_ id arity checks ... #:type childtype)
     (syntax/loc stx
       (define-expr-op id arity checks ... #:lift #f #:type childtype))]
    [(_ id arity checks ...)
     (syntax/loc stx
       (define-expr-op id arity checks ... #:lift #f))]))

(define get-first
  (lambda e (car e)))
(define get-second
  (lambda e (cadr e)))
(define-syntax-rule (define-op/combine id @op)
  (define-expr-op id get-first #:same-arity? #t #:lift @op))

(define-op/combine + @+)
(define-op/combine - @-)
(define-op/combine & #f)

(define-syntax-rule (define-op/cross id)
  (define-expr-op id @+))
(define-op/cross ->)

(define-expr-op ~ get-first #:min-length 1 #:max-length 1 #:arity 2)

(define join-arity
  (lambda e (@- (apply @+ e) (@* 2 (@- (length e) 1)))))
(define-syntax-rule (define-op/join id)
  (define-expr-op id join-arity #:join? #t))
(define-op/join join)

(define-expr-op <: get-second #:max-length 2 #:domain? #t)
(define-expr-op :> get-first  #:max-length 2 #:range? #t)
(define-expr-op sing #f #:min-length 1 #:max-length 1 #:type node/int?)

(define-syntax-rule (define-op/closure id @op)
  (define-expr-op id (const 2) #:min-length 1 #:max-length 1 #:arity 2 #:lift @op))
(define-op/closure ^ #f)
(define-op/closure * @*)

;; -- quantifier vars ----------------------------------------------------------

;(struct node/expr/quantifier-var node/expr (sym))
(struct node/expr/quantifier-var node/expr (sym)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "?~a" (node/expr/quantifier-var-sym self)))])

;; -- comprehensions -----------------------------------------------------------

(struct node/expr/comprehension node/expr (decls formula)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(comprehension ~a ~a ~a)" 
              (node/expr-arity self) 
              (node/expr/comprehension-decls self)
              (node/expr/comprehension-formula self)))])
(define (comprehension decls formula)
  (for ([e (map cdr decls)])
    (unless (node/expr? e)
      (raise-argument-error 'set "expr?" e))
    (unless (equal? (node/expr-arity e) 1)
      (raise-argument-error 'set "decl of arity 1" e)))
  (unless (node/formula? formula)
    (raise-argument-error 'set "formula?" formula))
  (node/expr/comprehension (length decls) decls formula))

(define-syntax (set stx)
  (syntax-case stx ()
    [(_ ([r0 e0] ...) pred)
     (syntax/loc stx
       (let* ([r0 (node/expr/quantifier-var (node/expr-arity e0) 'r0)] ... )
         (comprehension (list (cons r0 e0) ...) pred)))]))

;; -- relations ----------------------------------------------------------------

(struct node/expr/relation node/expr (name typelist parent) #:transparent #:mutable
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/expr/relation arity name typelist parent) self)
     (fprintf port "~a" name))])
     ;(fprintf port "(relation ~a ~v ~a ~a)" arity name typelist parent))])
(define next-name 0)
(define (declare-relation typelist parent [name #f])
  (let ([name (if (false? name) 
                  (begin0 (format "r~v" next-name) (set! next-name (add1 next-name)))
                  name)])
    (node/expr/relation (length typelist) name typelist parent)))
(define (relation-arity rel)
  (node/expr-arity rel))
(define (relation-name rel)
  (node/expr/relation-name rel))
(define (relation-typelist rel)
  (node/expr/relation-typelist rel))
(define (relation-parent rel)
  (node/expr/relation-parent rel))

;; -- constants ----------------------------------------------------------------

(struct node/expr/constant node/expr (type) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/expr/constant-type self)))])

; THESE SHOULD BE MACROS
(define none (node/expr/constant 1 'none))
(define univ (node/expr/constant 1 'univ))
(define iden (node/expr/constant 2 'iden))
(define Int (node/expr/relation 1 "Int" '(Int) "univ"))
(define succ (node/expr/relation 2 "succ" '(Int Int) "CharlieSaysWhatever"))

;; INTS ------------------------------------------------------------------------

(struct node/int () #:transparent)

;; -- operators ----------------------------------------------------------------

(struct node/int/op node/int (children) #:transparent)

(define-syntax (define-int-op stx)
  (syntax-case stx ()
    [(_ id type? checks ... #:lift @op)
     (with-syntax ([name (format-id #'id "node/int/op/~a" #'id)])
       (syntax/loc stx
         (begin
           (struct name node/int/op () #:transparent #:reflection-name 'id)
           (define id
             (lambda e
               (if ($and @op (for/and ([a (in-list e)]) ($not (type? a))))
                   (apply @op e)
                   (begin
                     (check-args 'id e type? checks ...)
                     (name e))))))))]
    [(_ id type? checks ...)
     (syntax/loc stx
       (define-int-op id type? checks ... #:lift #f))]))

(define-int-op add node/int? #:min-length 2)
(define-int-op subtract node/int? #:min-length 2)
(define-int-op multiply node/int? #:min-length 2)
(define-int-op divide node/int? #:min-length 2)

(define-int-op card node/expr? #:min-length 1 #:max-length 1)
(define-int-op sum node/expr? #:min-length 1 #:max-length 1)

(define-int-op remainder node/int? #:min-length 2 #:max-length 2)
(define-int-op abs node/int? #:min-length 1 #:max-length 1)
(define-int-op sign node/int? #:min-length 1 #:max-length 1)

(define (max s-int)
  (sum (- s-int (join (^ succ) s-int))))
(define (min s-int)
  (sum (- s-int (join s-int (^ succ)))))

;(define-int-op max node/expr? #:min-length 1 #:max-length 1)
;(define-int-op min node/expr? #:min-length 1 #:max-length 1)

;; -- constants ----------------------------------------------------------------

(struct node/int/constant node/int (value) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/int/constant-value self)))])

;; -- sum quantifier -----------------------------------------------------------
(struct node/int/sum-quant node/int (decls int-expr)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/int/sum-quant decls int-expr) self)
     (fprintf port "(sum [~a] ~a)"
                   decls
                   int-expr))])

(define (sum-quant-expr decls int-expr)
  (for ([e (map cdr decls)])
    (unless (node/expr? e)
      (raise-argument-error 'set "expr?" e))
    (unless (equal? (node/expr-arity e) 1)
      (raise-argument-error 'set "decl of arity 1" e)))
  (unless (node/int? int-expr)
    (raise-argument-error 'set "int-expr?" int-expr))
  (node/int/sum-quant decls int-expr))

;; FORMULAS --------------------------------------------------------------------

(struct node/formula () #:transparent)

;; -- constants ----------------------------------------------------------------



(struct node/formula/constant node/formula (type) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/formula/constant-type self)))])

(define true (node/formula/constant 'true))
(define false (node/formula/constant 'false))

;; -- operators ----------------------------------------------------------------

(struct node/formula/op node/formula (children) #:transparent)

(define-syntax (define-formula-op stx)
  (syntax-case stx ()
    [(_ id type? checks ... #:lift @op)
     (with-syntax ([name (format-id #'id "node/formula/op/~a" #'id)])
       (syntax/loc stx
         (begin
           (struct name node/formula/op () #:transparent #:reflection-name 'id)
           (define id
             (lambda e
               (if ($and @op (for/and ([a (in-list e)]) ($not (type? a))))
                   (apply @op e)
                   (begin
                     (check-args 'id e type? checks ...)
                     (name e))))))))]
    [(_ id type? checks ...)
     (syntax/loc stx
       (define-formula-op id type? checks ... #:lift #f))]))

(define-formula-op in node/expr? #:same-arity? #t #:max-length 2)


(define-formula-op ordered node/expr? #:max-length 2)

(define-formula-op && node/formula? #:min-length 1 #:lift #f)
(define-formula-op || node/formula? #:min-length 1 #:lift #f)
(define-formula-op => node/formula? #:min-length 2 #:max-length 2 #:lift #f)
(define-formula-op ! node/formula? #:min-length 1 #:max-length 1 #:lift #f)
(define-formula-op int> node/int? #:min-length 2 #:max-length 2)
(define-formula-op int< node/int? #:min-length 2 #:max-length 2)
(define-formula-op int= node/int? #:min-length 2 #:max-length 2)

(define-formula-op = node/expr? #:same-arity? #t #:max-length 2 #:lift int=)

(define not !)

(define-syntax (@@and stx)
  (syntax-case stx ()
    [(_) (syntax/loc stx true)] ;#t?
    [(_ a0 a ...)
     (syntax/loc stx
       (let ([a0* a0])
         (if (node/formula? a0*)
             (&& a0* a ...)
             (and a0* a ...))))]))
(define-syntax (@@or stx)
  (syntax-case stx ()
    [(_) (syntax/loc stx false)]
    [(_ a0 a ...)
     (syntax/loc stx
       (let ([a0* a0])
         (if (node/formula? a0*)
             (|| a0* a ...)
             (or a0* a ...))))]))
       

;; -- quantifiers --------------------------------------------------------------

(struct node/formula/quantified node/formula (quantifier decls formula)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/formula/quantified quantifier decls formula) self)
     (fprintf port "(~a ~a ~a)" quantifier decls formula))])

(define (quantified-formula quantifier decls formula)
  (for ([e (in-list (map cdr decls))])
    (unless (node/expr? e)
      (raise-argument-error quantifier "expr?" e))
    #'(unless (equal? (node/expr-arity e) 1)
      (raise-argument-error quantifier "decl of arity 1" e)))
  (unless (or (node/formula? formula) (equal? #t formula))
    (raise-argument-error quantifier "formula?" formula))
  (node/formula/quantified quantifier decls formula))


;(struct node/formula/higher-quantified node/formula (quantifier decls formula))

;; -- multiplicities -----------------------------------------------------------

(struct node/formula/multiplicity node/formula (mult expr)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/formula/multiplicity mult expr) self)
     (fprintf port "(~a ~a)" mult expr))])
(define (multiplicity-formula mult expr)
  (unless (node/expr? expr)
    (raise-argument-error mult "expr?" expr))
  (node/formula/multiplicity mult expr))


#|(define-syntax (all stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (with-syntax ([(rel ...) (generate-temporaries #'(r1 ...))])
       (syntax/loc stx
         (let* ([x1 (declare-relation 1)] ...
                [decls (list (cons x1 r1) ...)])
           (quantified-formula 'all decls pred))))]))|#



; ok something of this form works!
; now to make it actually work.
; ok, search through pred for instances of v0, replace with just the datum.
; then, in kodkod-translate, we keep a list of quantified variables, and if we ever hit one we know what to do.
; and that can only happen in the context of interpret-expr, right? yeah, it always appears in an expression context.
; and in that scenario, we can always just straight print it!

; OK new plan: reader goes through all 
(define-syntax (all stx) ;#'(quantified-formula 'all (list 'v0 'e0) true)
  (syntax-case stx ()
    [(_ ([v0 e0] ...) pred)
     ; need a with syntax????
     (syntax/loc stx
       (let* ([v0 (node/expr/quantifier-var (node/expr-arity e0) 'v0)] ...)
         (quantified-formula 'all (list (cons v0 e0) ...) pred)))]))

#|(define-syntax (one stx) ;#'(quantified-formula 'all (list 'v0 'e0) true)
  (syntax-case stx ()
    [(_ ([v0 e0]) pred)
     ; need a with syntax????
     (syntax/loc stx
       (let ([v0 (node/expr/quantifier-var 1 'v0)])
         (quantified-formula 'one (list (cons v0 e0)) pred)))]))|#



(define-syntax (some stx)
  (syntax-case stx ()
    [(_ ([v0 e0] ...) pred)
     (syntax/loc stx
       (let* ([v0 (node/expr/quantifier-var (node/expr-arity e0) 'v0)] ...)
         (quantified-formula 'some (list (cons v0 e0) ...) pred)))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'some expr))]))

(define-syntax (no stx)
  (syntax-case stx ()
    [(_ ([v0 e0] ...) pred)
     (syntax/loc stx
       (let* ([v0 (node/expr/quantifier-var (node/expr-arity e0) 'v0)] ...)
         (! (quantified-formula 'some (list (cons v0 e0) ...) pred))))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'no expr))]))

(define-syntax (one stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (syntax/loc stx
       (multiplicity-formula 'one (set ([x1 r1] ...) pred)))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'one expr))]))

(define-syntax (lone stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (syntax/loc stx
       (multiplicity-formula 'lone (set ([x1 r1] ...) pred)))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'lone expr))]))


; sum quantifier macro
(define-syntax (sum-quant stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) int-expr)
     (syntax/loc stx
       (let* ([x1 (node/expr/quantifier-var (node/expr-arity r1) 'x1)] ...)
         (sum-quant-expr (list (cons x1 r1) ...) int-expr)))]))


;; PREDICATES ------------------------------------------------------------------

; Operators that take only a single argument
(define (unary-op? op)
  (@or (node/expr/op/~? op)
       (node/expr/op/^? op)
       (node/expr/op/*? op)
       (node/expr/op/sing? op)
       (node/formula/op/!? op)
       (node/int/op/sum? op)
       (node/int/op/card? op)
       (node/int/op/abs? op)
       (node/int/op/sign? op)
       (@member op (list ~ ^ * sing ! not sum card abs sign)))) ; These are just aliases for the expanded names
(define (binary-op? op)
  (@member op (list <: :> in = => int= int> int< remainder)))
(define (nary-op? op)
  (@member op (list + - & -> join && || add subtract multiply divide)))


;; PREFABS ---------------------------------------------------------------------

; Prefabs are functions that produce AST nodes. They're used in sketches, where
; we might want to specify an entire expression as a terminal or non-terminal
; rather than a single operator.
; A prefab needs to specify two things:
; (a) a function that takes a desired output arity k, and produces a list of
;     inputs that could produce such an output arity when the prefad is applied
; (b) a function that takes a number of inputs defined by the above function, 
;     and produces an AST.

(struct prefab (inputs ctor) #:transparent
  #:property prop:procedure (struct-field-index ctor))