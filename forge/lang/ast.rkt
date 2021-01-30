#lang racket

(require (for-syntax racket/syntax syntax/srcloc)
         syntax/srcloc (prefix-in @ racket) (prefix-in $ racket))

(provide (except-out (all-defined-out) next-name @@and @@or @@not int< int>)
         (rename-out [@@and and] [@@or or] [@@not not] [int< <] [int> >]))

; Forge's AST is based on Ocelot's AST, with modifications.

; Ocelot ASTs are made up of expressions (which evaluate to relations) and
; formulas (which evaluate to booleans).
; All AST structs start with node/. The hierarchy is:
;  * node (info) -- holds basic info like source location (added for Forge)
;   * node/expr (arity) -- expressions
;     * node/expr/op (children) -- simple operators
;       * node/expr/op/+
;       * node/expr/op/-
;       * ...
;     * node/expr/comprehension (decls formula)  -- set comprehension
;     * node/expr/relation (name typelist parent)  -- leaf relation
;     * node/expr/constant (type) -- relational constant [type serves purpose of name?]
;     * node/expr/quantifier-var (sym) -- variable for quantifying over
;   * node/formula  -- formulas
;     * node/formula/op  -- simple operators
;       * node/formula/op/and
;       * node/formula/op/or
;       * ...
;     * node/formula/quantified (TODO FILL)  -- quantified formula
;     * node/formula/multiplicity (TODO FILL) -- multiplicity formula
;     * node/formula/sealed
;       * wheat
;       * chaff
;   * node/int -- integer expression
;     * node/int/op (children)
;       * node/int/op/add
;       * ...
;     * node/int/constant (value) -- int constant
;; -----------------------------------------------------------------------------

; Group information in one struct to make change easier
; TODO TN: should this be transparent? or custom to-string to avoid printing #<nodeinfo>?
(struct nodeinfo (loc) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (nodeinfo loc) self)
     ; hide nodeinfo when printing; don't print anything or this will become overwhelming
     ;(fprintf port "")
     (void))])

; Base node struct, should be ancestor of all AST node types
; Should never be directly instantiated
(struct node (info) #:transparent)

(define empty-nodeinfo (nodeinfo (build-source-location #f)))

;; ARGUMENT CHECKS -------------------------------------------------------------

(define (check-args info op args type?
                    #:same-arity? [same-arity? #f] #:arity [arity #f]
                    #:min-length [min-length 2] #:max-length [max-length #f]
                    #:join? [join? #f] #:domain? [domain? #f] #:range? [range? #f])
  (define loc (nodeinfo-loc info))
  (when (< (length args) min-length)
    (raise-syntax-error #f (format "building ~a not enough arguments; required ~a got ~a at loc: ~a"
                                   op min-length args loc)
                        (datum->syntax #f args (build-source-location-syntax loc))))
  (unless (false? max-length)
    (when (> (length args) max-length)
      (raise-syntax-error #f (format "too many arguments; maximum ~a, got ~a at loc: ~a" max-length args loc)
                          (datum->syntax #f args (build-source-location-syntax loc)))))
  (for ([a (in-list args)])
    (unless (type? a)
      (raise-syntax-error #f (format "argument to ~a had unexpected type. expected ~a. loc: ~a" op type? loc)
                          (datum->syntax #f args (build-source-location-syntax loc))))
    (unless (false? arity)
      (unless (equal? (node/expr-arity a) arity)
        (raise-syntax-error #f (format "expression with arity ~v" arity)
                            (datum->syntax #f args (build-source-location-syntax loc))))))
  (when same-arity?
    (let ([arity (node/expr-arity (car args))])
      (for ([a (in-list args)])
        (unless (equal? (node/expr-arity a) arity)
          (raise-syntax-error #f (format "arguments must have same arity. got ~a and ~a at loc: ~a"
                                         arity (node/expr-arity a) loc)
                           (datum->syntax #f args (build-source-location-syntax loc)))))))
  (when join?
    (when (<= (apply join-arity (for/list ([a (in-list args)]) (node/expr-arity a))) 0)
       (raise-syntax-error #f (format "join would create a relation of arity 0 at loc: ~a" loc)
                           (datum->syntax #f args (build-source-location-syntax loc)))))
  
  (when range?
    (unless (equal? (node/expr-arity (cadr args)) 1)      
      (raise-syntax-error #f (format "second argument must have arity 1 at loc: ~a" loc)
                          (datum->syntax #f args (build-source-location-syntax loc)))))
  (when domain?
    (unless (equal? (node/expr-arity (car args)) 1)      
      (raise-syntax-error #f (format "first argument must have arity 1 at loc: ~a" loc)
                             (datum->syntax #f args (build-source-location-syntax loc))))))


;; EXPRESSIONS -----------------------------------------------------------------

; Previously, this would be: 
;(foldl @join rel vars))   ; rel[a][b]...  (taken from breaks.rkt)
; or (foldl join r sigs) (taken from below)
(define (build-box-join sofar todo)
  (cond [(empty? todo) sofar]
        [else
         (define loc1 (nodeinfo-loc (node-info sofar)))
         (define loc2 (nodeinfo-loc (node-info (first todo))))
         (build-box-join (join/info
                          (nodeinfo (build-source-location loc1 loc2))
                                    (first todo) sofar)
                          (rest todo))]))

; Should never be directly instantiated
(struct node/expr node (arity) #:transparent
  #:property prop:procedure (λ (r . sigs) (build-box-join r sigs)))

;; -- operators ----------------------------------------------------------------

; Should never be directly instantiated
(struct node/expr/op node/expr (children) #:transparent)

;; if-then-else *expression*, which is different from an if-then-else formula
;   The formula version is just sugar, the expression version is a basic expr type
;   that Kodkod/Pardinus understand and is hard to emulate generically.
(struct node/expr/ite node/expr (condition thene elsee) #:transparent #:reflection-name 'ite             
             #:methods gen:equal+hash
             [(define equal-proc (make-robust-node-equal-syntax node/expr))
              (define hash-proc  (make-robust-node-hash-syntax node/expr 0))
              (define hash2-proc (make-robust-node-hash-syntax node/expr 3))]
             #:methods gen:custom-write
             [(define (write-proc self port mode)                
                (fprintf port "~a" (list 'ite (node/expr/ite-condition self)
                                         (node/expr/ite-thene self)
                                         (node/expr/ite-elsee self))))])

(define-syntax (ite/info stx)
  (syntax-case stx ()
    [(_ info a b c)
     (quasisyntax/loc stx
       (begin
         (unless (node/formula? a)
           (raise-syntax-error #f (format "If-then-else expression requires first argument to be a formula")
                               (datum->syntax #f a (build-source-location-syntax (nodeinfo-loc info)))))
         (unless (node/expr? b)
           (raise-syntax-error #f (format "If-then-else expression requires second argument to be an expression")
                               (datum->syntax #f b (build-source-location-syntax (nodeinfo-loc info)))))
         (unless (node/expr? c)
           (raise-syntax-error #f (format "If-then-else expression requires third argument to be an expression")
                               (datum->syntax #f c (build-source-location-syntax (nodeinfo-loc info)))))
         (unless (equal? (node/expr-arity b) (node/expr-arity c))
           (raise-syntax-error #f (format "If-then-else expression requires expression arguments to have same arity")
                               (datum->syntax #f c (build-source-location-syntax (nodeinfo-loc info)))))
         (node/expr/ite info (node/expr-arity b) a b c)))]))

(define-syntax (ite stx)
  (syntax-case stx ()
    [(_ a b c) (quasisyntax/loc stx (ite/info (nodeinfo #,(build-source-location stx)) a b c))]))

; lifted operators are defaults, for when the types aren't as expected
(define-syntax (define-node-op stx)
  (syntax-case stx ()
    [(_ id parent arity checks ... #:lift @op #:type childtype)
     ;(printf "defining: ~a~n" stx)
     (with-syntax ([name (format-id #'id "~a/~a" #'parent #'id)]
                   [parentname (format-id #'id "~a" #'parent)]
                   [macroname/info (format-id #'id "~a/info" #'id)]
                   [child-accessor (format-id #'id "~a-children" #'parent)]
                   [display-id (if (equal? '|| (syntax->datum #'id)) "||" #'id)]
                   [ellip '...]) ; otherwise ... is interpreted as belonging to the outer macro
       (syntax/loc stx
         (begin
           (struct name parent () #:transparent #:reflection-name 'id
             
             #:methods gen:equal+hash
             [(define equal-proc (make-robust-node-equal-syntax parentname))
              (define hash-proc  (make-robust-node-hash-syntax parentname 0))
              (define hash2-proc (make-robust-node-hash-syntax parentname 3))]
             #:methods gen:custom-write
             [(define (write-proc self port mode)
                ; all of the /op nodes have their children in a field named "children"
                (fprintf port "~a" (cons 'display-id (child-accessor self))))])
           ; Keep this commented-out line for use in emergencies to debug bad source locations:
           ;(fprintf port "~a" (cons 'display-id (cons (nodeinfo-loc (node-info self)) (child-accessor self)))))])
           
           ; a macro constructor that captures the syntax location of the call site
           ;  (good for, e.g., test cases + parser)
           (define-syntax (id stx2)
             (syntax-case stx2 ()
               [(_ e ellip)                
                (quasisyntax/loc stx2
                  (macroname/info (nodeinfo #,(build-source-location stx2)) e ellip))]))
           
           ; a macro constructor that also takes a syntax object to use for location
           ;  (good for, e.g., creating a big && in sigs.rkt for predicates)
           (define-syntax (macroname/info stx2)                     
             (syntax-case stx2 ()                              
               [(_ info e ellip)
                (quasisyntax/loc stx2
                  ;(printf "in created macro, arg location: ~a~n" (build-source-location stx2))
                  (begin
                    ; Keeping this comment in case these macros need to be maintained:
                    ; This line will cause a bad syntax error without any real error-message help.
                    ; The problem is that "id" is the thing defined by this define-stx
                    ;   so it'l try to expand (e.g.) "~" by itself. Instead of "id" use " 'id ".
                    ;(printf "debug2, in ~a: ~a~n" id (list e ellip))
                    
                    ; allow to work with a list of args or a spliced list e.g. (+ 'univ 'univ) or (+ (list univ univ)).                   
                    (let* ([args-raw (list e ellip)]
                           [args (cond
                                   [(or (not (equal? 1 (length args-raw)))
                                        (not (list? (first args-raw)))) args-raw]
                                   [else (first args-raw)])])
                      (if ($and @op (for/and ([a (in-list args)]) ($not (childtype a))))
                          (apply @op args)
                          (begin
                            (check-args info 'id args childtype checks ...)
                            (if arity
                                ; expression
                                (if (andmap node/expr? args)
                                    ; expression with expression children (common case)
                                    (let ([arities (for/list ([a (in-list args)]) (node/expr-arity a))])
                                      (name info (apply arity arities) args))
                                    ; expression with non-expression children or const arity (e.g., sing)
                                    (name info (arity) args))
                                ; intexpression or formula
                                (name info args)))))))])))))] 
    [(_ id parent arity checks ... #:lift @op)
     (printf "Warning: ~a was defined without a child type; defaulting to node/expr?~n" (syntax->datum #'id))
     (syntax/loc stx
       (define-node-op id parent arity checks ... #:lift @op #:type node/expr?))]
    [(_ id parent arity checks ... #:type childtype)    
     (syntax/loc stx
       (define-node-op id parent arity checks ... #:lift #f #:type childtype))]
    [(_ id parent arity checks ...)     
     (syntax/loc stx
       (define-node-op id parent arity checks ... #:lift #f))]))

(define get-first
  (lambda e (car e)))
(define get-second
  (lambda e (cadr e)))
(define-syntax-rule (define-op/combine id @op)
  (define-node-op id node/expr/op get-first #:same-arity? #t #:lift @op #:type node/expr?))

(define-op/combine + @+)
(define-op/combine - @-)
(define-op/combine & #f)

(define-syntax-rule (define-op/cross id)
  (define-node-op id node/expr/op @+ #:type node/expr?))
(define-op/cross ->)

(define-node-op ~ node/expr/op get-first #:min-length 1 #:max-length 1 #:arity 2 #:type node/expr?)

(define join-arity
  (lambda e (@- (apply @+ e) (@* 2 (@- (length e) 1)))))
(define-syntax-rule (define-op/join id)
  (define-node-op id node/expr/op join-arity #:join? #t #:type node/expr?))
(define-op/join join)

(define-node-op <: node/expr/op get-second #:max-length 2 #:domain? #t #:type node/expr?)
(define-node-op :> node/expr/op get-first  #:max-length 2 #:range? #t #:type node/expr?)
(define-node-op sing node/expr/op (const 1) #:min-length 1 #:max-length 1 #:type node/int?)

(define-node-op prime node/expr/op get-first #:min-length 1 #:max-length 1 #:type node/expr?)

(define-syntax-rule (define-op/closure id @op)
  (define-node-op id node/expr/op (const 2) #:min-length 1 #:max-length 1 #:arity 2 #:lift @op #:type node/expr?))
(define-op/closure ^ #f)
(define-op/closure * @*)




;; -- quantifier vars ----------------------------------------------------------

(struct node/expr/quantifier-var node/expr (sym) #:transparent
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/expr/quantifier-var))
   (define hash-proc  (make-robust-node-hash-syntax node/expr/quantifier-var 0))
   (define hash2-proc (make-robust-node-hash-syntax node/expr/quantifier-var 3))]
  #:methods gen:custom-write
  [(define (write-proc self port mode)     
     (fprintf port "~a" (node/expr/quantifier-var-sym self)))])

;; -- comprehensions -----------------------------------------------------------

(struct node/expr/comprehension node/expr (decls formula)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(comprehension ~a ~a)"               
              (node/expr/comprehension-decls self)
              (node/expr/comprehension-formula self)))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/expr/comprehension))
   (define hash-proc  (make-robust-node-hash-syntax node/expr/comprehension 0))
   (define hash2-proc (make-robust-node-hash-syntax node/expr/comprehension 3))])

(define (comprehension info decls formula)
  (for ([e (map cdr decls)])
    (unless (node/expr? e)
      (raise-argument-error 'set "expr?" e))
    (unless (equal? (node/expr-arity e) 1)
      (raise-argument-error 'set "decl of arity 1" e)))
  (unless (node/formula? formula)
    (raise-argument-error 'set "formula?" formula))
  (node/expr/comprehension info (length decls) decls formula))

(define-syntax (set stx)
  (syntax-case stx ()
    [(_ ([r0 e0] ...) pred)
     (quasisyntax/loc stx
       (let* ([r0 (node/expr/quantifier-var (nodeinfo #,(build-source-location stx)) (node/expr-arity e0) 'r0)] ... )
         (comprehension (nodeinfo #,(build-source-location stx)) (list (cons r0 e0) ...) pred)))]))

;; -- relations ----------------------------------------------------------------

; Do not use this constructor directly, instead use the rel macro or the build-relation procedure.
; The is-variable field allows support for Electrum-style var fields in the core language 
(struct node/expr/relation node/expr (name typelist parent is-variable) #:transparent #:mutable
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/expr/relation info arity name typelist parent is-variable) self)
     ;(fprintf port "(relation ~a ~v ~a ~a)" arity name typelist parent)
     (fprintf port "(rel ~a)" name))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/expr/relation))
   (define hash-proc  (make-robust-node-hash-syntax node/expr/relation 0))
   (define hash2-proc (make-robust-node-hash-syntax node/expr/relation 3))])
(define next-name 0)

; e.g.: (rel '(Node Node) 'Node "edges") to define the usual edges relation
(define-syntax (rel stx)
  (syntax-case stx ()
    [(_ (typelist ...) parent name)
     (quasisyntax/loc stx       
       (build-relation #,(build-source-location stx) (typelist ...) parent name #f))]
    [(_ (typelist ...) parent name isv)
     (quasisyntax/loc stx       
       (build-relation #,(build-source-location stx) (typelist ...) parent name isvar))]))

; Used by rel macro but *also* by Sig and relation macros in forge/core (sigs.rkt)
(define (build-relation loc typelist parent [name #f] [is-var #f])
  (let ([name (cond [(false? name) 
                     (begin0 (format "r~v" next-name) (set! next-name (add1 next-name)))]
                     [(symbol? name) (symbol->string name)]
                     [else name])]
        [types (map (lambda (t)
                      (cond                        
                        [(string? t) t]
                        [(symbol? t) (symbol->string t)]
                        [else (error (format "build-relation expected list of strings or symbols: ~a" typelist))])) typelist)]
        [scrubbed-parent (cond [(symbol? parent) (symbol->string parent)]
                               [(string? parent) parent]
                               [else (error (format "build-relation expected parent as either symbol or string"))])])    
    (node/expr/relation (nodeinfo loc) (length types) name
                        types scrubbed-parent is-var)))

; Helpers to more cleanly talk about relation fields
(define (relation-arity rel)
  (node/expr-arity rel))
(define (relation-name rel)
  (node/expr/relation-name rel))
(define (relation-typelist rel)
  (node/expr/relation-typelist rel))
(define (relation-parent rel)
  (node/expr/relation-parent rel))

;; -- relations ----------------------------------------------------------------

(struct node/expr/atom node/expr (name) #:transparent #:mutable
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/expr/atom info arity name) self)
     (fprintf port "(atom ~a)" name))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/expr/atom))
   (define hash-proc  (make-robust-node-hash-syntax node/expr/atom 0))
   (define hash2-proc (make-robust-node-hash-syntax node/expr/atom 3))])


(define-syntax (atom stx)
  (syntax-case stx ()    
    [(_ val)
     (quasisyntax/loc stx (node/expr/atom
                           (nodeinfo #,(build-source-location stx))
                           1 val))]))

;(define (atom name)
;  (node/expr/atom
;   (quasisyntax/loc stx (node/expr/constant (nodeinfo #,(build-source-location stx))
;   1 name))

(define (atom-name rel)
  (node/expr/atom-name rel))

;; -- constants ----------------------------------------------------------------

(struct node/expr/constant node/expr (type) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/expr/constant-type self)))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/expr/constant))
   (define hash-proc  (make-robust-node-hash-syntax node/expr/constant 0))
   (define hash2-proc (make-robust-node-hash-syntax node/expr/constant 3))])

; Macros in order to capture source location
; constants
(define-syntax none (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/expr/constant (nodeinfo #,(build-source-location stx)) 1 'none))])))
(define-syntax univ (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/expr/constant (nodeinfo #,(build-source-location stx)) 1 'univ))])))
(define-syntax iden (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/expr/constant (nodeinfo #,(build-source-location stx)) 2 'iden))])))
; relations, not constants
(define-syntax Int (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/expr/relation (nodeinfo #,(build-source-location stx)) 1 "Int" '(Int) "univ" #f))])))
(define-syntax succ (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/expr/relation (nodeinfo #,(build-source-location stx)) 2 "succ" '(Int Int) "Int" #f))])))

;; INTS ------------------------------------------------------------------------

; Should never be directly instantiated
(struct node/int node () #:transparent)

;; -- operators ----------------------------------------------------------------

(struct node/int/op node/int (children) #:transparent)

(define-node-op add node/int/op #f #:min-length 2 #:type node/int?)
(define-node-op subtract node/int/op #f #:min-length 2 #:type node/int?)
(define-node-op multiply node/int/op #f #:min-length 2 #:type node/int?)
(define-node-op divide node/int/op #f #:min-length 2 #:type node/int?)

; id, parent, arity, checks
(define-node-op card node/int/op #f #:min-length 1 #:max-length 1 #:type node/expr?)
(define-node-op sum node/int/op #f #:min-length 1 #:max-length 1 #:type node/expr?)

(define-node-op remainder node/int/op #f #:min-length 2 #:max-length 2 #:type node/int?)
(define-node-op abs node/int/op #f #:min-length 1 #:max-length 1 #:type node/int?)
(define-node-op sign node/int/op #f #:min-length 1 #:max-length 1 #:type node/int?)

; min and max are now *defined*, not declared:
;(define-node-op max node/int/op #:min-length 1 #:max-length 1 #:type node/int?)
;(define-node-op min node/int/op #:min-length 1 #:max-length 1 #:type node/int?)

(define (max s-int)
  (sum (- s-int (join (^ succ) s-int))))
(define (min s-int)
  (sum (- s-int (join s-int (^ succ)))))

;; -- constants ----------------------------------------------------------------

(struct node/int/constant node/int (value) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/int/constant-value self)))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/int/constant))
   (define hash-proc  (make-robust-node-hash-syntax node/int/constant 0))
   (define hash2-proc (make-robust-node-hash-syntax node/int/constant 3))])


(define-syntax (int stx)
  (syntax-case stx ()
    [(_ n)
     (quasisyntax/loc stx       
         (node/int/constant (nodeinfo #,(build-source-location stx)) n))]))

;; -- sum quantifier -----------------------------------------------------------
(struct node/int/sum-quant node/int (decls int-expr)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/int/sum-quant info decls int-expr) self)
     (fprintf port "(sum [~a] ~a)"
                   decls
                   int-expr))]
    #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/int/sum-quant))
   (define hash-proc  (make-robust-node-hash-syntax node/int/sum-quant 0))
   (define hash2-proc (make-robust-node-hash-syntax node/int/sum-quant 3))])

(define (sum-quant-expr info decls int-expr)
  (for ([e (map cdr decls)])
    (unless (node/expr? e)
      (raise-argument-error 'set "expr?" e))
    (unless (equal? (node/expr-arity e) 1)
      (raise-argument-error 'set "decl of arity 1" e)))
  (unless (node/int? int-expr)
    (raise-argument-error 'set "int-expr?" int-expr))
  (node/int/sum-quant info decls int-expr))

;; FORMULAS --------------------------------------------------------------------

; Should never be directly instantiated
(struct node/formula node () #:transparent)

;; -- constants ----------------------------------------------------------------

(struct node/formula/constant node/formula (type) #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/formula/constant-type self)))]
    #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/formula/constant))
   (define hash-proc  (make-robust-node-hash-syntax node/formula/constant 0))
   (define hash2-proc (make-robust-node-hash-syntax node/formula/constant 3))])

(define-syntax true (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/formula/constant (nodeinfo #,(build-source-location stx)) 'true))])))
(define-syntax false (lambda (stx) (syntax-case stx ()    
    [val (identifier? (syntax val)) (quasisyntax/loc stx (node/formula/constant (nodeinfo #,(build-source-location stx)) 'false))])))

;; -- operators ----------------------------------------------------------------

; Should never be directly instantiated
(struct node/formula/op node/formula (children) #:transparent)

(define-node-op in node/formula/op #f  #:same-arity? #t #:max-length 2 #:type node/expr?)

; TODO: what is this for?
(define-node-op ordered node/formula/op #f #:max-length 2 #:type node/expr?)

(define-node-op && node/formula/op #f #:min-length 1 #:lift #f #:type node/formula?)
(define-node-op || node/formula/op #f #:min-length 1 #:lift #f #:type node/formula?)
(define-node-op => node/formula/op #f #:min-length 2 #:max-length 2 #:lift #f #:type node/formula?)
(define-node-op ! node/formula/op #f #:min-length 1 #:max-length 1 #:lift #f #:type node/formula?)
(define-node-op int> node/formula/op #f #:min-length 2 #:max-length 2 #:type node/int?)
(define-node-op int< node/formula/op #f #:min-length 2 #:max-length 2 #:type node/int?)
(define-node-op int= node/formula/op #f #:min-length 2 #:max-length 2 #:type node/int?)

; Electrum temporal operators
(define-node-op always node/formula/op #f #:min-length 1 #:max-length 1 #:lift #f #:type node/formula?)
(define-node-op eventually node/formula/op #f #:min-length 1 #:max-length 1 #:lift #f #:type node/formula?)
(define-node-op after node/formula/op #f #:min-length 1 #:max-length 1 #:lift #f #:type node/formula?)
(define-node-op until node/formula/op #f #:min-length 1 #:max-length 2 #:lift #f #:type node/formula?)
(define-node-op releases node/formula/op #f #:min-length 1 #:max-length 2 #:lift #f #:type node/formula?)

; --------------------------------------------------------

(define (int=-lifter i1 i2)
  (int= i1 i2))

(define-node-op = node/formula/op #f #:same-arity? #t #:max-length 2 #:lift int=-lifter #:type node/expr?) 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lift the "and", "or" and "not" procedures

(define-syntax (@@and stx)
  (syntax-case stx ()
    [(_) (syntax/loc stx true)] ; Racket treats any non-#f as true
    [(_ a0 a ...)
     (quasisyntax/loc stx
       (let ([a0* a0])         
         (if (node/formula? a0*)
             (&&/info (nodeinfo #,(build-source-location stx)) a0* a ...)
             (and a0* a ...))))]))
(define-syntax (@@not stx)
  (syntax-case stx ()    
    [(_ a0)
     (quasisyntax/loc stx
       (let ([a0* a0])
         (if (node/formula? a0*)
             (!/info (nodeinfo #,(build-source-location stx)) a0*)
             (not a0*))))]))
(define-syntax (@@or stx)
  (syntax-case stx ()
    [(_) (syntax/loc stx false)]
    [(_ a0 a ...)
     (quasisyntax/loc stx
       (let ([a0* a0])
         (if (node/formula? a0*)
             (||/info (nodeinfo #,(build-source-location stx)) a0* a ...)
             (or a0* a ...))))]))

; *** WARNING ***
; Because of the way this is set up, if you're running tests in the REPL on the ast.rkt tab,
; you need to use @@and (etc.) not and (etc.) to construct formulas. If you try to use and, etc.
; you'll get the boolean behavior, which short-circuits. E.g.
; (and (= iden iden) (= univ univ))
; evaluates to 
; (= #<nodeinfo> '('univ 'univ))
; which is the last thing in the list.


(require (prefix-in @ (only-in racket ->)))
(define/contract (maybe-and->list fmla)
  (@-> node/formula? (listof node/formula?))
  (cond [(node/formula/op/&&? fmla)
         (apply append (map maybe-and->list (node/formula/op-children fmla)))]
        [else
         (list fmla)]))

;; -- quantifiers --------------------------------------------------------------

(struct node/formula/quantified node/formula (quantifier decls formula)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/formula/quantified info quantifier decls formula) self)
     (fprintf port "(~a [~a] ~a)" quantifier decls formula))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/formula/quantified))
   (define hash-proc  (make-robust-node-hash-syntax node/formula/quantified 0))
   (define hash2-proc (make-robust-node-hash-syntax node/formula/quantified 3))])

(define (quantified-formula info quantifier decls formula)  
  (for ([e (in-list (map cdr decls))])
    (unless (node/expr? e)
      (raise-argument-error quantifier "expr?" e))
    #'(unless (equal? (node/expr-arity e) 1)
      (raise-argument-error quantifier "decl of arity 1" e)))
  (unless (or (node/formula? formula) (equal? #t formula))
    (raise-argument-error quantifier "formula?" formula))
  (node/formula/quantified info quantifier decls formula))


;(struct node/formula/higher-quantified node/formula (quantifier decls formula))

;; -- multiplicities -----------------------------------------------------------

(struct node/formula/multiplicity node/formula (mult expr)
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (match-define (node/formula/multiplicity info mult expr) self)
     (fprintf port "(~a ~a)" mult expr))]
  #:methods gen:equal+hash
  [(define equal-proc (make-robust-node-equal-syntax node/formula/multiplicity))
   (define hash-proc  (make-robust-node-hash-syntax node/formula/multiplicity 0))
   (define hash2-proc (make-robust-node-hash-syntax node/formula/multiplicity 3))])

(define (multiplicity-formula info mult expr)
  (unless (node/expr? expr)
    (raise-argument-error mult "expr?" expr))
  (node/formula/multiplicity info mult expr))

(define-syntax (all stx)
  (syntax-case stx ()
    [(_ ([v0 e0] ...) pred)
     ; need a with syntax???? 
     (quasisyntax/loc stx
       (let* ([v0 (node/expr/quantifier-var (nodeinfo #,(build-source-location stx)) (node/expr-arity e0) 'v0)] ...)
         (quantified-formula (nodeinfo #,(build-source-location stx)) 'all (list (cons v0 e0) ...) pred)))]))

(define-syntax (some stx)
  (syntax-case stx ()
    [(_ ([v0 e0] ...) pred)     
     (quasisyntax/loc stx
       (let* ([v0 (node/expr/quantifier-var (nodeinfo #,(build-source-location stx)) (node/expr-arity e0) 'v0)] ...)
         (quantified-formula (nodeinfo #,(build-source-location stx)) 'some (list (cons v0 e0) ...) pred)))]
    [(_ expr)
     (quasisyntax/loc stx
       (multiplicity-formula (nodeinfo #,(build-source-location stx)) 'some expr))]))

(define-syntax (no stx)
  (syntax-case stx ()
    [(_ ([v0 e0] ...) pred)
     (quasisyntax/loc stx
       (let* ([v0 (node/expr/quantifier-var (nodeinfo #,(build-source-location stx)) (node/expr-arity e0) 'v0)] ...)
         (! (quantified-formula (nodeinfo #,(build-source-location stx)) 'some (list (cons v0 e0) ...) pred))))]
    [(_ expr)
     (quasisyntax/loc stx
       (multiplicity-formula (nodeinfo #,(build-source-location stx)) 'no expr))]))

(define-syntax (one stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (quasisyntax/loc stx
       ; TODO TN: is this right? shouldn't it be a quantified-formula?
       (multiplicity-formula (nodeinfo #,(build-source-location stx)) 'one (set ([x1 r1] ...) pred)))]
    [(_ expr)
     (quasisyntax/loc stx
       (multiplicity-formula (nodeinfo #,(build-source-location stx)) 'one expr))]))

(define-syntax (lone stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (quasisyntax/loc stx
       ; TODO TN: is this right? 
       (multiplicity-formula (nodeinfo #,(build-source-location stx)) 'lone (set ([x1 r1] ...) pred)))]
    [(_ expr)
     (quasisyntax/loc stx
       (multiplicity-formula (nodeinfo #,(build-source-location stx)) 'lone expr))]))

; sum quantifier macro
(define-syntax (sum-quant stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) int-expr)
     (quasisyntax/loc stx
       (let* ([x1 (node/expr/quantifier-var (nodeinfo #,(build-source-location stx)) (node/expr-arity r1) 'x1)] ...)
         (sum-quant-expr (nodeinfo #,(build-source-location stx)) (list (cons x1 r1) ...) int-expr)))]))

;; -- sealing (for examplar) -----------------------------------------------------------

(define (simple-write-proc str)
  (lambda (v port mode)
    (fprintf port "#<~a>" str)))

(struct node/formula/sealed node/formula []
  #:methods gen:custom-write [(define write-proc (simple-write-proc "node/formula/sealed"))])
(struct wheat node/formula/sealed []
  #:methods gen:custom-write [(define write-proc (simple-write-proc "wheat"))]
  #:extra-constructor-name make-wheat)
(struct chaff node/formula/sealed []
  #:methods gen:custom-write [(define write-proc (simple-write-proc "chaff"))]
  #:extra-constructor-name make-chaff)

(define (unseal-node/formula x)
  (if (node/formula/sealed? x)
    (node-info x)
    x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Build syntax for a generic equals/hash that's robust to new node subtypes

; Issue with this approach: struct-accessors is re-called every time equals? is invoked.
; Leaving it like this for now until it becomes a performance issue.

; Might think to promote struct-accessors into phase 2 and invoke it from within
;  the builder macros, but since macros work outside-in, can't just do something like
; (printf "accessors: ~a~n" (struct-accessors #'structname))
;   ^ the macro gets #'structname, not the actual structure name.

; Macro to get all accessors
; Thanks to Alexis King:
; https://stackoverflow.com/questions/41311604/get-a-structs-field-names
; requires installing syntax-classes package
(require (for-meta 1 racket/base
                     syntax/parse/class/struct-id)
         syntax/parse/define)

  (define-simple-macro (struct-accessors id:struct-id)
    (begin ;(printf "~a~n" (list id.accessor-id ...))
           (list id.accessor-id ...)))

; Use this macro to produce syntax (for use in operator-registration macro)
;   that builds a comparator including all struct fields except for node-info
(define-syntax (make-robust-node-equal-syntax stx)
  (syntax-case stx ()
    [(_ structname)
     (begin
       ; don't want to call struct-accessors every time this lambda is invoked,
       ; so call once at expansion time of make-robust...
       ;(printf "structname: ~a~n" (syntax->datum #'structname))       
       #`(lambda (a b equal-proc)           
           (andmap (lambda (access)
                     ;(printf "checking equality for ~a, proc ~a~n" 'structname access)
                     (equal-proc (access a) (access b)))
                   (remove node-info (struct-accessors structname)))))]))

; And similarly for hash
(define multipliers '(3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71))
(define-simple-macro (make-robust-node-hash-syntax structname offset)
  (lambda (a hash-proc)
    (define multiplied
      (for/list ([access (remove node-info (struct-accessors structname))]
                 [multiplier (drop multipliers offset)])
        (* multiplier (hash-proc (access a)))))
    (apply @+ multiplied)))
