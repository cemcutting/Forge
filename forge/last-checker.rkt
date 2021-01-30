#lang racket

(require 
  "sigs-structs.rkt"
  "lang/ast.rkt"
  "shared.rkt"
  racket/syntax
  syntax/srcloc
  (prefix-in @ (only-in racket -> >=)))

(provide checkFormula checkExpression primify)

; Recursive descent for last-minute consistency checking
; Catch potential issues not detected by AST construction + generate warnings 

(define (checkFormula run-or-state formula quantvars)
  (when (@>= (get-verbosity) VERBOSITY_DEBUG)
    (printf "last-checker: checkFormula: ~a~n" formula))
  
  (match formula    
    [(node/formula/constant info type)
     #f]
    
    [(node/formula/op info args)
     (checkFormulaOp run-or-state formula quantvars args)]
        
    [(node/formula/multiplicity info mult expr)
      (checkExpression run-or-state expr quantvars)]
    
    [(node/formula/quantified info quantifier decls subform)
     (for-each
      (lambda (decl)
        (let ([var (car decl)]
              [domain (cdr decl)])
          ; CHECK: shadowed variables
          (when (assoc var quantvars)
            (raise-syntax-error #f (format "Shadowing of variable ~a detected. Check for something like \"some x: A | some x : B | ...\"." var)
                                (datum->syntax #f var (build-source-location-syntax (nodeinfo-loc info)))))
          ; CHECK: recur into domain(s)
          (checkExpression run-or-state domain quantvars)))
      decls)

     ; Extend domain environment
     (let ([new-quantvars (append (map assocify decls) quantvars)])       
       ; CHECK: recur into subformula
       (checkFormula run-or-state subform new-quantvars))]    

    [(node/formula/sealed info)
     (checkFormula run-or-state info quantvars)]

    [else (error (format "no matching case in checkFormula for ~a" formula))]))

(define (assocify a-pair)  
  (list (car a-pair) (cdr a-pair)))


; This function isn't technically needed at the moment: every branch just recurs
; However, keeping the structure here for easy addition of new checks
(define (checkFormulaOp run-or-state formula quantvars args)  
  (when (@>= (get-verbosity) VERBOSITY_DEBUG)
    (printf "last-checker: checkFormulaOp: ~a~n" formula))

  (match formula
    
    ; TEMPORAL OPERATORS
    [(? node/formula/op/always?) (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    [(? node/formula/op/eventually?) (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    [(? node/formula/op/until?) (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    [(? node/formula/op/releases?) (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    [(? node/formula/op/after?) (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    
    ; AND 
     [(? node/formula/op/&&?)
      (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]

    ; OR
    [(? node/formula/op/||?)
     (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    
    ; IMPLIES
    [(? node/formula/op/=>?)
     (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    
    ; IN (atomic fmla)
    [(? node/formula/op/in?)
     (for-each (lambda (x) (checkExpression run-or-state x quantvars)) args)]
    
    ; EQUALS 
    [(? node/formula/op/=?)
     (for-each (lambda (x) (checkExpression run-or-state x quantvars)) args)]

    ; NEGATION
    [(? node/formula/op/!?)
     (for-each (lambda (x) (checkFormula run-or-state x quantvars)) args)]
    
    ; INTEGER >
    [(? node/formula/op/int>?)
     (void)]
    ; INTEGER <
    [(? node/formula/op/int<?)
     (void)]
    ; INTEGER =
    [(? node/formula/op/int=?)
     (void)]))

; Turn signame into list of all primsigs it contains
; Note we use Alloy-style "_remainder" names here; these aren't necessarily embodied in Forge
(define/contract (primify run-or-state raw-signame)
  (@-> (or/c Run? State? Run-spec?) (or/c symbol? string?) (listof symbol?))  
  (let ([signame (cond [(string? raw-signame) (string->symbol raw-signame)]
                       [(Sig? raw-signame) (Sig-name raw-signame)]
                       [else raw-signame])])
    (cond [(equal? 'Int signame)           
           '(Int)]
          [(equal? 'univ signame)           
           (remove-duplicates (flatten (map (lambda (n) (primify run-or-state n)) (cons 'Int (map Sig-name (get-sigs run-or-state))))))]
          [else           
           (define the-sig (get-sig run-or-state signame))
           (define all-primitive-descendants
             (remove-duplicates
              (flatten
               (map (lambda (n) (primify run-or-state n))
                    (get-children run-or-state signame)))))
           (cond
             [(Sig-abstract the-sig)
              all-primitive-descendants]
             [else (cons (string->symbol (string-append (symbol->string signame) "_remainder"))
                         all-primitive-descendants)])])))

; For expressions, this descent does two things:
;   - collects possible typings of expressions
;   - throws syntax errors as needed (using typing info from children)
(define/contract (checkExpression run-or-state expr quantvars)
  (@-> (or/c Run? State? Run-spec?) node/expr? list? (listof (listof symbol?)))

  (when (@>= (get-verbosity) VERBOSITY_DEBUG)
    (printf "last-checker: checkExpression: ~a~n" expr))
  
  (define (primifyThis n)
    (primify run-or-state n))
  
  (match expr

    ; relation name (base case)
    [(node/expr/relation info arity name typelist parent isvar)     
     (apply cartesian-product (map primifyThis typelist))]

    ; atom (base case)
    [(node/expr/atom info arity name)
     ; overapproximate for now (TODO: get atom's sig)
     (primify run-or-state 'univ)]
    
    [(node/expr/ite info arity a b c)     
     (checkFormula run-or-state a quantvars) ; Check condition formula
     (let ([b-potentials (checkExpression run-or-state b quantvars)]
           [c-potentials (checkExpression run-or-state c quantvars)])
       ; Might be a or b, we don't know
       (remove-duplicates (append b-potentials c-potentials)))]
    
    ; The INT Constant
    [(node/expr/constant info 1 'Int)
       (list (list 'Int))]

    ; other expression constants
    [(node/expr/constant info arity type)
     (let ([prims (primify run-or-state 'univ)])
       (cond [(equal? arity 1)
              (map list prims)]
             [else     
              (cartesian-product prims prims)]))]
    
    ; expression w/ operator (union, intersect, ~, etc...)
    [(node/expr/op info arity args)
     (checkExpressionOp run-or-state expr quantvars args)]
 
    ; quantifier variable
    [(node/expr/quantifier-var info arity sym)
     ; Look up in quantvars association list, type is type of domain
     (if (assoc expr quantvars) ; expr, not sym (decls are over var nodes)
         (checkExpression run-or-state (second (assoc expr quantvars)) quantvars)
         (raise-syntax-error #f (format "Variable ~a used but was unbound in overall formula being checked. Bound variables: ~a" sym (map car quantvars) )
                             (datum->syntax #f sym (build-source-location-syntax (nodeinfo-loc info)))))]

    ; set comprehension e.g. {n : Node | some n.edges}
    [(node/expr/comprehension info arity decls subform)
     (define child-values       
       (map
        (lambda (decl)
          (let ([var (car decl)]
                [domain (cdr decl)])
            ; CHECK: shadowed variables
            (when (assoc var quantvars)
              (raise-syntax-error #f (format "Shadowing of variable ~a detected. Check for something like \"some x: A | some x : B | ...\"." var)
                                  (datum->syntax #f var (build-source-location-syntax (nodeinfo-loc info)))))
            ; CHECK: recur into domain(s)
            (checkExpression run-or-state domain quantvars))) decls))

     ; Extend domain environment
     (let ([new-quantvars (append (map assocify decls) quantvars)])       
       ; CHECK: recur into subformula
       (checkFormula run-or-state subform new-quantvars))

     ; Return type constructed from decls above
     (map flatten (map append (apply cartesian-product child-values)))]

    [else (error (format "no matching case in checkExpression for ~a" expr))]))


(define (keep-only keepers pool)
  (filter (lambda (ele) (member ele keepers)) pool))

(define/contract (checkExpressionOp run-or-state expr quantvars args)
  (@-> (or/c Run? State? Run-spec?) node/expr/op? list? (listof (or/c node/expr? node/int?))   
       (listof (listof symbol?)))
  (when (@>= (get-verbosity) VERBOSITY_DEBUG)
    (printf "last-checker: checkExpressionOp: ~a~n" expr))

  (define RESULT
  (match expr

    ; prime
    [(? node/expr/op/prime?)
     (checkExpression run-or-state (first args) quantvars)]

    ; UNION
    [(? node/expr/op/+?)
     (remove-duplicates (apply append (map (lambda (x) (checkExpression run-or-state x quantvars)) args)))]

    [(? node/expr/op/<:?)
     (remove-duplicates (apply append (map (lambda (x) (checkExpression run-or-state x quantvars)) args)))]
    
    ; SETMINUS 
    [(? node/expr/op/-?)
     ; A-B should have only 2 children. B may be empty.
     (checkExpression run-or-state (first args) quantvars)]
    
    ; INTERSECTION
    [(? node/expr/op/&?)
     (foldl
      (lambda (x acc)
        (keep-only (checkExpression run-or-state x quantvars) acc))
      (checkExpression run-or-state (first args) quantvars)
      (rest args))]
    
    ; PRODUCT
    [(? node/expr/op/->?)
     (let* ([child-values (map (lambda (x) (checkExpression run-or-state x quantvars)) args)]
            [result (map flatten (map append (apply cartesian-product child-values)))])       
       result)]
   
    ; JOIN
    [(? node/expr/op/join?)
     (let* ([child-values (map (lambda (x) (checkExpression run-or-state x quantvars)) args)]
            [join-result (check-join child-values)])
       (when (@>= (get-verbosity) VERBOSITY_LASTCHECK) 
         (when (empty? join-result)
           (raise-syntax-error #f (format "join always results in an empty relation")
                               (datum->syntax #f expr (build-source-location-syntax (nodeinfo-loc (node-info expr)))))))
         join-result)]
    
    ; TRANSITIVE CLOSURE
    [(? node/expr/op/^?)
    (let* ([child-values (map (lambda (x) (checkExpression run-or-state x quantvars)) args)])     
      (check-closure (first child-values)))]

    ; REFLEXIVE-TRANSITIVE CLOSURE
    [(? node/expr/op/*?)
     ; includes iden, so might contain any arity-2 tuple
     (let ([prims (primify run-or-state 'univ)])
       (cartesian-product prims prims))]

    ; TRANSPOSE: ~(r); r must be arity 2. reverse all types of r
    [(? node/expr/op/~?)
      (map reverse (checkExpression run-or-state (first args) quantvars))]
    
    ; SINGLETON (typecast number to 1x1 relation with that number in it)
    [(? node/expr/op/sing?)
     (list (list 'Int))]))
;  (printf "result for ~a was ~a~n" expr RESULT)
  RESULT)

(define/contract (check-closure lst)
  (@-> (listof (listof symbol?)) (listof (listof symbol?)))
  (define one-more (check-join (list lst lst)))
  (define new-candidate (remove-duplicates (append lst one-more)))  
  (if (equal? (list->set new-candidate) (list->set lst))
      new-candidate
      (check-closure new-candidate)))  

; since join is n-ary, pass *list* of typelist
(define/contract (check-join child-values)
  (@-> (listof (listof (listof symbol?))) (listof (listof symbol?)))
  (let ([product-of-children (apply cartesian-product child-values)])
    (remove-duplicates
     (filter-map
      (lambda (l) (foldl
                   (lambda (nxt sofar)
                     (if (and sofar (equal? (first nxt) (last sofar)))
                         (append (drop-right sofar 1) (drop nxt 1))
                         #f))
                   (first l)
                   (rest l)))
      product-of-children))))

(module+ test
  (require rackunit)
  ;(printf "Testing last-checker~n")
  (check-equal?
   (list->set (check-join '( ((n1 a) (n2 b) (n2 c) (n3 c) (n4 d))
                             ((a x) (k x) (c y) (c z) (e k))
                             ((y n100) (z n200)))))
   (list->set '((n2 n100) (n2 n200) (n3 n100) (n3 n200))))
  
  )
