#lang racket

(require (prefix-in logging: forge/logging/logging))
(require (except-in forge/sigs 
                    run check test example)
         (prefix-in unlogged: forge/sigs))
(require syntax/parse/define)

(provide (all-from-out forge/sigs))
(provide run check test example)

(define-simple-macro (run name args ...)
  (begin
    (unlogged:run name args ...)
    (set! name (logging:log-run name))))

(define-simple-macro (check name args ...)
  (begin
    (unlogged:check name args ...)
    (set! name (logging:log-run name "check"))))

(define (get-unsat-data first-instance)
  (if (Unsat-core first-instance)
      (for/list ([node (Unsat-core first-instance)])
        (format "~a" node))
      #f))

(define (get-sat-data first-instance)
  (for/list ([instance (Sat-instances first-instance)])
    (for/hash ([(relation-name tuples) instance])
      (define stringified-atoms
        (for/list ([tuple tuples])
          (for/list ([atom tuple])
            (format "~a" atom))))
      (values relation-name stringified-atoms))))

(define-simple-macro (test name args ... #:expect expected)
  #:with command-str (format "~a" (syntax->datum #'(test name args ... #:expected expected)))
  (cond 
    [(member 'expected '(sat unsat))
     (unlogged:run name args ...)
     (define first-instance (stream-first (forge:Run-result name)))
     (define passed (equal? (if (Sat? first-instance) 'sat 'unsat) 'expected))
     (logging:log-test name 'expected passed 'command-str
                       (if (Sat? first-instance)
                           (get-sat-data first-instance)
                           (get-unsat-data first-instance)))
     (unless passed
       (raise (format "Failed test ~a. Expected ~a, got ~a.~a"
                      'name 'expected (if (Sat? first-instance) 'sat 'unsat)
                      (if (Sat? first-instance)
                          (format " Found instance ~a" first-instance)
                          (if (Unsat-core first-instance)
                              (format " Core: ~a" (Unsat-core first-instance))
                              "")))))
     (forge:close-run name)]

    [(equal? 'expected 'theorem)
     (unlogged:check name args ...)
     (define first-instance (stream-first (forge:Run-result name)))
     (logging:log-test name 'theorem (Unsat? first-instance) 'command-str
                            (if (Sat? first-instance)
                                (get-sat-data first-instance)
                                (get-unsat-data first-instance)))
     (when (Sat? first-instance)
       (raise (format "Theorem ~a failed. Found instance:~n~a"
                      'name first-instance)))
     (forge:close-run name)]

    [else (raise (format "Illegal argument to test. Received ~a, expected sat, unsat, or theorem."
                         'expected))]))

(define-simple-macro (example name:id ex-pred ex-bounds ...)
  #:with command-str (format "~a" (syntax->datum #'(example name ex-pred ex-bounds ...)))
  (let ()
    (unlogged:run name #:preds [ex-pred]
                       #:bounds [ex-bounds ...])
    (define first-instance (stream-first (forge:Run-result name)))
    (logging:log-test name 'example (Sat? first-instance) 'command-str
                           (hash 'pred (format "~a" 'ex-pred)
                                 'bounds (for/list ([bound '(ex-bounds ...)]) (format "~a" bound))))
    (unless (Sat? first-instance)
      (raise (format "Failed example ~a." 'name)))
    (forge:close-run name)))

