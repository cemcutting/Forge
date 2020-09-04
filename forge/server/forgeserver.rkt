#lang racket

(require (only-in "../lang/ast.rkt" relation-name)
         "modelToXML.rkt" xml
         net/sendurl "../racket-rfc6455/net/rfc6455.rkt" net/url web-server/http/request-structs racket/runtime-path
         racket/async-channel
         racket/hash)
(require "eval-model.rkt")
; TODO: remove this once evaluator is in; just want to show we can evaluate something

(require "../lang/reader.rkt")
(require "../shared.rkt")
(require "../lang/reader.rkt")

(provide display-model)

;(define-runtime-path sterling-path "../sterling-js/dist/index.html")
(define-runtime-path sterling-path "../sterling/build/index.html")

; name is the name of the model
; get-next-model returns the next model each time it is called, or #f.
(define (display-model get-next-model name command filepath bitwidth funs-n-preds [show #t])
  (define model (get-next-model))
  ;(printf "Instance : ~a~n" model)
  (define chan (make-async-channel))

  (define stop-service
    (ws-serve
     ; This is the connection handler function, it has total control over the connection
     ; from the time that conn-headers finishes responding to the connection request, to the time
     ; the connection closes. The server generates a new handler thread for this function
     ; every time a connection is initiated.
     (λ (connection _)
       (let loop ()

         ; The only thing we should be receiving is next-model requests, current requests (from a new connection), and pings.
         (define m (ws-recv connection))

         (unless (eof-object? m)
           ;(println m)
           (cond [(equal? m "ping")
                  (ws-send! connection "pong")]
                 [(equal? m "current")
                  (ws-send! connection (model-to-XML-string model name command filepath bitwidth forge-version))]
                 [(equal? m "next")
                  (set! model (get-next-model))
                  (ws-send! connection (model-to-XML-string model name command filepath bitwidth forge-version))]
                 [(string-prefix? m "EVL:") ; (equal? m "eval-exp")
                  (define parts (regexp-match #px"^EVL:(\\d+):(.*)$" m))
                  (define command (third parts))
                  
                  (define result (case command 
                    [("--version" "-v") forge-version]
                    [("--file" "-f") filepath]
                    [else (with-handlers (
                        ;[exn:fail:read? (λ (exn) (println exn) "syntax error")]
                        ;[exn:fail:parsing? (λ (exn) (println exn) "syntax error")]
                        [exn:fail:contract? (λ (exn) (println exn) "error")]
                        [exn:fail? (λ (exn) (println exn) "syntax error")]
                      )

                      (define port (open-input-string (string-append "eval " command)))
                      (define stxFromEvaluator (read-syntax 'Evaluator port))
                      (define alloy (third (last (syntax->datum stxFromEvaluator))))
                      ;(printf "alloy: ~a~n" alloy)
                      (define kodkod (alloy->kodkod alloy))
                      ;(printf "kodkod: ~a~n" kodkod)
                      (define binding (model->binding (cdr model) bitwidth))
                      ;(printf "funs-n-preds : ~a~n" funs-n-preds)
                      (set! binding (hash-union binding funs-n-preds))
                      ;(printf "binding: ~a~n" binding)
                      (define lists (eval-unknown kodkod binding bitwidth))
                      ;(printf "lists: ~a~n" lists)
                      (if (list? lists)
                          (string-join (for/list ([l lists])
                              (string-join (for/list ([atom l])
                                (cond
                                  [(int-atom? atom) (int-atom->string atom)]
                                  [(number? atom) (number->string atom)]
                                  [(symbol? atom) (symbol->string atom)])
                              ) "->")
                              ) " + ")
                          lists)
                      )]
                    ))
                  ;(println result)
                  (ws-send! connection (format "EVL:~a:~a" (second parts) result))]
                 [else
                  (ws-send! "BAD REQUEST")])
           (loop))))
     #:port 0 #:confirmation-channel chan))

  (define port (async-channel-get chan))

  (when show 
        (cond [(string? port)
         (displayln "NO PORTS AVAILABLE!!")]
        [else
         (send-url/file sterling-path #f #:query (number->string port))
         (printf "Sterling running. Hit enter to stop service.\n")
         (void (read-char))
         (stop-service)])))
