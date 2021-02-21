#lang racket

(require forge/sigs-structs)
(require forge/translate-from-kodkod-cli)
(require forge/shared)
(require json)
(require basedir)
(require request)
(require net/url-string)
(require sha)

(provide log-execution log-run log-test log-errors flush-logs log-check-ex-spec log-notification)

(define (drracket-background-expanding? data-file)
  ;; alternate idea: look for the "drracket-background-compilation" logger ... try `log-level?` or looking for events with a `make-log-receiver`
  (with-handlers ([drracket-access-exn? (lambda (x) #true)])
    (with-output-to-file data-file #:exists 'append (lambda () (void)))
    #false))

(define (drracket-access-exn? x)
  (and (exn:fail? x)
       (regexp-match? #rx"forbidden .* access" (exn-message x))))

(define (safe-make-parent-directory* filename)
  (with-handlers ([exn:fail? (lambda (x) #false)])
    (file-or-directory-permissions (path-only filename) #o777)
    (make-parent-directory* filename)
    filename))

(define user-data-file
  (let ([user-data-file (writable-config-file "user-data.json" #:program "forge")])
    (cond
      [(file-exists? user-data-file)
       (and (not (drracket-background-expanding? user-data-file))
            user-data-file)]
      [else
       (and (safe-make-parent-directory* user-data-file)
            (not (drracket-background-expanding? user-data-file))
            (call-with-output-file user-data-file
                                   #:exists 'append
                                   (curry write-json (hash 'users '()
                                                           'projects '())))
            user-data-file)])))

(define log-file
  (safe-make-parent-directory*
    (writable-data-file "user-logs.log" #:program "forge")))

(define log-post-url 
  (string->url "https://us-central1-pyret-examples.cloudfunctions.net/forge-logging"))
(define (flush-logs)
  (when (and (logging-on?) (file-exists? log-file))
    (println
      (with-handlers ([exn:fail:network? (thunk* #f)])
        (define log-lines (file->lines log-file))
        (define filtered (filter jsexpr? log-lines))
        (define num-all-logs (length log-lines))
        (define num-good-logs (length filtered))
        (when (> num-good-logs 0)
          (printf "LOGGING: Found ~a logs; ~a valid.~n" num-all-logs num-good-logs)
          (define payload (jsexpr->bytes (map string->jsexpr filtered)))
          (define response (post http-requester log-post-url payload))
          (println response)
          (and (equal? (http-response-code response) 201)
               (call-with-output-file log-file (thunk* #t) #:exists 'replace)))))))

(define (write-log value)
  (when (logging-on?)
    (call-with-output-file log-file 
                           (lambda (port)
                             (write-json value port)
                             (newline port)) 
                           #:exists 'append)))

(define (verify-header source-user source-project filename)
  (define user-data (call-with-input-file user-data-file read-json))
  (define user-index (index-where (hash-ref user-data 'users)
                                  (lambda (user)
                                    (equal? source-user (hash-ref user 'email)))))

  (define updated-user-data
    (if user-index
        (let ([user (list-ref (hash-ref user-data 'users) user-index)])
          (if (member filename (hash-ref user 'files))
              user-data
              (let ()
                (displayln "Warning: new file detected.")
                ; (display (string-append "We do not have the current file in our system. "
                ;                         "Please select 0 if this is a new file, or "
                ;                         "if the file was moved from another location, "
                ;                         "please select that file: \n"
                ;                         "0) New file\n"))
                ; (for ([filename (hash-ref user 'files)]
                ;       [file-num (in-naturals)])
                ;   (displayln (format "~a) ~a" file-num filename))))
              (hash-update user-data 'users
                           (lambda (users)
                             (list-set users user-index 
                                       (hash-update user 'files
                                                    (curry cons filename))))))))

        (let ()
          ; Verify user
          (display (string-append "It seems you are a new user. "
                                  "If so, please retype your email to verify: "))
          (define verify-user (read-line))
          (unless (equal? source-user verify-user)
            (raise "Email verification failed."))

          ; Add user to data
          (hash-update user-data 'users
                       (lambda (users)
                         (cons (hash 'email source-user
                                     'files (list filename))
                               users))))))

  (unless (member source-project (hash-ref user-data 'projects))
    (display (string-append "Please retype the project name to verify: "))
    (define verify-project (read-line))
    (unless (equal? source-project verify-project)
      (raise "Project verification failed."))
    (set! updated-user-data
      (hash-update user-data 'projects
                   (curry cons source-project))))

  (call-with-output-file user-data-file 
                         (curry write-json updated-user-data)
                         #:exists 'replace))

(define logging-on? (make-parameter #f))

; {
;     "log-type": "execution",
;     "user": "<student>@cs.brown.edu",
;     "filename": "/User/<username>/Documents/cs1950y/forge1.rkt",
;     "project": "forge1",
;     "time": 12345987023458,
;     "raw": "#lang forge/core\n...",
;     "mode": "forge/core",
; }
(define (log-execution language port path)
  (define peek-port (peeking-input-port port))
  (define project (read peek-port))
  (define user (read peek-port))
  (close-input-port peek-port)

  (if (and (string? project) (string? user))
      (let ((got-data-file? (and (path-string? user-data-file)
                                 (path-string? log-file))))
        (logging-on? got-data-file?)
        (read port)
        (read port)
        (define filename (format "~a" path))
        (when (string-contains? filename "unsaved-editor")
          (raise "Please save file before running."))
        (define logged-name (format "~a.~a" (file-name-from-path path) 
                                            (sha256 (string->bytes/utf-8 filename))))
        (define time (current-seconds))
        (define raw (file->string filename))
        (define mode (format "~a" language))

        (when got-data-file?
          (flush-logs)
          (verify-header user project filename)

          (write-log (hash 'log-type "execution"
                           'user user
                           'filename logged-name
                           'project project
                           'time time
                           'raw raw
                           'mode mode)))
        (values got-data-file? project user))

      (let ()
        (logging-on? #f)
        (if (equal? language 'forge/check-ex-spec)
            (values #f (read port) #f)
            (values #f #f #f)))))

; (struct Run (
;   name     ; Symbol
;   command  ; String (syntax)
;   run-spec ; Run-spec
;   result   ; Stream
;   atom-rels ; List<node/expr/relation>
;   ) #:transparent)
; {
;     "log-type": "run",
;     "raw": "(run my-run #:preds [...] ...)",
;     "run-id": 0,
;     "spec": {
;             "sigs": ["A", "B"],
;             "relations": ["r"],
;             "predicates": ["..."],
;             "bounds": ["..."],
; }
(define curr-run-id 0)
(define (next-run-id)
  (begin0
    curr-run-id
    (set! curr-run-id (add1 curr-run-id))))

(define (log-run run [log-type "run"]) ; TODO: MAKE WORK FOR CHECKS
  (if (logging-on?)
      (let ()
        (define run-id (next-run-id))

        (define logged-result (stream-map/once (curry log-instance run-id run )
                                               (Run-result run)))

        (define sigs (map (compose symbol->string Sig-name)
                          (get-sigs run)))
        (define relations (map (compose symbol->string Relation-name)
                               (get-relations run)))
        (write-log (hash 'log-type "run" ; log-type TODO
                         'raw (format "~a" (syntax->datum (Run-command run)))
                         'run-id run-id
                         'spec (hash 'sigs sigs
                                     'relations relations
                                     'predicates '()
                                     'bounds '())))
        (struct-copy Run run
                     [result logged-result]))
      run))

; {
;     "log-type": "instance",
;     "run-id": 0,
;     "label": "sat",
;     "sigs": {
;             "A": ["A0", "A1", "A2"],
;             "B": ["B0", "B1"],
;         },
;     "relations": {
;             "r": [["A0", "B0"], ["A0", "B1"], ["A1", "B1"]],
;         },
; }
(define (log-instance run-id run instance)
  (when (logging-on?)
    (cond
      [(and (Unsat? instance) (equal? (Unsat-kind instance) 'no-more-instances))
       (write-log (hash 'log-type "instance"
                        'run-id run-id
                        'label "no-more-instances"))]
      [(Unsat? instance)
       (write-log (hash 'log-type "instance"
                        'run-id run-id
                        'label "unsat"
                        'core (format "~a" (Unsat-core instance))))]
       
      [(Sat? instance)
       (define true-instances 
         (for/list ([true-instance (Sat-instances instance)])
           (for/hash ([(name atoms) true-instance])
             (values name 
                     (for/list ([tuple atoms])
                       (for/list ([atom tuple])
                         (format "~a" atom)))))))
       
       (write-log (hash 'log-type "instance"
                        'run-id run-id
                        'label "sat"
                        'instances true-instances))]))
  instance)

; {
;     "log-type": "test",
;     "raw": "(test my-test #:preds [...] ...)",
;     "expected": "sat",
;     "passed": true,
;     "spec": {
;             "sigs": ["A", "B"],
;             "relations": ["r"],
;             "predicates": ["..."],
;             "bounds": ["..."],
;         },
; }
(define (log-test test expected passed command-str data)
  (when (logging-on?)

    (define sigs (map (compose symbol->string Sig-name)
                      (get-sigs test)))
    (define relations (map (compose symbol->string Relation-name)
                           (get-relations test)))

    (write-log (hash 'log-type "test"
                     'raw command-str
                     'expected (symbol->string expected)
                     'passed passed
                     'data data
                     'spec (hash 'sigs sigs
                                 'relations relations
                                 'predicates '()
                                 'bounds '())))))

(define ((log-error default-exception-handler) err)
  (when (logging-on?)
    (write-log (hash 'log-type "error"
                     'message (if (exn? err)
                                  (exn-message err)
                                  (format "~a" err))))
    (flush-logs))
  (default-exception-handler err))

(define (log-notification message data)
  (when (logging-on?)
    (write-log (hash 'log-type "notification"
                     'message message
                     'data data
                     'time (current-seconds)))))

(require syntax/parse/define)
(define-simple-macro (log-errors commands ...)
  (begin
    (define old-exception-handler (uncaught-exception-handler))
    (uncaught-exception-handler (log-error old-exception-handler))
    commands ...
    (uncaught-exception-handler old-exception-handler)))

(define (log-check-ex-spec wheat-results chaff-results)
  (when (logging-on?)
    (define get-name (dynamic-require 'forge/check-ex-spec/library/commands 'test-report-name))
    (define get-passed? (dynamic-require 'forge/check-ex-spec/library/commands 'test-report-passed?))
    (define (to-jsexpr data)
      (for/list ([file data])
        (for/list ([test file])
          (hash 'test-name (symbol->string (get-name test))
                'passed (get-passed? test)))))
    (write-log (hash 'log-type "check-ex-spec"
                     'wheat-results (to-jsexpr wheat-results)
                     'chaff-results (to-jsexpr chaff-results)))))
