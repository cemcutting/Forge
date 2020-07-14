#lang br/quicklang

(define-syntax-rule (forge-core-module-begin cmds ...)
  (#%module-begin
    (provide (all-defined-out))
    cmds ...))
(provide (rename-out [forge-core-module-begin #%module-begin]))

(require "../../sigs.rkt")
(provide (all-from-out "../../sigs.rkt"))
(provide require)