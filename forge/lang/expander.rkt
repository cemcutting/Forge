#lang racket

(require (for-syntax syntax/parse)
         (for-syntax (for-syntax syntax/parse)))
(require syntax/parse/define
         (for-syntax syntax/parse/define))
(require (for-syntax (for-syntax racket/base)))
(require (for-syntax racket/function
                     syntax/srcloc))
(require forge/sigs)
; (require "ast.rkt")


(provide #%module-begin)
(provide #%top #%app #%datum #%top-interaction)

(provide require provide all-defined-out except-out prefix-in)
(provide forge:nsa define-namespace-anchor)
; (provide (all-from-out "ast.rkt"))
(provide (all-from-out forge/sigs))
(provide (all-defined-out))
(begin-for-syntax (provide (all-defined-out)))

(begin-for-syntax
  (define-syntax-parser make-token
    [(make-token token-class:id token-string:str token-symbol)
     #'(define-syntax-class token-class
         (pattern token-string
           #:attr symbol #'token-symbol))])

  (make-token abstract-tok "abstract" #:abstract))

(define-for-syntax (my-expand stx)
  (define core-funcs-and-macros
    (map (curry datum->syntax stx)
         '(^ * ~ + - & join
           -> => implies ! not and or && || ifte iff <=>
           = in ni != !in !ni is
           no some one lone all set two
           < > int= >= <=
           add subtract multiply divide sign abs remainder
           card sum sing succ max min sum-quant
           node/int/constant
           let)))

  (define result (local-expand stx 'expression core-funcs-and-macros))
  result)


(begin-for-syntax
  ; AlloyModule : ModuleDecl? Import* Paragraph*
  ;             | EvalDecl*
  ; (define-syntax-class AlloyModuleClass
  ;   (pattern ((~literal AlloyModule)
  ;             (~optional module-decl:ModuleDeclClass)
  ;             (~seq import:ImportClass ...)
  ;             (~seq paragraph:ParagraphClass ...)))
  ;   (pattern ((~literal AlloyModule)
  ;             (~seq eval-decl:EvalDeclClass ...))))


  ; Header stuff

  ; ModuleDecl : /MODULE-TOK QualName (LEFT-SQUARE-TOK NameList RIGHT-SQUARE-TOK)?
  (define-syntax-class ModuleDeclClass
    (pattern ((~literal ModuleDecl)
              module-name:QualNameClass
              (~optional (~seq "[" other-names:NameListClass "]")))))

  ; Import : OPEN-TOK QualName (LEFT-SQUARE-TOK QualNameList RIGHT-SQUARE-TOK)? (AS-TOK Name)?
  (define-syntax-class ImportClass
    (pattern ((~literal Import)
              import-name:QualNameClass
              (~optional (~seq "[" other-names:QualNameListClass "]"))
              (~optional (~seq "as" as-name:NameClass))))
    (pattern ((~literal Import)
              file-path:str
              (~optional (~seq "as" as-name:NameClass)))))


  ; Main Decls

  ; EvalDecl : EVAL-TOK Expr
  (define-syntax-class EvalDeclClass
    (pattern ((~literal EvalDecl)
              "eval"
              exp:ExprClass)))

  ; @Paragraph : SigDecl | FactDecl | PredDecl | FunDecl | AssertDecl 
  ;                      | CmdDecl | TestExpectDecl | SexprDecl | BreakDecl 
  ;                      | InstanceDecl | QueryDecl | StateDecl | TransitionDecl 
  ;                      | RelDecl | OptionDecl | InstDecl | TraceDecl
  (define-syntax-class ParagraphClass
    (pattern decl:SigDeclClass)
    (pattern decl:FactDeclClass)
    (pattern decl:PredDeclClass)
    (pattern decl:FunDeclClass)
    (pattern decl:AssertDeclClass)
    (pattern decl:CmdDeclClass)
    (pattern decl:TestExpectDeclClass)
    (pattern decl:SexprDeclClass)
    ; (pattern decl:BreakDeclClass)
    ; (pattern decl:InstanceDeclClass)
    ; (pattern decl:QueryDeclClass)
    ; (pattern decl:StateDeclClass)
    ; (pattern decl:TransitionDeclClass)
    (pattern decl:RelDeclClass)
    (pattern decl:OptionDeclClass)
    (pattern decl:InstDeclClass)
    (pattern decl:ExampleDeclClass))
    ; (pattern decl:TraceDeclClass))

  ;Used for Electrum stuff
  ;Used to declare var Sigs and Relations (so they can change over time)
  (define-syntax-class VarKeywordClass (pattern "var")) 

  ; SigDecl : VAR-TOK? ABSTRACT-TOK? Mult? /SIG-TOK NameList SigExt? /LEFT-CURLY-TOK ArrowDeclList? /RIGHT-CURLY-TOK Block?
  (define-syntax-class SigDeclClass
    (pattern ((~literal SigDecl)
              (~optional abstract:abstract-tok)
              (~optional mult:MultClass)
              (~optional isv:VarKeywordClass #:defaults ([isv #'#f]))
              sig-names:NameListClass
              ;when extending with in is implemented,
              ;if "sig A in B extends C" is allowed,
              ;check if this allows multiple SigExtClasses / how to do that if not
              ;note the parser currently does not allow that
              (~optional extends:SigExtClass)
              (~optional relation-decls:ArrowDeclListClass)
              (~optional block:BlockClass))))

  ; SigExt : EXTENDS-TOK QualName 
  ;        | IN-TOK QualName (PLUS-TOK QualName)*
  (define-syntax-class SigExtClass
    (pattern ((~literal SigExt)
              "extends"
              name:QualNameClass)
      #:attr symbol #'#:extends
      #:attr value #'name.name)
    (pattern ((~literal SigExt)
              "in" 
              name:QualNameClass
              (~seq (~seq "+" names:QualNameClass) ...))
      #:attr symbol #'#:in
      #:attr value #'(raise "Extending with in not yet implemented.")))

  ; Mult : LONE-TOK | SOME-TOK | ONE-TOK | TWO-TOK
  (define-syntax-class MultClass
    (pattern ((~literal Mult) "lone") #:attr symbol #'#:lone)
    (pattern ((~literal Mult) "some") #:attr symbol #'#:some)
    (pattern ((~literal Mult) "one") #:attr symbol #'#:one)
    (pattern ((~literal Mult) "two") #:attr symbol #'#:two))

  ; ArrowMult : LONE-TOK | SET-TOK | ONE-TOK | TWO-TOK
  (define-syntax-class ArrowMultClass
    (pattern ((~literal ArrowMult) "lone") #:attr symbol #'pfunc)
    (pattern ((~literal ArrowMult) "set") #:attr symbol #'default)
    (pattern ((~literal ArrowMult) "one") #:attr symbol #'func)
    (pattern ((~literal ArrowMult) "two") #:attr symbol #'(raise "relation arity two not implemented")))

  ; Decl : DISJ-TOK? NameList /COLON-TOK DISJ-TOK? SET-TOK? Expr
  (define-syntax-class DeclClass
    (pattern ((~literal Decl)
              (~optional "disj")
              names:NameListClass
              (~optional "disj")
              (~optional "set")
              expr:ExprClass)
      #:attr translate (with-syntax ([expr (my-expand #'expr)])
                         #'((names.names expr) ...))))

  ; DeclList : Decl
  ;          | Decl /COMMA-TOK @DeclList
  (define-syntax-class DeclListClass
    (pattern ((~literal DeclList)
              decls:DeclClass ...)
      #:attr translate (datum->syntax #'(decls ...) 
                                      (apply append 
                                             (map syntax->list 
                                                  (syntax->list #'(decls.translate ...)))))))

  ; ArrowDecl : DISJ-TOK? NameList /COLON-TOK DISJ-TOK? ArrowMult ArrowExpr
  (define-syntax-class ArrowDeclClass
    (pattern ((~literal ArrowDecl)
              (~optional "disj")
              (~optional isv:VarKeywordClass #:defaults ([isv #'#f])) ; electrum
              name-list:NameListClass
              (~optional "disj") 
              mult-class:ArrowMultClass
              type-list:ArrowExprClass)
      #:attr names #'(name-list.names ...)
      #:attr types #'type-list.names
      #:attr mult #'mult-class.symbol
      #:attr is-var #'isv))

  ; ArrowDeclList : ArrowDecl
  ;               | ArrowDecl /COMMA-TOK @ArrowDeclList
  (define-syntax-class ArrowDeclListClass
    (pattern ((~literal ArrowDeclList)
              arrow-decl:ArrowDeclClass ...)))

  ; ArrowExpr : QualName
  ;           | QualName /ARROW-TOK @ArrowExpr
  (define-syntax-class ArrowExprClass
    (pattern ((~literal ArrowExpr)
              name-list:QualNameClass ...)
      #:attr names #'(name-list.name ...)))

  ; FactDecl : FACT-TOK Name? Block
  (define-syntax-class FactDeclClass
    (pattern ((~literal FactDecl)
              "fact" 
              (~optional name:NameClass)
              block:BlockClass)))

  (define-syntax-class PredTypeClass
    #:datum-literals (PredType)
    #:attributes (sym)
    (pattern (PredType "wheat")
      #:attr sym #'wheat)
    (pattern (PredType "chaff")
      #:attr sym #'chaff))

  ; PredDecl : /PRED-TOK PredType? (QualName DOT-TOK)? Name ParaDecls? Block
  (define-syntax-class PredDeclClass
    (pattern ((~literal PredDecl)
              (~optional :PredTypeClass)
              (~optional (~seq prefix:QualNameClass "."))
              name:NameClass
              (~optional decls:ParaDeclsClass)
              block:BlockClass)))

  ; FunDecl : /FUN-TOK (QualName DOT-TOK)? Name ParaDecls? /COLON-TOK Expr Block
  (define-syntax-class FunDeclClass
    (pattern ((~literal FunDecl)
              (~optional (~seq prefix:QualNameClass "."))
              name:NameClass
              (~optional decls:ParaDeclsClass)
              output:ExprClass
              block:BlockClass)))

  ; ParaDecls : /LEFT-PAREN-TOK @DeclList? /RIGHT-PAREN-TOK 
  ;           | /LEFT-SQUARE-TOK @DeclList? /RIGHT-SQUARE-TOK
  ; DeclList : Decl
  ;          | Decl /COMMA-TOK @DeclList
  (define-syntax-class ParaDeclsClass
    (pattern ((~literal ParaDecls)
              (~seq decls:DeclClass ...))
      #:attr translate (datum->syntax #'(decls ...)
                                      (apply append (map (compose (curry map car )
                                                                  (curry map syntax->list )
                                                                  syntax->list) 
                                                         (syntax->list #'(decls.translate ...)))))))

  ; AssertDecl : /ASSERT-TOK Name? Block
  (define-syntax-class AssertDeclClass
    (pattern ((~literal AssertDecl)
              (~optional name:NameClass)
              block:BlockClass)))

  ; CmdDecl :  (Name /COLON-TOK)? (RUN-TOK | CHECK-TOK) Parameters? (QualName | Block)? Scope? (/FOR-TOK Bounds)?
  (define-syntax-class CmdDeclClass
    (pattern ((~literal CmdDecl)
              (~optional name:NameClass)
              (~or "run" "check")
              (~optional parameters:ParametersClass)
              (~optional (~or pred-name:QualNameClass
                              pred-block:BlockClass))
              (~optional scope:ScopeClass)
              (~optional bounds:BoundsClass))))

  ; TestDecl : (Name /COLON-TOK)? Parameters? (QualName | Block)? Scope? (/FOR-TOK Bounds)? /IS-TOK (SAT-TOK | UNSAT-TOK)
  (define-syntax-class TestDeclClass
    (pattern ((~literal TestDecl)
              (~optional name:NameClass)
              (~optional parameters:ParametersClass)
              (~optional (~or pred-name:QualNameClass
                              pred-block:BlockClass))
              (~optional scope:ScopeClass)
              (~optional bounds:BoundsClass)
              (~or "sat" "unsat" "theorem"))))

  ; TestBlock : /LEFT-CURLY-TOK TestDecl* /RIGHT-CURLY-TOK
  (define-syntax-class TestBlockClass
    (pattern ((~literal TestBlock)
              test-decls:TestDeclClass ...)))

  ; TestExpectDecl : TEST-TOK? EXPECT-TOK Name? TestBlock
  (define-syntax-class TestExpectDeclClass
    (pattern ((~literal TestExpectDecl)
              (~optional "test")
              "expect"
              (~optional name:NameClass)
              test-block:TestBlockClass)))

  (define-syntax-class ExampleDeclClass
    (pattern ((~literal ExampleDecl)
              (~optional name:NameClass)
              pred:ExprClass
              bounds:BoundsClass)))

  ; Scope : /FOR-TOK Number (/BUT-TOK @TypescopeList)? 
  ;       | /FOR-TOK @TypescopeList
  ; TypescopeList : Typescope
  ;               | Typescope /COMMA-TOK @TypescopeList
  (define-syntax-class ScopeClass
    (pattern ((~literal Scope)
              (~optional default:NumberClass)
              (~seq typescope:TypescopeClass ...))
      #:attr translate #'(typescope.translate ...)))

  ; Typescope : EXACTLY-TOK? Number QualName
  (define-syntax-class TypescopeClass
    (pattern ((~literal Typescope)
              (~optional (~and "exactly" exactly))
              num:NumberClass
              name:QualNameClass)
      #:attr translate (if (attribute exactly)
                           #'(name.name num.value num.value)
                           #'(name.name 0 num.value))))

  ; OptionDecl : /OPTION-TOK QualName (QualName | FILE-PATH-TOK | Number)
  (define-syntax-class OptionDeclClass
    #:attributes (n v)
    (pattern ((~literal OptionDecl) name:QualNameClass value:QualNameClass)
             #:attr n #'name.name
             #:attr v #'value.name)
    (pattern ((~literal OptionDecl) name:QualNameClass value:str)
             #:attr n #'name.name
             #:attr v #'value)
    (pattern ((~literal OptionDecl) name:QualNameClass value:NumberClass)
             #:attr n #'name.name
             #:attr v #'value.value)
    (pattern ((~literal OptionDecl) name:QualNameClass "-" value:NumberClass)
             #:attr n #'name.name
             #:attr v (quasisyntax #,(* -1 (syntax->datum #'value.value)))))

 
  ; Block : /LEFT-CURLY-TOK Expr* /RIGHT-CURLY-TOK
  (define-syntax-class BlockClass
    (pattern ((~literal Block)
              exprs:ExprClass ...)))

  ; Name : IDENTIFIER-TOK
  (define-syntax-class NameClass
    (pattern ((~literal Name)
              name:id)))

  ; NameList : @Name
  ;          | @Name /COMMA-TOK @NameList
  (define-syntax-class NameListClass
    (pattern ((~literal NameList)
              names:id ...)))

  ; QualName : (THIS-TOK /SLASH-TOK)? (@Name /SLASH-TOK)* @Name | INT-TOK | SUM-TOK
  (define-syntax-class QualNameClass
    #:attributes (name)
    (pattern ((~literal QualName)
              (~optional "this") ; TODO, allow more complex qualnames
              (~seq prefixes:id ...)
              raw-name:id)
      #:attr name #'raw-name)
    (pattern ((~literal QualName) "Int")
      #:attr name #'(raise "Int as qualname?"))
    (pattern ((~literal QualName) "sum")
      #:attr name #'(raise "sum as qualname?")))

  ; QualNameList : @QualName
  ;              | @QualName /COMMA-TOK @QualNameList
  (define-syntax-class QualNameListClass
    (pattern ((~literal QualNameList)
              (~or (~seq (~optional "this")
                         (~seq prefixes:id ...)
                         name:id)
                   "Int"
                   "sum") ...)))

  ; Number : NUM-CONST-TOK
  (define-syntax-class NumberClass
    (pattern ((~literal Number) n)
      #:attr value #'n))

  ; SexprDecl : Sexpr
  (define-syntax-class SexprDeclClass
    (pattern ((~literal SexprDecl) exp:SexprClass)))

  ; Sexpr : SEXPR-TOK
  (define-syntax-class SexprClass
    (pattern ((~literal Sexpr) exp)))

  ; InstDecl : /INST-TOK Name Bounds Scope?
  (define-syntax-class InstDeclClass
    (pattern ((~literal InstDecl)
              name:NameClass
              bounds:BoundsClass
              (~optional scope:ScopeClass))))

  ; RelDecl : ArrowDecl
  (define-syntax-class RelDeclClass
    (pattern ((~literal RelDecl) decl:ArrowDeclClass)))

  ; Parameters : /LeftAngle @QualNameList /RightAngle 
  (define-syntax-class ParametersClass
    (pattern ((~literal Parameters)
              name:QualNameClass ...)))

  ; Bounds : EXACTLY-TOK? @ExprList
  ;        | EXACTLY-TOK? @Block
  (define-syntax-class BoundsClass
    (pattern ((~literal Bounds)
              (~optional "exactly")
              exprs:ExprClass ...)
      #:attr translate (datum->syntax #'(exprs ...) 
                                      (map my-expand (syntax->list #'(exprs ...))))))

  ; EXPRESSIONS

  ; Const : NONE-TOK | UNIV-TOK | IDEN-TOK
  ;       | MINUS-TOK? Number 
  (define-syntax-class ConstClass
    #:attributes (translate)
    (pattern ((~literal Const) "none")
      #:attr translate (syntax/loc this-syntax none))
    (pattern ((~literal Const) "univ")
      #:attr translate (syntax/loc this-syntax univ))
    (pattern ((~literal Const) "iden")
      #:attr translate (syntax/loc this-syntax iden))
    (pattern ((~literal Const) n:NumberClass)
      #:attr translate (syntax/loc this-syntax (int n.value)))
    (pattern ((~literal Const) "-" n:NumberClass)
      #:attr translate (quasisyntax/loc this-syntax (int #,(* -1 (syntax->datum #'n.value))))))

  ; ArrowOp : (@Mult | SET-TOK)? ARROW-TOK (@Mult | SET-TOK)?
  ;         | STAR-TOK
  (define-syntax-class ArrowOpClass
    (pattern ((~literal ArrowOp)
              (~optional (~or "lone" "some" "one" "two" "set"))
              "->"
              (~optional (~or "lone" "some" "one" "two" "set"))))
    (pattern ((~literal ArrowOp) "*")))

  ; CompareOp : IN-TOK | EQ-TOK | LT-TOK | GT-TOK | LEQ-TOK | GEQ-TOK | EQUIV-TOK | IS-TOK | NI-TOK
  (define-syntax-class CompareOpClass
    (pattern ((~literal CompareOp)
              (~and op
                    (~or "in" "=" "<" ">" "<=" ">="
                         "==" "is" "ni")))
      #:attr symbol (datum->syntax #'op (string->symbol (syntax->datum #'op)))))

  ; LetDecl : @Name /EQ-TOK Expr
  (define-syntax-class LetDeclClass
    (pattern ((~literal LetDecl)
              name:id
              exp:ExprClass)
      #:attr translate (with-syntax ([exp (my-expand #'exp)]) 
                         #'(name exp))))

  ; LetDeclList : LetDecl
  ;             | LetDecl /COMMA-TOK @LetDeclList
  (define-syntax-class LetDeclListClass
    (pattern ((~literal LetDeclList)
              decls:LetDeclClass ...)
      #:attr translate #'(decls.translate ...)))

  ; BlockOrBar : Block | BAR-TOK Expr
  (define-syntax-class BlockOrBarClass
      #:attributes (exprs)
    (pattern ((~literal BlockOrBar) block:BlockClass)
      #:attr exprs (my-expand #'block))
    (pattern ((~literal BlockOrBar) "|" exp:ExprClass)
      #:attr exprs (my-expand #'exp)))

  ; Quant : ALL-TOK | NO-TOK | SUM-TOK | @Mult
  (define-syntax-class QuantClass
    (pattern ((~literal Quant) (~and q (~or "all" "no" "lone"
                                            "some" "one" "two")))
      #:attr symbol (datum->syntax #'q
                                   (string->symbol (syntax->datum #'q))))
    (pattern ((~literal Quant) (~literal sum))
      #:attr symbol (syntax/loc #'q sum-quant)))

  (define-syntax-class ExprClass
    (pattern ((~or (~literal Expr) (~literal Expr0.5) (~literal Expr1) (~literal Expr2) (~literal Expr3)
                   (~literal Expr4) (~literal Expr5) (~literal Expr6) (~literal Expr7) (~literal Expr7.5)
                   (~literal Expr8) (~literal Expr9) (~literal Expr10) (~literal Expr11)
                   (~literal Expr12) (~literal Expr13) (~literal Expr14) (~literal Expr15)
                   (~literal Expr16) (~literal Expr17))
             _ ...)))

  ; ExprList : Expr
  ;          | Expr /COMMA-TOK @ExprList
  (define-syntax-class ExprListClass
    (pattern ((~literal ExprList)
              exprs:ExprClass ...))))



; AlloyModule : ModuleDecl? Import* Paragraph*
;             | EvalDecl*
(define-syntax (AlloyModule stx)
  (syntax-parse stx
    [((~literal AlloyModule) (~optional module-decl:ModuleDeclClass)
                             (~seq import:ImportClass ...)
                             (~seq paragraph:ParagraphClass ...))
     (syntax/loc stx (begin
     (~? module-decl)
     import ...
     paragraph ...))]
    [((~literal AlloyModule) ((~literal EvalDecl) "eval" expr:ExprClass))
     (syntax/loc stx expr)]
    [((~literal AlloyModule) ((~literal EvalDecl) "eval" expr:ExprClass) ...+)
     (syntax/loc stx (raise "Can't eval multiple expressions."))]))

; ModuleDecl : /MODULE-TOK QualName (LEFT-SQUARE-TOK NameList RIGHT-SQUARE-TOK)?
(define-syntax (ModuleDecl stx)
  (syntax-parse stx 
    [((~literal ModuleDecl) module-name:QualNameClass
                            (~optional (~seq "[" other-names:NameListClass "]")))
     (syntax/loc stx (raise "ModuleDecl not yet implemented."))]))


; Import : OPEN-TOK QualName (LEFT-SQUARE-TOK QualNameList RIGHT-SQUARE-TOK)? (AS-TOK Name)?
(define-syntax (Import stx)
  (syntax-parse stx
      [((~literal Import) file-path:str
                          (~optional (~seq "as" as-name:NameClass)))
       (syntax/loc stx (begin
           (~? (require (prefix-in as-name.name file-path))
               (require file-path))))]
    [((~literal Import) import-name:QualNameClass
                        (~optional (~seq "[" other-names:QualNameListClass "]"))
                        (~optional (~seq "as" as-name:NameClass)))
     (syntax/loc stx (begin
         (raise (format "Importing packages not yet implemented: ~a." 'import-name))
         (~? (raise (format "Bracketed import not yet implemented. ~a" 'other-names)))
         (~? (raise (format "Importing as not yet implemented. ~a" 'as-name)))))]))
  
; SigDecl : VAR-TOK? ABSTRACT-TOK? Mult? /SIG-TOK NameList SigExt? /LEFT-CURLY-TOK ArrowDeclList? /RIGHT-CURLY-TOK Block?
(define-syntax (SigDecl stx)
  (syntax-parse stx
    [((~literal SigDecl) (~optional abstract:abstract-tok)
                         (~optional mult:MultClass)
                         (~optional isv:VarKeywordClass #:defaults ([isv #'#f]))
                         sig-names:NameListClass
                         ;when extending with in is implemented,
                         ;if "sig A in B extends C" is allowed,
                         ;check if this allows multiple SigExtClasses / how to do that if not
                         ;note the parser currently does not allow that
                         (~optional extends:SigExtClass)
                         (~optional block:BlockClass))
     (syntax/loc stx (begin
       (~? (raise (format "Sig block not yet implemented: ~a" 'block)))
       ;when extending with in is implemented,
       ;if "sig A in B extends C" is allowed,
       ;check if this allows that and update if needed
       ;note the parser currently does not allow that
       (sig sig-names.names (~? mult.symbol)
                            (~? abstract.symbol)
                            (~? (~@ #:is-var isv))
                            (~? (~@ extends.symbol extends.value))) ...))]

    [((~literal SigDecl) (~optional abstract:abstract-tok)
                         (~optional mult:MultClass)
                         (~optional isv:VarKeywordClass #:defaults ([isv #'#f]))
                         sig-names:NameListClass
                         ;when extending with in is implemented,
                         ;if "sig A in B extends C" is allowed,
                         ;check if this allows multiple SigExtClasses / how to do that if not
                         ;note the parser currently does not allow that
                         (~optional extends:SigExtClass)
                         ((~literal ArrowDeclList) arrow-decl:ArrowDeclClass ...)
                         (~optional block:BlockClass))
     (quasisyntax/loc stx (begin
       (~? (raise (format "Sig block not yet implemented: ~a" 'block)))
       ;when extending with in is implemented,
       ;if "sig A in B extends C" is allowed,
       ;check if this allows that and update if needed
       ;note the parser currently does not allow that
       (sig sig-names.names (~? mult.symbol) 
                            (~? abstract.symbol) 
                            (~? (~@ #:is-var isv))
                            (~? (~@ extends.symbol extends.value))) ...
       #,@(apply append
            (for/list ([sig-name (syntax->list #'(sig-names.names ...))]
                       #:when #t
                       [relation-names (syntax->list #'(arrow-decl.names ...))]
                       [relation-types (syntax->list #'(arrow-decl.types ...))]
                       [relation-is-var (syntax->list #'(arrow-decl.is-var ...))]
                       [relation-mult (syntax->list #'((~? arrow-decl.mult default) ...))])
              (for/list ([relation-name (syntax->list relation-names)])            
                (with-syntax ([relation-name relation-name]
                              [relation-types (datum->syntax relation-types 
                                                             (cons (syntax->datum sig-name)
                                                                   (syntax->list relation-types)))]                          
                              [relation-mult relation-mult]
                              [is-var relation-is-var])                                             
                      #'(relation relation-name relation-types #:is relation-mult #:is-var is-var)))))))]))
   
; RelDecl : ArrowDecl
(define-syntax (RelDecl stx)
  (syntax-parse stx
  [((~literal RelDecl) arrow-decl:ArrowDeclClass)
   (quasisyntax/loc stx (begin
   #,@(for/list ([name (syntax->list #'arrow-decl.names)])
        (with-syntax ([name name])
          (syntax/loc stx (relation name arrow-decl.types))))))]))

; FactDecl : FACT-TOK Name? Block
(define-syntax (FactDecl stx)
  (syntax-parse stx
  [((~literal FactDecl) _ ...)
   (syntax/loc stx (raise "Facts are not allowed in #lang forge."))]))

; PredDecl : /PRED-TOK PredType? (QualName DOT-TOK)? Name ParaDecls? Block
(define-syntax (PredDecl stx)
  (syntax-parse stx
  [((~literal PredDecl) (~optional t:PredTypeClass)
                        (~optional (~seq prefix:QualNameClass "."))
                        name:NameClass
                        block:BlockClass)
   (with-syntax ([block (my-expand #'block)])
     (quasisyntax/loc stx (begin
       (~? (raise (format "Prefixes not allowed: ~a" 'prefix)))
       ; preserve stx location in Racket *sub*expression
       #,(syntax/loc stx (pred (~? t.sym) name.name block)))))]

  [((~literal PredDecl) (~optional t:PredTypeClass)
                        (~optional (~seq prefix:QualNameClass "."))
                        name:NameClass
                        decls:ParaDeclsClass
                        block:BlockClass)
   (with-syntax ([decl (datum->syntax #'name (cons (syntax->datum #'name.name)
                                                   (syntax->list #'decls.translate)))]
                 [block (my-expand #'block)])
     (quasisyntax/loc stx (begin
       (~? (raise (format "Prefixes not allowed: ~a" 'prefix)))
       ; preserve stx location in Racket *sub*expression
       #,(syntax/loc stx (pred (~? t.sym) decl block)))))]))

; FunDecl : /FUN-TOK (QualName DOT-TOK)? Name ParaDecls? /COLON-TOK Expr Block
(define-syntax (FunDecl stx)
  (syntax-parse stx
  [((~literal FunDecl) (~optional (~seq prefix:QualNameClass "."))
                       name:NameClass
                       output:ExprClass
                       block:BlockClass)
   (with-syntax ([block (my-expand #'block)])
     (syntax/loc stx (begin
       (~? (raise (format "Prefixes not allowed: ~a" 'prefix)))
       (const name.name block))))]

  [((~literal FunDecl) (~optional (~seq prefix:QualNameClass "."))
                       name:NameClass
                       decls:ParaDeclsClass
                       output:ExprClass
                       block:BlockClass)
   (with-syntax ([decl (datum->syntax #'name (cons (syntax->datum #'name.name)
                                                   (syntax->list #'decls.translate)))]
                 [block (my-expand #'block)])
     (syntax/loc stx (begin
       (~? (raise (format "Prefixes not allowed: ~a" 'prefix)))
       (fun decl block))))]))

; AssertDecl : /ASSERT-TOK Name? Block
(define-syntax (AssertDecl stx)
  (syntax-parse stx
  [((~literal AssertDecl) _ ...)
   (syntax/loc stx (raise "Assertions not yet implemented."))]))

; CmdDecl :  (Name /COLON-TOK)? (RUN-TOK | CHECK-TOK) Parameters? (QualName | Block)? Scope? (/FOR-TOK Bounds)?
(define-syntax (CmdDecl stx)
  (syntax-parse stx
  [((~literal CmdDecl) (~optional name:NameClass)
                       (~and cmd-type (~or "run" "check"))
                       (~optional parameters:ParametersClass)
                       (~optional (~or pred:QualNameClass
                                       preds:BlockClass))
                       (~optional scope:ScopeClass)
                       (~optional bounds:BoundsClass))
   (with-syntax ([cmd-type (datum->syntax #'cmd-type
                                         (string->symbol (syntax->datum #'cmd-type)))]
                 [name #'(~? name.name temporary-name)]
                 [preds (my-expand #'(~? pred.name preds))])
     (syntax/loc stx (begin
       (cmd-type name (~? (~@ #:preds [preds]))
                      (~? (~@ #:scope scope.translate))
                      (~? (~@ #:bounds bounds.translate)))
       (display name))))]))

; TestDecl : (Name /COLON-TOK)? Parameters? (QualName | Block)? Scope? (/FOR-TOK Bounds)? /IS-TOK (SAT-TOK | UNSAT-TOK)
(define-syntax (TestDecl stx)
  (syntax-parse stx
  [((~literal TestDecl) (~optional name:NameClass)
                        (~optional parameters:ParametersClass)
                        (~optional (~or pred:QualNameClass
                                        preds:BlockClass))
                        (~optional scope:ScopeClass)
                        (~optional bounds:BoundsClass)
                        (~and expected (~or "sat" "unsat" "theorem")))
   (with-syntax ([name #'(~? name.name temporary-name)]
                 [preds (my-expand #'(~? pred.name preds))]
                 [expected (datum->syntax #'expected
                                          (string->symbol (syntax->datum #'expected)))])
     (syntax/loc stx (begin
       (test name (~? (~@ #:preds [preds]))
                  (~? (~@ #:scope scope.translate))
                  (~? (~@ #:bounds bounds.translate))
                  #:expect expected))))]))

; TestExpectDecl : TEST-TOK? EXPECT-TOK Name? TestBlock
(define-syntax (TestExpectDecl stx)
  (syntax-parse stx
  [((~literal TestExpectDecl) (~optional (~and "test" test-tok))
                              "expect" 
                              (~optional name:NameClass)
                              block:TestBlockClass)
   (if (attribute test-tok)
       (syntax/loc stx (begin block.test-decls ...))
       (syntax/loc stx (begin)))]))

(define-syntax-parser ExampleDecl
  [((~literal ExampleDecl) (~optional name:NameClass)
                           pred:ExprClass
                           bounds:BoundsClass)
   #`(example (~? name.name unnamed-example) 
              pred
              #,@#'bounds.translate)])

; OptionDecl : /OPTION-TOK QualName (QualName | FILE-PATH-TOK | Number)
(define-syntax (OptionDecl stx)
  (syntax-parse stx
  [dec:OptionDeclClass
     (syntax/loc stx (set-option! 'dec.n 'dec.v))
   ]))

; InstDecl : /INST-TOK Name Bounds Scope?
(define-syntax (InstDecl stx)
  (syntax-parse stx
  [((~literal InstDecl)
              name:NameClass
              bounds:BoundsClass
              (~optional scope:ScopeClass))
   (with-syntax ([(bounds ...) #'bounds.translate])
     (syntax/loc stx (begin
       (~? (raise (format "Scope not implemented for bounds ~a" 'scope)))
       (inst name.name bounds ...))))]))


; Block : /LEFT-CURLY-TOK Expr* /RIGHT-CURLY-TOK
(define-syntax (Block stx)
  (syntax-parse stx
    [((~literal Block) exprs:ExprClass ...)
     (with-syntax ([(exprs ...) (map my-expand (syntax->list #'(exprs ...)))])
       (syntax/loc stx (and exprs ...)))]))

(define-syntax (Expr stx)
  (syntax-parse stx
  [((~literal Expr) "let" decls:LetDeclListClass bob:BlockOrBarClass)
   (syntax/loc stx (let decls.translate bob.exprs))]

  [((~literal Expr) "bind" decls:LetDeclListClass bob:BlockOrBarClass)
   (syntax/loc stx (raise "bind not implemented."))]

  [((~literal Expr) q:QuantClass decls:DeclListClass bob:BlockOrBarClass)
   (syntax/loc #'q (q.symbol decls.translate bob.exprs))]


  [((~literal Expr) expr1:ExprClass (~or "or" "||") expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (or expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass (~or "iff" "<=>") expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (iff expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass (~or "implies" "=>") expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])     
     (syntax/loc stx (implies expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass (~or "implies" "=>") expr2:ExprClass
                                    "else" expr3:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)]
                 [expr3 (my-expand #'expr3)])
     (syntax/loc stx (ifte expr1 expr2 expr3)))]

  [((~literal Expr) expr1:ExprClass (~or "and" "&&") expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (and expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass (~or "releases") expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (releases expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass (~or "until") expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (until expr1 expr2)))]
    
  [((~literal Expr) (~or "!" "not") expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (! expr1)))]

  [((~literal Expr) (~or "always") expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (always expr1)))]
  [((~literal Expr) (~or "eventually") expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (eventually expr1)))]
  [((~literal Expr) (~or "after") expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
       (syntax/loc stx (after expr1)))]
    
  [((~literal Expr) expr1:ExprClass op:CompareOpClass expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)]
                 [op #'op.symbol])
     (syntax/loc stx (op expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass 
                    (~or "!" "not") op:CompareOpClass 
                    expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)]
                 [op #'op.symbol])
     ; Need to preserve srcloc in both the "not" and the "op" nodes
     (quasisyntax/loc stx (! #,(syntax/loc stx (op expr1 expr2)))))]

  [((~literal Expr) (~and (~or "no" "some" "lone" "one" "two" "set")
                          op)
                    expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [op (datum->syntax #'op (string->symbol (syntax->datum #'op)))])
     (syntax/loc stx (op expr1)))]

  [((~literal Expr) "#" expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (card expr1)))]

  ; Semantic priming as in Electrum
  [((~literal Expr) expr1:ExprClass "'")
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (prime expr1)))]

  [((~literal Expr) expr1:ExprClass "+" expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (+ expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass "-" expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (- expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass "++" expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (++ expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass "&" expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (& expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass op:ArrowOpClass expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (-> expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass ":>" expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (:> expr1 expr2)))]

  [((~literal Expr) expr1:ExprClass "<:" expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (<: expr1 expr2)))]

  [((~literal Expr) "[" exprs:ExprListClass "]")
   (syntax/loc stx (raise (format "Unimplemented ~a" exprs)))]

  [((~literal Expr) expr1:ExprClass "." expr2:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [expr2 (my-expand #'expr2)])
     (syntax/loc stx (join expr1 expr2)))]

  [((~literal Expr) name:NameClass "[" exprs:ExprListClass "]")
   (with-syntax ([name #'name.name]
                 [(exprs ...) (datum->syntax #f (map my-expand (syntax->list #'(exprs.exprs ...))))])
     (syntax/loc stx (name exprs ...)))]

  [((~literal Expr) expr1:ExprClass "[" exprs:ExprListClass "]")
   (with-syntax ([expr1 (my-expand #'expr1)]
                 [(exprs ...) (datum->syntax #f (map my-expand (syntax->list #'(exprs.exprs ...))))])
     (syntax/loc stx (expr1 exprs ...)))]

  [((~literal Expr) "~" expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (~ expr1)))]

  [((~literal Expr) "^" expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (^ expr1)))]

  [((~literal Expr) "*" expr1:ExprClass)
   (with-syntax ([expr1 (my-expand #'expr1)])
     (syntax/loc stx (* expr1)))]

  [((~literal Expr) const:ConstClass)   
   (syntax/loc stx const.translate)]

  [((~literal Expr) name:QualNameClass)
   (syntax/loc stx name.name)]

  [((~literal Expr) "this")
   (syntax/loc stx this)]

  [((~literal Expr) "{" decls:DeclListClass bob:BlockOrBarClass "}")
   (syntax/loc stx (set decls.translate bob.exprs))]

  [((~literal Expr) block:BlockClass)
   (my-expand (syntax/loc stx block))]

  [((~literal Expr) sexpr:SexprClass)
   (syntax/loc stx (read sexpr))]

  ))

; --------------------------
; these used to be define-simple-macro, but define-simple-macro doesn't
; preserve syntax location, so we copy the definition from the docs except use syntax/loc.

(define-syntax (dsm-keep stx-outer)
  (syntax-case stx-outer ()
    [(_ (macro-id . pattern) pattern-directive ... template)
     (with-syntax ([ellip '...])
       (syntax/loc stx-outer
         (define-syntax (macro-id stx)
           (syntax-parse stx
             #:track-literals
             [((~var macro-id id) . pattern) pattern-directive ... (syntax/loc stx template)]))))]))

(dsm-keep (Expr0.5 stx ...) (Expr stx ...))
(dsm-keep (Expr1 stx ...) (Expr stx ...))
(dsm-keep (Expr2 stx ...) (Expr stx ...))
(dsm-keep (Expr3 stx ...) (Expr stx ...))
(dsm-keep (Expr4 stx ...) (Expr stx ...))
(dsm-keep (Expr5 stx ...) (Expr stx ...))
(dsm-keep (Expr6 stx ...) (Expr stx ...))
(dsm-keep (Expr7 stx ...) (Expr stx ...))
(dsm-keep (Expr7.5 stx ...) (Expr stx ...))
(dsm-keep (Expr8 stx ...) (Expr stx ...))
(dsm-keep (Expr9 stx ...) (Expr stx ...))
(dsm-keep (Expr10 stx ...) (Expr stx ...))
(dsm-keep (Expr11 stx ...) (Expr stx ...))
(dsm-keep (Expr12 stx ...) (Expr stx ...))
(dsm-keep (Expr13 stx ...) (Expr stx ...))
(dsm-keep (Expr14 stx ...) (Expr stx ...))
(dsm-keep (Expr15 stx ...) (Expr stx ...))
(dsm-keep (Expr16 stx ...) (Expr stx ...))
(dsm-keep (Expr17 stx ...) (Expr stx ...))





; Transition System Stuff to be implemented
; StateDecl : STATE-TOK /LEFT-SQUARE-TOK QualName /RIGHT-SQUARE-TOK 
;     (QualName DOT-TOK)? Name ParaDecls? Block
; TransitionDecl : TRANSITION-TOK /LEFT-SQUARE-TOK QualName /RIGHT-SQUARE-TOK 
;     (QualName DOT-TOK)? Name ParaDecls? Block
; TraceDecl : TRACE-TOK Parameters
;     (QualName DOT-TOK)? Name ParaDecls? (/COLON-TOK Expr)? Block
; LeftAngle : LT-TOK | LEFT-TRIANGLE-TOK
; RightAngle: GT-TOK | RIGHT-TRIANGLE-TOK


; Other things (to be implemented?)
; NumberList : Number
;            | Number /COMMA-TOK @NumberList

; BreakDecl : /FACT-TOK /BREAK-TOK? Expr /COLON-TOK @NameList
;           | /BREAK-TOK Expr /COLON-TOK @NameList
; InstanceDecl : INSTANCE-TOK
; QueryDecl : @Name /COLON-TOK ArrowExpr /EQ-TOK Expr
