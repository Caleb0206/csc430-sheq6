#lang typed/racket
(require typed/rackunit)

;; SHEQ5
;; Fully finished SHEQ5 assignment with game, too.

;; Data definitions

;; Value - Numbers, Booleans, String, CloV, PrimV
(define-type Value (U Real Boolean String CloV PrimV))

;; CloV - Closures contain list of symbol params, body of ExprC, Env
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)

;; PrimV - Represents a primitive operator by its symbol
(struct PrimV ([op : Symbol]) #:transparent)

;; LamC - Lambdas contain a list of symbol args, and a body of ExprC
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

;; Binding : pair of a Symbol and a Value
(struct Binding ([name : Symbol] [val : Value]) #:transparent)

;; Env : a list of Bindings
(define-type Env (Listof Binding))

;; ExprC type : NumC, IfC, IdC, AppC, LamC, StringC
(define-type ExprC (U NumC IfC IdC AppC LamC StringC))

;; NumC : a Real
(struct NumC ([n : Real]) #:transparent)

;; StringC : a String
(struct StringC ([s : String]) #:transparent)

;; IdC : a symbol representing an ID
(struct IdC ([name : Symbol]) #:transparent)

;; IfC : an if statement of ExprC, and ExprC's to act on if true or false
(struct IfC ([v : ExprC] [iftrue : ExprC] [iffalse : ExprC]) #:transparent)

;; AppC : Represents a function application.function ExprC with a list of arg ExprC's
(struct AppC ([expr : ExprC] [args : (Listof ExprC)]) #:transparent)

;; Top level environment
(: top-env Env)
(define top-env (list
                 (Binding 'true #t)
                 (Binding 'false #f)
                 (Binding '+ (PrimV '+))
                 (Binding '- (PrimV '-))
                 (Binding '* (PrimV '*))
                 (Binding '/ (PrimV '/))
                 (Binding '<= (PrimV '<=))
                 (Binding 'equal? (PrimV 'equal?))
                 (Binding 'substring (PrimV 'substring))
                 (Binding 'strlen (PrimV 'strlen))
                 (Binding 'error (PrimV 'error))
                 (Binding 'println (PrimV 'println))
                 (Binding 'read-num (PrimV 'read-num))
                 (Binding 'read-str (PrimV 'read-str))
                 (Binding '++ (PrimV '++)))) 

;; reserved-keywords - a list of key-words
(define reserved-keywords '(if lambda let = in end : else))

;; ---- Interpreters ----

;; top-interp - Parse and evaluate the S-exp, return a serialized String result
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

;; interp - takes the complete AST (ExprC) with an Env, returning a Value
(define (interp [e : ExprC] [env : Env]) : Value
  ; template
  #;(match e
      [numc -> number]
      [stringc -> s]
      [ifc -> eval if expr]
      [LamC -> CloV params body env]
      [AppC -> interp CloV or PrimV]
      [Idc -> get binding])

  ; body
  (match e
    [(NumC n) n]
    [(StringC s) s]
    [(IfC v if-t if-f)
     (define test-val (interp v env))
     (cond
       [(boolean? test-val)
        (if test-val
            (interp if-t env)
            (interp if-f env))]
       [else (error 'interp "SHEQ: If expected boolean test, got ~a" test-val)])]
    [(LamC params body) (CloV params body env)]
    [(AppC (IdC 'seq) exprs)
     (interp-seq exprs env)]
    [(AppC lam args)
     (define f-val (interp lam env))
     (define arg-vals
       (for/list : (Listof Value) ([a args])
         (interp a env)))
     (cond
       [(CloV? f-val)
        (if (equal? (length arg-vals) (length (CloV-params f-val)))
            (interp (CloV-body f-val)
                    (append (map Binding (CloV-params f-val) arg-vals)
                            (CloV-env f-val)))
            (error 'interp "SHEQ: Incorrect number of arguments for CloV, got ~a expected ~a"
                   (length (CloV-params f-val))
                   (length arg-vals)))]
        
       [(PrimV? f-val)
        (interp-prim f-val arg-vals)]
       [else
        (error 'interp "SHEQ: Attempted to apply non function value ~a" f-val)])]         
    [(IdC id) (get-binding-val id env)]))

;; interp-seq - takes a list of ExprC's to interpret them sequentially, returns the last expression's Value
(define (interp-seq [exprs : (Listof ExprC)] [env : Env]) : Value
  (match exprs
    ['() (error 'interp "SHEQ: seq needs at least 1 expression.")]
    [(list f) (interp f env)]
    [(cons f rest) (begin (interp f env) (interp-seq rest env))]))

;; interp-prim - takes a PrimV and a list of Values, returns a Value
(define (interp-prim [p : PrimV] [args : (Listof Value)]) : Value
  (match (PrimV-op p)
    ['+
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (+ a b)]
          [else (error 'interp-prim "SHEQ: PrimV + expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['*
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (* a b)]
          [else (error 'interp-prim "SHEQ: PrimV * expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['-
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (- a b)]
          [else (error 'interp-prim "SHEQ: PrimV - expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['/
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b) (not (equal? b 0))) (/ a b)]
          [(and (real? a) (real? b) (equal? b 0))
           (error 'interp-prim "SHEQ: Divide by zero error")]
          [else (error 'interp-prim "SHEQ: PrimV / expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['<=
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (<= a b)]
          [else (error 'interp-prim "SHEQ: PrimV <= expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['equal?
     (match args
       [(list a b)
        (cond [(or (CloV? a) (CloV? b) (PrimV? a) (PrimV? b)) #f]
           
              [else (equal? a b)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['substring
     (match args
       [(list s start stop)
        (cond
          [(and (string? s)
                (natural? start)
                (natural? stop)
                (>= start 0)
                (< start (string-length s))
                (>= stop 0)
                (< stop (string-length s)))
           (substring s (inexact->exact start) (inexact->exact stop))]
          [else
           (error 'interp-prim "SHEQ: Substring needs string and 2 valid natural indices, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 3, got ~a" (length args))])]
    ['strlen
     (match args
       [(list s)
        (if (string? s)
            (string-length s)
            (error 'interp-prim "SHEQ: Syntax error, ~a is not a string" s))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['error
     (match args
       [(list v)
        (error 'interp-prim "SHEQ: user-error ~a" (serialize v))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['println
     (match args
       [(list s)
        (if (string? s)
            (begin
              (displayln s)
              #t)
            (error 'interp-prim "SHEQ: Attempted to print a non-string value, got ~a" s))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['read-num
     (match args
       ['()
        (begin
          (display "> ")
          ;; (flush-output)
          (define input (read-line))
          (cond
            [(eof-object? input)
             (error 'interp-prim "SHEQ: read-num read EOF")]
            [else
             (define num (string->number input))
             (if (real? num)
                 num
                 (error 'interp-prim "SHEQ: read-num expected a Number, got ~a" input))]))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 0, got ~a" (length args))])]
    ['read-str
     (match args
       ['()
        (begin
          (display "> ")
          ;; (flush-output)
          (define input (read-line))
          (if (eof-object? input)
              (error 'interp-prim "SHEQ: read-str read EOF")
              input))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 0, got ~a" (length args))])]
    ['++
     (match args
       ['() ""]
       [_ (apply string-append (map val->string args))])]
    [_
     (error 'interp-prim "SHEQ: Invalid PrimV op, got ~a" args)]))


;; ---- Parser ---- 
;; parse - takes a S-exp and returns concrete syntax in ExprC AST
(define (parse [e : Sexp]) : ExprC
  ; template
  #;(match e
      [number -> NumC]
      [string -> StringC]
      [not reserved symbol -> idc]
      [list 'let ... -> AppC(LamC)]
      [list 'if ... -> IfC]
      [list 'lambda ... -> LamC]
      [list f args -> AppC]
      [else -> throw unknown error])
  ; body
  (match e
    ;; Match Real
    [(? real? n) (NumC n)]
    ;; Match String
    [(? string? s) (StringC s)]
    ;; Match Id
    [(? symbol? name)
     (if (reserved-symbol? name)
         (error 'parse "SHEQ: Syntax error, unexpected reserved keyword, got ~e" name)
         (IdC name))]
    ;; Match Let
    [(list 'let 
           (list (list (? symbol? args) '= vals) ...) 
           'in
           in-body
           'end)
     (define args-list (cast args (Listof Symbol)))
     (cond
       [(not (distinct-args? args-list))
        (error 'parse "SHEQ: Let binding list is invalid, duplicate variables ~a" args-list)]
       [(ormap reserved-symbol? args-list)
        (error 'parse "SHEQ: let binding list is invalid, reserved symbol was used ~a" args-list)]
       [else (AppC 
              (LamC args-list (parse in-body)) 
              (for/list : (Listof ExprC) ([v vals]) 
                (parse (cast v Sexp))))])]
    ;; Match If
    [(list 'if v iftrue iffalse)
     (IfC (parse v) (parse iftrue) (parse  iffalse))]
    ;; Match Lambda
    [(list 'lambda (list (? symbol? args) ...) ': body)
     (define args-list (cast args (Listof Symbol)))
     (if (distinct-args? args-list)
         (LamC args-list (parse body))
         (error 'parse "SHEQ: Lambda args list is invalid, duplicate parameters found, ~a" args-list))]
    ;; Match Application
    [(list f args ...)
     (AppC (parse f) (for/list : (Listof ExprC) ([a args]) (parse a)))]
    [other (error 'parse "SHEQ: Syntax error, got ~e" other)]))


;; serialize - takes a Value and returns a serialized String
(define (serialize [v : Value]) : String
  (match v
    [(? real? r) (~v r)]
    [(? boolean? b) (if b
                        "true"
                        "false")]
    [(? string? s) (~v s)]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]))

;; val->string - converts a Value to a string
(define (val->string [v : Value]) : String
  (match v
    [(? real? r) (~a r)]
    [(? boolean? b) (if b
                        "true"
                        "false")]
    [(? string? s) (~a s)]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]))

;; ---- Helper functions ----

;; get-binding-val takes a symbol and enviornment, performs a lookup and returns an ExprC if found
(define (get-binding-val [s : Symbol] [env : Env]) : Value
  (match env
    ['() (error 'get-binding "SHEQ: An unbound identifier ~a" s)]
    [(cons (Binding name val) r)
     (if (equal? s name)
         val
         (get-binding-val s r))]))

;; distinct-args? - returns true if every symbol in args is distinct 
(define (distinct-args? [args : (Listof Symbol)]) : Boolean
  (not (check-duplicates args)))

;; reserved-symbol? - Determines if a given symbol is in the reserved keywords
(define (reserved-symbol? [s : Symbol]) : Boolean
  (if (memq s reserved-keywords)
      #t
      #f))

;; create-env - takes Listof Symbol, Listof Value, an Env, and returns a new Env
(define (create-env [args : (Listof Symbol)] [vals : (Listof Value)] [env : Env]) : Env
  (match* (args vals)
    [('() '()) env]
    [('() _) (error 'create-env "SHEQ: too many values were passed in application ~a ~a" args vals)]
    [(_ '()) (error 'create-env "SHEQ: too few values were passed in application ~a ~a" args vals)]
    [((cons fa ra) (cons fv rv))
     (create-env ra rv (cons (Binding fa fv) env))]))

;; ---- Tests ----

;; Large test
; The program calculates two areas using two different functions, and then compares them.
;; The result is the result of the comparison
(define prog '{
               let
                  {[square = {lambda (x) : {* x x}}]
                   [area = {lambda (w h) : {* w h}}]
                   [gt = {lambda (v1 v2 t f) : {if {<= v1 v2} 1 0}}]}
                in
                {gt {square 4} {area 4 3} 0 1}
                end})
(check-equal? (top-interp prog) "0")

;; ---- top-interp Tests ----
(check-equal? (top-interp '{+ 3 2}) "5")
(check-equal? (top-interp '{if {<= 5 10} "less than" "not less than"}) "\"less than\"")

(check-equal? (top-interp 
               '{let {[x = 5]
                      [y = {+ 8 9}]}
                  in
                  {+ x {* y {let {[x = 3]}
                              in
                              {+ x x}
                              end}}}
                  end
                  }) "107")

(check-equal? (top-interp '{seq
                            {let ([n = 5])
                              in
                              {+ 1 n}
                              end}
                            {let ([x = 2])
                              in
                              {* 2 x}
                              end}}) "4")

;; incorect num of arguments (from handin)
(check-exn #rx"SHEQ: Incorrect number of arguments for CloV"
           (lambda () (top-interp '{{lambda () : 19} 17})))

;; divide by zero error test case (from handin)
(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (top-interp
                       '{{lambda (ignoreit) : {ignoreit {/ 52 {+ 0 0}}}} {lambda (x) : {+ 7 x}}})))

;; ---- interp tests ----
(check-equal? (interp (IdC 'true) top-env) #t)

(check-equal? (interp (NumC 89) top-env) 89)

(check-equal? (interp (AppC (IdC '+) (list (NumC 8)
                                           (AppC (IdC '*) (list (NumC 2) (NumC 3))))) top-env)  14)

(check-equal? (interp (AppC (IdC 'main) '()) (list (Binding 'main (CloV '() (NumC 5) '())))) 5)

(check-equal? (interp (AppC (IdC 'someFunction) (list (NumC 3)))
                      (list (Binding 'someFunction
                                     (CloV '(x)
                                           (AppC (IdC '*) (list (NumC 10) (IdC 'x)))
                                           top-env)))) 30)

(check-equal? (interp (AppC (IdC '<=) (list (NumC 9) (NumC 10))) top-env) #t)

(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 9) (NumC 10))) top-env) #f)

(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 9) (NumC 10))) top-env) #f)

(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 5) (NumC 2))) (NumC 1) (NumC -1)) top-env) -1)

(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '+) (list (IdC 'x) (NumC 1))))
                            (list (NumC 5))) top-env) 6)

(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (NumC 81) (NumC 81)))
                           (IdC 'true) (IdC 'false)) top-env) #t)

;; interp with seq
(check-exn #rx"SHEQ: seq needs at least 1 expression."
           (lambda () (interp (AppC (IdC 'seq) '()) top-env)))


;; ---- interp error check ---- 
(check-exn #rx"SHEQ: An unbound identifier" (lambda () (interp (IdC 'x) '())))

(check-exn #rx"SHEQ: PrimV \\+ expected 2 numbers"
           (lambda () (interp (AppC (IdC '+) (list (IdC '-) (NumC 4))) top-env)))

(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (interp (AppC (IdC '/) (list (NumC 5) (NumC 0))) top-env)))

(check-exn #rx"SHEQ: If expected boolean test"
           (lambda () (interp (parse '{if 32 23 32}) top-env)))

(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda ()
             (interp (AppC (LamC '(x)
                                 (AppC (IdC '+) (list (IdC 'x) (NumC 1) (NumC 2))))
                           (list (NumC 5))) top-env)))

(check-exn #rx"SHEQ: Attempted to apply non function value"
           (lambda ()
             (interp (AppC (NumC 9) (list (NumC 12))) top-env)))



;; ---- serialize tests ----
(check-equal? (serialize '32) "32")
(check-equal? (serialize #f) "false")
(check-equal? (serialize #t) "true")
(check-equal? (serialize (CloV '(x) (NumC 34) top-env)) "#<procedure>")
(check-equal? (serialize (PrimV '<=)) "#<primop>")

(check-exn #rx"SHEQ: user-error true" (lambda () (interp-prim (PrimV 'error) (list #t))))


;; ---- parse Tests ----

(check-equal? (parse '{(lambda (x) : {+ x 1}) 5})
              (AppC (LamC '(x) (AppC (IdC '+) (list (IdC 'x) (NumC 1)))) (list (NumC 5))))

(check-equal? (parse '{+ 5 12}) (AppC (IdC '+) (list (NumC 5) (NumC 12))))

(check-equal? (parse '{applyThis 5 12}) (AppC (IdC 'applyThis) (list (NumC 5) (NumC 12))))

(check-equal? (parse 'double) (IdC 'double))

(check-equal? (parse '{double x 2}) (AppC (IdC 'double) (list (IdC 'x) (NumC 2))))

(check-equal? (parse '{ifleq0? 5 x y}) (AppC (IdC 'ifleq0?) (list (NumC 5) (IdC 'x) (IdC 'y))))

(check-equal? (parse '{let {[x = 5] [y = {* 7 8}]} in {+ x y} end}) 
              (AppC 
               (LamC (list 'x 'y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))) 
               (list (NumC 5) 
                     (AppC (IdC '*) (list (NumC 7) (NumC 8))))))

(check-equal? (parse '{if {<= 3 90} 3 90})
              (IfC (AppC (IdC '<=) (list (NumC 3) (NumC 90))) (NumC 3) (NumC 90)))


;; parse errors
(check-exn #rx"SHEQ: Lambda args list is invalid, duplicate parameters found"
           (lambda () (parse '(lambda (x y x) : 33))))
(check-exn #rx"SHEQ: Let binding list is invalid, duplicate variables"
           (lambda () (parse '(let {[bo = {lambda () : 33}] [bo = "Twenty"]} in {bo} end))))
(check-exn #rx"SHEQ: let binding list is invalid, reserved symbol was used"
           (lambda () (parse '(let {[if = {lambda () : 0}]} in {if 3} end))))

(check-exn #rx"SHEQ: Syntax error, got"
           (lambda () (parse '{})))

(check-exn #rx"SHEQ: Syntax error, unexpected reserved keyword, got"
           (lambda () (parse '{let 2})))

(check-exn #rx"SHEQ: Syntax error, unexpected reserved keyword, got"
           (lambda () (parse '{end 3 4 3 2})))

(check-exn #rx"SHEQ: Syntax error, unexpected reserved keyword, got" (lambda () (parse '=)))


;; ---- intperp-prim Tests ----
;; PrimV '+ tests
(check-equal? (interp-prim (PrimV '+) (list 8 9)) 17)
(check-exn #rx"SHEQ: PrimV \\+ expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '+) (list 8 #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '+) (list 8 23 3 2))))

;; PrimV '* tests
(check-equal? (interp-prim (PrimV '*) (list 8 4)) 32)
(check-exn #rx"SHEQ: PrimV \\* expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '*) (list #f #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '*) (list 2))))

;; PrimV '/ tests
(check-equal? (interp-prim (PrimV '/) (list 33 11)) 3)
(check-exn #rx"SHEQ: PrimV \\/ expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '/) (list #f #t))))
(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (interp-prim (PrimV '/) (list 3 0)))) 
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '/) (list 21 2 3))))

;; PrimV '- tests
(check-equal? (interp-prim (PrimV '-) (list 33 11)) 22)
(check-exn #rx"SHEQ: PrimV \\- expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '-) (list #f #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '-) (list 9 3 2 1 3))))

;; PrimV '<= tests
(check-equal? (interp-prim (PrimV '<=) (list 3 11)) #t)
(check-equal? (interp-prim (PrimV '<=) (list 3 -11)) #f)
(check-exn #rx"SHEQ: PrimV \\<= expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '<=) (list #f #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '<=) (list 3))))

;; PrimV 'equal? tests
(check-equal? (interp-prim (PrimV 'equal?) (list 9 9)) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list #f #f)) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list "hi" "hi")) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list 3 #f)) #f)
(check-equal? (interp-prim (PrimV 'equal?)
                           (list (CloV '(x) (NumC 1) '()) (CloV '(x) (NumC 1) '()))) #f)
(check-equal? (interp-prim (PrimV 'equal?)
                           (list (PrimV '-) (PrimV '-))) #f)
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'equal?) (list 3))))

;; PrimV 'substring tests
(check-equal? (interp-prim (PrimV 'substring) (list "hello world!" 0 5)) "hello")
(check-exn #rx"SHEQ: Substring needs string and 2 valid natural indices"
           (lambda () (interp-prim (PrimV 'substring) (list "hello" 99 1))))
(check-exn #rx"SHEQ: Incorrect number of arguments, expected 3"
           (lambda () (interp-prim (PrimV 'substring) (list "bib" 0 1 23 3))))

;; PrimV 'strlen tests
(check-equal? (interp-prim (PrimV 'strlen) (list "hello world!")) 12)
(check-exn #rx"SHEQ: Syntax error" (lambda () (interp-prim (PrimV 'strlen) (list 3))))
(check-exn #rx"SHEQ: Incorrect number of arguments, expected 1"
           (lambda () (interp-prim (PrimV 'strlen) (list "bib" "five" 3))))

;; PrimV 'error test
(check-exn #rx"SHEQ: Incorrect number of arguments, expected 1"
           (lambda () (interp-prim (PrimV 'error) (list "This" "too many"))))

;; PrimV invalid PrimV test
(check-exn #rx"SHEQ: Invalid PrimV op"
           (lambda () (interp-prim (PrimV 'dothis) (list 9))))

;; PrimV 'println tests
(check-equal? (interp-prim (PrimV 'println) (list "test: Hello World from interp")) #t)

(check-exn #rx"SHEQ: Attempted to print a non-string value"
           (lambda ()
             (interp-prim (PrimV 'println) (list 5))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda ()
             (interp-prim (PrimV 'println) (list "a" "c"))))


;; PrimV 'read-num test
(check-equal? (with-input-from-string "52\n"
                (lambda () (interp-prim (PrimV 'read-num) '()))) 52)

(check-exn #rx"SHEQ: read-num expected a Number"
           (lambda () 
             (with-input-from-string "five"
               (lambda () (interp-prim (PrimV 'read-num) '())))))

(check-exn #rx"SHEQ: read-num read EOF"
           (lambda () 
             (with-input-from-string ""
               (lambda () (interp-prim (PrimV 'read-num) '())))))

(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'read-num) (list 4 2 1))))

;; PrimV 'read-str tests
(check-equal? (with-input-from-string "hello\n"
                (lambda () (interp-prim (PrimV 'read-str) '()))) "hello")

(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'read-str) (list "s" "b" "c"))))

(check-exn #rx"SHEQ: read-str read EOF"
           (lambda () 
             (with-input-from-string ""
               (lambda () (interp-prim (PrimV 'read-str) '())))))

;; PrimV '++ tests
(check-equal? (interp-prim (PrimV '++) (list 4 "hello" #f)) "4hellofalse")
(check-equal? (interp-prim (PrimV '++) '()) "")

;; ---- Helper Tests ----

;; value->string tests
(check-equal? (val->string 3) "3")
(check-equal? (val->string #t) "true")
(check-equal? (val->string #f) "false")
(check-equal? (val->string "s") "s")
(check-equal? (val->string (CloV '(x) (NumC 4) top-env)) "#<procedure>")
(check-equal? (val->string (PrimV '+)) "#<primop>")

;; distinct-args? tests
(check-equal? (distinct-args? '(x y z)) #t)
(check-equal? (distinct-args? '(x y x)) #f)

;; reserved-symbol tests
(check-equal? (reserved-symbol? 'lambda) #t)
(check-equal? (reserved-symbol? '+++) #f)

;; create-env tests
(check-equal? (create-env (list 'a) (list 5) (list (Binding 'random 314)))
              (list (Binding 'a 5) (Binding 'random 314)))
(check-exn #rx"SHEQ: too many values were passed in application"
           (lambda () (create-env (list 'a) (list 5 3 4) (list (Binding 'random 314)))))
(check-exn #rx"SHEQ: too few values were passed in application"
           (lambda () (create-env (list 'a 'x) (list 4) (list (Binding 'random 314)))))

;; get-binding tests
(check-equal? (get-binding-val 'sym (list (Binding 'sym 5))) 5)
(check-exn #rx"SHEQ: An unbound identifier" (lambda () (get-binding-val 'sym '())))

