#lang typed/racket
(require typed/rackunit)

;; SHEQ6
;; Status statement here.

;; Data definitions

;; Value - Numbers, Booleans, String, CloV, PrimV, ArrayV, NullV
(define-type Value (U Real Boolean String CloV PrimV ArrayV NullV))

;; NullV - contains nothing
(struct NullV () #:transparent)

;; RealV
(struct RealV ([n : Real]))
;; StringV
(struct StringV ([str : String]))
;; BoolV
(struct BoolV ([bool : Boolean]))

;; ArrayV - Array contains an address and a size, both of Natural types
(struct ArrayV ([address : Natural] [size : Natural]) #:transparent)

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
                 (Binding '++ (PrimV '++))
                 (Binding 'make-array (PrimV 'make-array))
                 (Binding 'array (PrimV 'array))
                 (Binding 'aref (PrimV 'aref))
                 (Binding 'aset! (PrimV 'aset!)))) 

;; reserved-keywords - a list of key-words
(define reserved-keywords '(if lambda let = in end : else))

;; ---- Interpreters ----

;; top-interp - Parse and evaluate the S-exp, return a serialized String result
(define (top-interp [s : Sexp] [memsize : Natural]) : String
  (serialize (interp (parse s) top-env (make-initial-store memsize))))

;; interp - takes the complete AST (ExprC) with an Env, returning a Value
(define (interp [e : ExprC] [env : Env] [store : (Vectorof Value)]) : Value
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
     (define test-val (interp v env store))
     (cond
       [(boolean? test-val)
        (if test-val
            (interp if-t env store)
            (interp if-f env store))]
       [else (error 'interp "SHEQ: If expected boolean test, got ~a" test-val)])]
    [(LamC params body) (CloV params body env)]
    [(AppC (IdC 'seq) exprs)
     (interp-seq exprs env store)]
    [(AppC lam args)
     (define f-val (interp lam env store))
     (define arg-vals
       (for/list : (Listof Value) ([a args])
         (interp a env store)))
     (cond
       [(CloV? f-val)
        (if (equal? (length arg-vals) (length (CloV-params f-val)))
            (interp (CloV-body f-val)
                    (append (map Binding (CloV-params f-val) arg-vals)
                            (CloV-env f-val))
                    store)
            (error 'interp "SHEQ: Incorrect number of arguments for CloV, got ~a expected ~a"
                   (length (CloV-params f-val))
                   (length arg-vals)))]
        
       [(PrimV? f-val)
        (interp-prim f-val arg-vals store)]
       [else
        (error 'interp "SHEQ: Attempted to apply non function value ~a" f-val)])]         
    [(IdC id) (get-binding-val id env)]))

;; interp-seq - takes a list of ExprC's to interpret them sequentially, returns the last expression's Value
(define (interp-seq [exprs : (Listof ExprC)] [env : Env] [store : (Vectorof Value)]) : Value
  (match exprs
    ['() (error 'interp "SHEQ: seq needs at least 1 expression.")]
    [(list f) (interp f env store)]
    [(cons f rest) (begin (interp f env store) (interp-seq rest env store))]))

;; interp-prim - takes a PrimV and a list of Values, returns a Value
(define (interp-prim [p : PrimV] [args : (Listof Value)] [store : (Vectorof Value)]) : Value
  (match (PrimV-op p)
    ['+
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (+ a b)]
          [else (error 'interp-prim "SHEQ: PrimV + expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: + received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['*
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (* a b)]
          [else (error 'interp-prim "SHEQ: PrimV * expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: * received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['-
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (- a b)]
          [else (error 'interp-prim "SHEQ: PrimV - expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: - received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['/
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b) (not (equal? b 0))) (/ a b)]
          [(and (real? a) (real? b) (equal? b 0))
           (error 'interp-prim "SHEQ: Divide by zero error")]
          [else (error 'interp-prim "SHEQ: PrimV / expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: / received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['<=
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (<= a b)]
          [else (error 'interp-prim "SHEQ: PrimV <= expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: <= received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['equal?
     (match args
       [(list a b)
        (cond [(or (CloV? a) (CloV? b) (PrimV? a) (PrimV? b)) #f]
              [else (equal? a b)])]
       [_ (error 'interp-prim "SHEQ: equal? received incorrect number of arguments, expected 2, got ~a" (length args))])]
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
           (error 'interp-prim "SHEQ: substring needs string and 2 valid natural indices, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: substring received incorrect number of arguments, expected 3, got ~a" (length args))])]
    ['strlen
     (match args
       [(list s)
        (if (string? s)
            (string-length s)
            (error 'interp-prim "SHEQ: Syntax error, ~a is not a string" s))]
       [_ (error 'interp-prim "SHEQ: strlen received incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['error
     (match args
       [(list v)
        (error 'interp-prim "SHEQ: user-error ~a" (serialize v))]
       [_ (error 'interp-prim "SHEQ: error received incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['println
     (match args
       [(list s)
        (if (string? s)
            (begin
              (displayln s)
              #t)
            (error 'interp-prim "SHEQ: Attempted to print a non-string value, got ~a" s))]
       [_ (error 'interp-prim "SHEQ: println received incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['read-num
     (match args
       ['()
        (begin
          (display "> ")
          (define input (read-line))
          (cond
            [(eof-object? input)
             (error 'interp-prim "SHEQ: read-num read EOF")]
            [else
             (define num (string->number input))
             (if (real? num)
                 num
                 (error 'interp-prim "SHEQ: read-num expected a Number, got ~a" input))]))]
       [_ (error 'interp-prim "SHEQ: read-num received incorrect number of arguments, expected 0, got ~a" (length args))])]
    ['read-str
     (match args
       ['()
        (begin
          (display "> ")
          (define input (read-line))
          (if (eof-object? input)
              (error 'interp-prim "SHEQ: read-str read EOF")
              input))]
       [_ (error 'interp-prim "SHEQ: read-str received incorrect number of arguments, expected 0, got ~a" (length args))])]
    ['++
     (match args
       ['() ""]
       [_ (apply string-append (map val->string args))])]
    ['make-array
     (match args
       [(list size val)
        (cond
          [(and (natural? size) (>= size 1))
            (define len (inexact->exact size))
            (define arr (make-vector len val))
            (define addr (allocate store len))
            (for ([i (in-range len)])
              (vector-set! store (+ addr i) val))
            
            (ArrayV addr len)]
          [(and (natural? size) (< size 1))
           (error 'interp-prim "SHEQ: make-array expected size 1 or greater, got ~a" size)]
          [(not (natural? size))
           (error 'interp-prim "SHEQ: make-array expected a natural number for size, got ~a" size)]
          )]
       [_ (error 'interp-prim "SHEQ: make-array received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['array
     (match args
       ['() (error 'interp-prim "SHEQ: array expected at least one element, got ~a" args)]
       [_
        (define len (length args))
        (define addr (allocate store len))
        (for ([i (in-range len)] [v args])
          (vector-set! store (+ addr i) v))
        (ArrayV addr len)])]
    ['aref
     (match args
       [(list arr index)
        (cond
          [(not (ArrayV? arr))
           (error 'interp-prim "SHEQ: aref expected an array, got ~a" arr)]
          [(not (integer? index))
           (error 'interp-prim "SHEQ: aref expected an integer for index, got ~a" index)]
          [(or (< index 0) (>= index (ArrayV-size arr)))
           (error 'interp-prim "SHEQ: aref index out of bounds. ~a index for array of size ~a"
                  index
                  (ArrayV-size arr))]
          [else
           (vector-ref store (cast (+ (ArrayV-address arr) index) Nonnegative-Integer))])]
       [_ (error 'interp-prim "SHEQ: aref received incorrect number of arguments, expected 2, got ~a" (length args))])]
    ['aset!
     (match args
       [(list arr index val)
        (cond
          [(not (ArrayV? arr))
           (error 'interp-prim "SHEQ: aset! expected an array, got ~a" arr)]
          [(not (integer? index))
           (error 'interp-prim "SHEQ: aset! expected an integer for index, got ~a" index)]
          
          [(or (< index 0) (>= index (ArrayV-size arr)))
           (error 'interp-prim "SHEQ: aset! index out of bounds. ~a index for array of size ~a"
                  index
                  (ArrayV-size arr))]
          [else
           (vector-set! store (cast (+ (ArrayV-address arr) index) Nonnegative-Integer) val)
           (NullV)])]
       [_ (error 'interp-prim "SHEQ: aset! received incorrect number of arguments, expected 3, got ~a" (length args))])]
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
    [(PrimV _) "#<primop>"]
    [(ArrayV addr size) (string-append "#<array>")]))

;; val->string - converts a Value to a string
(define (val->string [v : Value]) : String
  (match v
    [(? real? r) (~a r)]
    [(? boolean? b) (if b
                        "true"
                        "false")]
    [(? string? s) (~a s)]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]
    [(ArrayV _ _) "#<array>"]))

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
    [('() _) (error 'create-env "SHEQ: create-env received too many values were passed in application ~a ~a" args vals)]
    [(_ '()) (error 'create-env "SHEQ: create-env received too few values were passed in application ~a ~a" args vals)]
    [((cons fa ra) (cons fv rv))
     (create-env ra rv (cons (Binding fa fv) env))]))

;; make-initial-store - takes a Natural number size, returns a Vector of Values where index 0 is equal to 1
(define (make-initial-store [size : Natural]) : (Vectorof Value)
  (define stre : (Mutable-Vectorof Value) (make-vector size 0))
  (vector-set! stre 0 1)
  stre)

;; allocate - takes a Vector of Values and a Natural number size, returns a Natural pointer to which the Value was stored
(define (allocate [stre : (Vectorof Value)] [n : Natural]): Natural
  (define next-free (assert (vector-ref stre 0) natural?))
  (define new-free (+ next-free n))
  (if (>= new-free (vector-length stre))
      (error 'allocate "SHEQ: Out of memory. Tried to allocate ~a cells, but only ~a are left."
             n
             (- (vector-length stre) next-free))
      (vector-set! stre 0 new-free))
  next-free)


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
(check-equal? (top-interp prog 100) "0")

;; ---- top-interp Tests ----
(check-equal? (top-interp '{+ 3 2} 100) "5")
(check-equal? (top-interp '{if {<= 5 100} "less than" "not less than"} 10) "\"less than\"")

(check-equal? (top-interp 
               '{let {[x = 5]
                      [y = {+ 8 9}]}
                  in
                  {+ x {* y {let {[x = 3]}
                              in
                              {+ x x}
                              end}}}
                  end}
               100) "107")

;; - top-interp seq test
(check-equal? (top-interp '{seq
                            {let ([n = 5])
                              in
                              {+ 1 n}
                              end}
                            {let ([x = 2])
                              in
                              {* 2 x}
                              end}}
                          100) "4")

;; - top-interp with arrays
(check-equal? (top-interp '{let ([arr1 = {make-array 5 0}]
                                 [arr2 = {array 0 0 0 0 0}])
                             in
                             {equal? arr1 arr2}
                             end} 100) "false")

(check-equal? (top-interp '{let ([arr3 = {make-array 5 0}]
                                 [f = {lambda (x) : {* x 2}}])
                             in
                             {seq
                              {aset! arr3 0 {f 10}}
                              {aref arr3 0}}
                             end} 100) "20")

;; - incorect num of arguments (from handin)
(check-exn #rx"SHEQ: Incorrect number of arguments for CloV"
           (lambda () (top-interp '{{lambda () : 19} 17} 100)))

;; - divide by zero error test case (from handin)
(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (top-interp
                       '{{lambda (ignoreit) : {ignoreit {/ 52 {+ 0 0}}}} {lambda (x) : {+ 7 x}}}
                       100)))

;; ---- interp tests ----
(define test-store (make-initial-store 100)) ; test-store is a store for the tests below

(check-equal? (interp (IdC 'true) top-env test-store) #t)

(check-equal? (interp (NumC 89) top-env test-store) 89)

(check-equal? (interp (AppC (IdC '+) (list (NumC 8)
                                           (AppC (IdC '*) (list (NumC 2) (NumC 3)))))
                        top-env
                        test-store)  14)

(check-equal? (interp (AppC (IdC 'main) '()) (list (Binding 'main (CloV '() (NumC 5) '()))) test-store) 5)

(check-equal? (interp (AppC (IdC 'someFunction) (list (NumC 3)))
                      (list (Binding 'someFunction
                                     (CloV '(x)
                                           (AppC (IdC '*) (list (NumC 10) (IdC 'x)))
                                           top-env
                                           ))) test-store) 30)

(check-equal? (interp (AppC (IdC '<=) (list (NumC 9) (NumC 10))) top-env test-store) #t)

(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 9) (NumC 10))) top-env test-store) #f)

(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 9) (NumC 10))) top-env test-store) #f)

(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 5) (NumC 2))) (NumC 1) (NumC -1)) top-env test-store) -1)

(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '+) (list (IdC 'x) (NumC 1))))
                            (list (NumC 5))) top-env test-store) 6)

(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (NumC 81) (NumC 81)))
                           (IdC 'true) (IdC 'false)) top-env test-store) #t)

;; interp with seq
(check-exn #rx"SHEQ: seq needs at least 1 expression."
           (lambda () (interp (AppC (IdC 'seq) '()) top-env test-store)))


;; ---- interp error check ---- 
(check-exn #rx"SHEQ: An unbound identifier" (lambda () (interp (IdC 'x) '() test-store)))

(check-exn #rx"SHEQ: PrimV \\+ expected 2 numbers"
           (lambda () (interp (AppC (IdC '+) (list (IdC '-) (NumC 4))) top-env test-store)))

(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (interp (AppC (IdC '/) (list (NumC 5) (NumC 0))) top-env test-store)))

(check-exn #rx"SHEQ: If expected boolean test"
           (lambda () (interp (parse '{if 32 23 32}) top-env test-store)))

(check-exn #rx"SHEQ: \\+ received incorrect number of arguments, expected 2, got"
           (lambda ()
             (interp (AppC (LamC '(x)
                                 (AppC (IdC '+) (list (IdC 'x) (NumC 1) (NumC 2))))
                           (list (NumC 5)))
                     top-env test-store)))

(check-exn #rx"SHEQ: Attempted to apply non function value"
           (lambda ()
             (interp (AppC (NumC 9) (list (NumC 12))) top-env test-store)))



;; ---- serialize tests ----
(check-equal? (serialize '32) "32")
(check-equal? (serialize #f) "false")
(check-equal? (serialize #t) "true")
(check-equal? (serialize (CloV '(x) (NumC 34) top-env)) "#<procedure>")
(check-equal? (serialize (PrimV '<=)) "#<primop>")
(check-equal? (serialize (ArrayV 2 12)) "#<array>")

(check-exn #rx"SHEQ: user-error true" (lambda () (interp-prim (PrimV 'error) (list #t) test-store)))


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
(check-equal? (interp-prim (PrimV '+) (list 8 9) test-store) 17)
(check-exn #rx"SHEQ: PrimV \\+ expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '+) (list 8 #t) test-store)))
(check-exn #rx"SHEQ: \\+ received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV '+) (list 8 23 3 2) test-store)))

;; PrimV '* tests
(check-equal? (interp-prim (PrimV '*) (list 8 4) test-store) 32)
(check-exn #rx"SHEQ: PrimV \\* expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '*) (list #f #t) test-store)))
(check-exn #rx"SHEQ: \\* received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV '*) (list 2) test-store)))

;; PrimV '/ tests
(check-equal? (interp-prim (PrimV '/) (list 33 11) test-store) 3)
(check-exn #rx"SHEQ: PrimV \\/ expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '/) (list #f #t) test-store)))
(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (interp-prim (PrimV '/) (list 3 0) test-store))) 
(check-exn #rx"SHEQ: \\/ received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV '/) (list 21 2 3) test-store)))

;; PrimV '- tests
(check-equal? (interp-prim (PrimV '-) (list 33 11) test-store) 22)
(check-exn #rx"SHEQ: PrimV \\- expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '-) (list #f #t) test-store)))
(check-exn #rx"SHEQ: \\- received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV '-) (list 9 3 2 1 3) test-store)))

;; PrimV '<= tests
(check-equal? (interp-prim (PrimV '<=) (list 3 11) test-store) #t)
(check-equal? (interp-prim (PrimV '<=) (list 3 -11) test-store) #f)
(check-exn #rx"SHEQ: PrimV \\<= expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '<=) (list #f #t) test-store)))
(check-exn #rx"SHEQ: \\<= received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV '<=) (list 3) test-store)))

;; PrimV 'equal? tests
(check-equal? (interp-prim (PrimV 'equal?) (list 9 9) test-store) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list #f #f) test-store) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list "hi" "hi") test-store) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list 3 #f) test-store) #f)
(check-equal? (interp-prim (PrimV 'equal?)
                           (list (CloV '(x) (NumC 1) '()) (CloV '(x) (NumC 1) '()))
                           test-store) #f)
(check-equal? (interp-prim (PrimV 'equal?)
                           (list (PrimV '-) (PrimV '-))
                           test-store) #f)

;; - equal? array test
(define temp-store (make-initial-store 20))
(define left (interp-prim (PrimV 'make-array) (list 3 0) temp-store))
(define right (interp-prim (PrimV 'make-array) (list 5 11) temp-store))
(check-equal? (interp-prim (PrimV 'equal?) (list left right) temp-store) #f)
(check-equal? (interp-prim (PrimV 'equal?) (list left left) temp-store) #t)

;; - equal? error
(check-exn #rx"SHEQ: equal\\? received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV 'equal?) (list 3) test-store)))

;; PrimV 'substring tests
(check-equal? (interp-prim (PrimV 'substring) (list "hello world!" 0 5) test-store) "hello")
(check-exn #rx"SHEQ: substring needs string and 2 valid natural indices"
           (lambda () (interp-prim (PrimV 'substring) (list "hello" 99 1) test-store)))
(check-exn #rx"SHEQ: substring received incorrect number of arguments, expected 3"
           (lambda () (interp-prim (PrimV 'substring) (list "bib" 0 1 23 3) test-store)))

;; PrimV 'strlen tests
(check-equal? (interp-prim (PrimV 'strlen) (list "hello world!") test-store) 12)
(check-exn #rx"SHEQ: Syntax error" (lambda () (interp-prim (PrimV 'strlen) (list 3) test-store)))
(check-exn #rx"SHEQ: strlen received incorrect number of arguments, expected 1"
           (lambda () (interp-prim (PrimV 'strlen) (list "bib" "five" 3) test-store)))

;; PrimV 'error test
(check-exn #rx"SHEQ: error received incorrect number of arguments, expected 1"
           (lambda () (interp-prim (PrimV 'error) (list "This" "too many") test-store)))

;; PrimV invalid PrimV test
(check-exn #rx"SHEQ: Invalid PrimV op"
           (lambda () (interp-prim (PrimV 'dothis) (list 9) test-store)))

;; PrimV 'println tests
(check-equal? (interp-prim (PrimV 'println) (list "test: Hello World from interp") test-store) #t)

(check-exn #rx"SHEQ: Attempted to print a non-string value"
           (lambda ()
             (interp-prim (PrimV 'println) (list 5) test-store)))
(check-exn #rx"SHEQ: println received incorrect number of arguments"
           (lambda ()
             (interp-prim (PrimV 'println) (list "a" "c") test-store)))


;; PrimV 'read-num test
(check-equal? (with-input-from-string "52\n"
                (lambda () (interp-prim (PrimV 'read-num) '() test-store))) 52)

(check-exn #rx"SHEQ: read-num expected a Number"
           (lambda () 
             (with-input-from-string "five"
               (lambda () (interp-prim (PrimV 'read-num) '() test-store)))))

(check-exn #rx"SHEQ: read-num read EOF"
           (lambda () 
             (with-input-from-string ""
               (lambda () (interp-prim (PrimV 'read-num) '() test-store)))))

(check-exn #rx"SHEQ: read-num received incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'read-num) (list 4 2 1) test-store)))

;; PrimV 'read-str tests
(check-equal? (with-input-from-string "hello\n"
                (lambda () (interp-prim (PrimV 'read-str) '() test-store))) "hello")

(check-exn #rx"SHEQ: read-str received incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'read-str) (list "s" "b" "c") test-store)))

(check-exn #rx"SHEQ: read-str read EOF"
           (lambda () 
             (with-input-from-string ""
               (lambda () (interp-prim (PrimV 'read-str) '() test-store)))))

;; PrimV '++ tests
(check-equal? (interp-prim (PrimV '++) (list 4 "hello" #f) test-store) "4hellofalse")
(check-equal? (interp-prim (PrimV '++) '() test-store) "")
(check-equal? (interp-prim (PrimV '++) (list (ArrayV 3 2)) test-store) "#<array>")

;; PrimV 'make-array tests

;; test-store[1] = ArrayV of size 3 of all 10's
(check-equal? (interp-prim (PrimV 'make-array) (list 3 10) test-store) (ArrayV 1 3))

(check-exn #rx"SHEQ: Out of memory"
           (lambda () (interp-prim (PrimV 'make-array) (list 1000000 1) test-store)))

(check-exn #rx"SHEQ: make-array expected size 1 or greater"
           (lambda () (interp-prim (PrimV 'make-array) (list 0 1) test-store)))

(check-exn #rx"SHEQ: make-array expected a natural number for size"
           (lambda () (interp-prim (PrimV 'make-array) (list 2.4 1) test-store)))

(check-exn #rx"SHEQ: make-array received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV 'make-array) (list 2.3) test-store)))

;; PrimV 'array tests

;; test-store[4] = ArrayV of size 3 of all {"a", "b", 3}
(check-equal? (interp-prim (PrimV 'array) (list "a" "b" 3) test-store) (ArrayV 4 3))

(check-exn #rx"SHEQ: array expected at least one element"
           (lambda () (interp-prim (PrimV 'array) '() test-store)))

;; PrimV 'aref tests
(check-equal? (interp-prim (PrimV 'aref) (list (ArrayV 4 3) 0) test-store) "a")

(check-equal? (interp-prim (PrimV 'aref) (list (ArrayV 1 3) 2) test-store) 10)

(check-exn #rx"SHEQ: aref expected an array"
           (lambda () (interp-prim (PrimV 'aref) (list 23 23) test-store)))

(check-exn #rx"SHEQ: aref expected an integer for index"
           (lambda () (interp-prim (PrimV 'aref) (list (ArrayV 4 3) 1.2) test-store)))

(check-exn #rx"SHEQ: aref index out of bounds"
           (lambda () (interp-prim (PrimV 'aref) (list (ArrayV 4 3) 290192) test-store)))

(check-exn #rx"SHEQ: aref received incorrect number of arguments, expected 2, got"
           (lambda () (interp-prim (PrimV 'aref) (list 3 2 3 23 32 32) test-store)))

;; PrimV 'aset! tests

;; test-store : [7, 10, 10, 10, "a", "b, 3, _, _, ...]
(check-equal? (interp-prim (PrimV 'aset!) (list (ArrayV 1 3) 0 "changed") test-store) (NullV))
;; after      : [7, "changed", 10, 10, "a", "b, 3, _, _, ...]
(check-equal? (interp-prim (PrimV 'aref) (list (ArrayV 1 3) 0) test-store) "changed")

(check-exn #rx"SHEQ: aset! expected an array"
           (lambda () (interp-prim (PrimV 'aset!) (list "notarray" 23 1) test-store)))

(check-exn #rx"SHEQ: aset! expected an integer for index"
           (lambda () (interp-prim (PrimV 'aset!) (list (ArrayV 4 3) "parry" 1) test-store)))

(check-exn #rx"SHEQ: aset! index out of bounds"
           (lambda () (interp-prim (PrimV 'aset!) (list (ArrayV 4 3) -12 "bear") test-store)))

(check-exn #rx"SHEQ: aset! received incorrect number of arguments, expected 3, got"
           (lambda () (interp-prim (PrimV 'aset!) (list 0 0) test-store)))

;; ---- Helper Tests ----

;; value->string tests
(check-equal? (val->string 3) "3")
(check-equal? (val->string #t) "true")
(check-equal? (val->string #f) "false")
(check-equal? (val->string "s") "s")
(check-equal? (val->string (CloV '(x) (NumC 4) top-env)) "#<procedure>")
(check-equal? (val->string (PrimV '+)) "#<primop>")
(check-equal? (val->string (ArrayV 5 4)) "#<array>")

;; distinct-args? tests
(check-equal? (distinct-args? '(x y z)) #t)
(check-equal? (distinct-args? '(x y x)) #f)

;; reserved-symbol tests
(check-equal? (reserved-symbol? 'lambda) #t)
(check-equal? (reserved-symbol? '+++) #f)

;; create-env tests
(check-equal? (create-env (list 'a) (list 5) (list (Binding 'random 314)))
              (list (Binding 'a 5) (Binding 'random 314)))
(check-exn #rx"SHEQ: create-env received too many values were passed in application"
           (lambda () (create-env (list 'a) (list 5 3 4) (list (Binding 'random 314)))))
(check-exn #rx"SHEQ: create-env received too few values were passed in application"
           (lambda () (create-env (list 'a 'x) (list 4) (list (Binding 'random 314)))))

;; get-binding tests
(check-equal? (get-binding-val 'sym (list (Binding 'sym 5))) 5)
(check-exn #rx"SHEQ: An unbound identifier" (lambda () (get-binding-val 'sym '())))


;; make-initial-store tests
(check-equal? (make-initial-store 4) '#(1 0 0 0))
(check-equal? (vector-length (make-initial-store 10)) 10)
(check-equal? (vector-ref (make-initial-store 102) 0) 1)

;; allocate tests
(check-equal? (allocate (make-initial-store 12) 3) 1)

(define st (make-initial-store 10))
(check-equal? (allocate st 3) 1)
(check-equal? (vector-ref st 0) 4)
(check-equal? (allocate st 2) 4)
(check-equal? (vector-ref st 0) 6)

(check-exn #rx"SHEQ: Out of memory. Tried to allocate" (lambda () (allocate (make-initial-store 2) 3)))

