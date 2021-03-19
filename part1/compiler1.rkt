#lang nanopass

(require nanopass/base)

;; Definición del predicado que verifica las variables
(define (variable? x)
  (symbol? x))

(define (primitive? x)
  (or
   (eq? x '+)
   (eq? x '-)
   (eq? x '*)
   (eq? x '/)
   (eq? x 'and)
   (eq? x 'or)
   (eq? x 'length)
   (eq? x 'car)
   (eq? x 'cdr)))

(define (constant? x)
  (or
   (number? x)
   (boolean? x)
   (char? x)))

(define (type? x)
  (or
   (eq? x 'Bool)
   (eq? x 'Int)
   (eq? x 'Char)
   (eq? x 'List)
   (eq? x 'String)))

;; LENGUAJES

;; Definición del Lenguaje Fuente
(define-language LF
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t)))
  (Expr (e body)
    x
    pr
    c
    l
    s
    t
    (pr c* ... c)
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (e0 e1 ...)))


;; Definición de un Lenguaje alterno para remove-one-armed-if
(define-language IF
  (extends LF)
  (terminals
    (+ (void (v))))
  (Expr (e body)
    (- (if e0 e1))
    (+ v
       (void))))

;; Definición de un Lenguaje alterno para remove-string 
(define-language L2
  (extends IF)
  (terminals
    (- (string (s))))
  (Expr (e body)
    (- s)))

;; Deficinicion de un lenguaje alterno para renombrar variables
(define-language L3 (extends L2))

;; PARSERS
(define-parser parser-LF LF)
(define-parser parser-IF IF)
(define-parser parser-L2 L2)

;; PROCESOS

;; Proceso del compilador encargado de hacer explicitas las expresiones
;; begin en el cuerpo de lambda, let y letrec
(define-pass make-explicit : LF (ir) -> LF ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* , t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x*, t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* , t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t*, e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* , t*,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* , t*, e*] ...) (begin ,body* ... ,body))]))

;; Preproceso del compilador para quitar los if's que no tienen
;; dos clausulas.
(define-pass remove-one-armed-if : LF (ir) -> IF ()
  (Expr : Expr (ir) -> Expr ()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))

;; Preproceso del compilador para convertir cadenas en una
;; lista de caracteres.
(define-pass remove-string : LF (ir) -> L2 ()
  (Expr : Expr (ir) -> Expr ()
        [(,s) (string->list s)]))


;; Funcion para renombrar las varaibles

;Funcion auxiliar para encontrar las variables libres en
;una expresion
(define (FV-Rename exp)
  (nanopass-case (L2 Expr) exp
                 [,x `(,x)]
                 [(,pr ,c* ... ,c) (append (FV-Rename c) (foldr append '() (map FV-Rename c*)))]
                 [(begin ,e* ... ,e) (append (FV-Rename e) (foldr append '() (map FV-Rename e*)))]
                 ;[(list ,e* ...) (foldr append '() (map FV e*))]
                 [(if ,e0 ,e1 ,e2) (append (FV-Rename e0) (FV-Rename e1) (FV-Rename e2))]
                 ;[(lambda ([,x* ,t*] ...) ,body*) (remove (FV body) x*)]
                 ;[(let ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 ;[(letrec ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 [(,e0 ,e1 ...) (append (FV-Rename e0) (foldr append '() (map FV-Rename e1)))]
                 ))

#|(define-pass rename-var : L2 (ir) -> L3 ()
  (Expr : Expr (ir) -> Expr ()
        [(,s) (string->list s)]))|#















#|

"Primer intento":
(define-pass rename-var : LF (ir list) -> IF ()
  (definitions
    define list '()
    (define (free-variables sexp)
      (cond
        [(symbol? sexp) (list sexp)]
        [(eq? (car sexp) '+) (append (free-variables (cadr sexp)) (free-varaibles (caddr sexp)))]
        [(eq? (car sexp) '-) (append (free-variables (cadr sexp)) (free-varaibles (caddr sexp)))]
        [(eq? (car sexp) '*) (append (free-variables (cadr sexp)) (free-varaibles (caddr sexp)))]
        [(eq? (car sexp) '/) (append (free-variables (cadr sexp)) (free-varaibles (caddr sexp)))]
        [(eq? (car sexp) 'and) (append (free-variables (cadr sexp)) (free-varaibles (caddr sexp)))]
        [(eq? (car sexp) 'or) (append (free-variables (cadr sexp)) (free-varaibles (caddr sexp)))]
        [(eq? (car sexp) 'length) (free-variables (cdr sexp))]
        [(eq? (car sexp) 'car) (free-variables (cadr sexp))]
        [(eq? (car sexp) 'cdr) (free-variables (cadr sexp))]
        [(eq? (car sexp) 'let) (append (free-variables (cdr (cadr sexp))) (remove (car (cadr sexp)) (free-variables caddr sexp)))]
        [else '()]
        )))
  (Expr : Expr (ir list) -> Expr ()
        ))

"Segundo intento"
(module m racket
  (provide counter increment!)
  (define counter 0)
  (define (increment!)
  (set! counter (add1 counter))))

(require 'm)

(define varLig (make-hash))

(define-pass rename-aux : LF(ir) -> LF()
  (definitions
    (define (update)
      (increment!)
      (string->symbol (string-append "x" (number->string counter)))))
  (Expr : Expr(ir) -> Expr ()
    [,x (if (hash-has-key? varLig x) (hash-ref varLig x) (update))]
    [(if ,[e0] ,[e1]) '(if, e0, e1)]
    [(let ([,x* , t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t*, e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* , t*,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* , t*, e*] ...) (begin ,body* ... ,body))]
    ))|#
