#lang nanopass

;;PREDICADOS

(define symbol-table (make-hash))

(define fun-count 0)

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

;; SISTEMA DE TIPOS
;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
(define (c-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)])
	(or (and (equal? f 'List) (equal? s 'of) (type? t)) 
		(and (type? f) (equal? s '→) (type? t))))
	#f))

(define (arit? x) (memq x '(+ - * /)))

(define (lst? x) (memq x '(length car cdr)))

;;LENGUAJES

;Lenguaje para el preproceso type-const
(define-language L10
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (const t c)
    (begin e* ... e)
    (primapp pr e* ... e0)
    (if e0 e1 e2)
    (lambda ([x t]) body)
    (let ([x t e]) body)
    (letrec ([x t e]) body)
    (letfun ([x t e]) body)
    (list e* ...)
    (e0 e1)))

;Leguaje necesario para modificar los 
;constructores de asignacion
(define-language L11
  (extends L10)
  (Expr (e body)
    (- (lambda ([x t]) body))
    (+ (lambda ([x* t*] ...) body))))

;Leguaje necesario para descurrificar 
;lambdas
(define-language L12
  (extends L11)
  (Expr (e body)
    (- (let ([x t e]) body)
       (letrec ([x t e]) body)
       (letfun ([x t e]) body))
    (+ (let body)
       (letrec body)
       (letfun body))))

;;PARSERS
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L12 L12)

;;PROCESOS

;Preproceso para descurrificar las lambdas
(define-pass uncurry : L10 (ir) -> L11 ()
  (definitions
  	(define (uncurry var type body)
  	  (let* ([new-variables `([,var ,type])]
  	  		 [new-body (unparse-L10 body)]
  	  	     [lambda-parts (uncurry-aux new-variables new-body)])
  			`(lambda ,(first lambda-parts) ,(second lambda-parts))))
  	(define (uncurry-aux new-variables new-body)
  		(cond
  		  [(equal? 'lambda (car new-body))
  		  	(uncurry-aux `,(append new-variables (cadr new-body)) `,(caddr new-body))]
  		  [else (append (list new-variables) (list new-body))])))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,body) (parser-L11 (uncurry x t body))]
        [else ir]))

;(uncurry (parser-L10 '(lambda ([x Int]) (lambda ([y Int]) (primapp + x y)))))
;(uncurry (parser-L10 '(lambda ([x Int]) (lambda ([y Int]) (lambda ([z Int]) (primapp + x y))))))
;(uncurry (parser-L10 '(lambda ([x Int]) (lambda ([y Int]) (lambda ([z Int]) (lambda ([w Int]) (primapp + x y)))))))

;Funcion que genera la tabla de simbolos de 
;alguna expresion
(define (symbol-table-var exp)
  (nanopass-case (L11 Expr) exp
                 [(begin ,e* ... ,e) (begin
                 					   (symbol-table-var e)
                 					   (map symbol-table-var e*)
                 					   symbol-table)]
                 [(primapp ,pr ,e* ... ,e0) (begin
                 						   	  (symbol-table-var e0)
                 						      (map symbol-table-var e*)
                 						      symbol-table)]
                 [(if ,e0 ,e1 ,e2) (begin 
                 					 `,(if (symbol-table-var e0) (symbol-table-var e1) (symbol-table-var e2))
                 					 symbol-table)]
                 [(lambda ([,x ,t]) ,body) (begin
                 							 (symbol-table-var body)
                 							 symbol-table)]
                 [(let ([,x ,t ,e]) ,[body])    (begin
                 								  `,(hash-set! symbol-table x (cons t (unparse-L11 e)))
                 								  symbol-table)]
                 [(letrec ([,x ,t ,e]) ,[body]) (begin 
                 								  (symbol-table-var e)
                 								  `,(hash-set! symbol-table x (cons t (unparse-L11 e)))
                 								  symbol-table)]
                 [(letfun ([,x ,t ,e]) ,[body]) (begin 
                 								  (symbol-table-var e)
                 								  `,(hash-set! symbol-table x (cons t (unparse-L11 e)))
                 								  symbol-table)]
                 [(list ,e* ...) (begin 
                 	 			   (map symbol-table-var e*)
                 	 			   symbol-table)]
                 [(,e0 ,e1) (begin
                 			  (symbol-table-var e0)
                 			  (symbol-table-var e1)
                 			  symbol-table)]
                 [else symbol-table]
                 ))

;(symbol-table-var (parser-L11 '(begin (let ([x Int (const Int 3)]) (primapp + x x))
;									  (letfun ([y Int (const Int 4)]) (primapp + y y)))))
;(symbol-table-var (parser-L11 '(primapp + (const Int 1) (const Int 2))))
;(symbol-table-var (parser-L11 '(if (const Bool #f) (primapp + x x) (primapp + x x))))
;(symbol-table-var (parser-L11 '(let ([x Int (const Int 3)]) (let ([y Int (const Int 4)]) (primapp + x x)))))
;(symbol-table-var (parser-L11 '(letrec ([foo (Int → Int) (lambda ([x Int]) x)]) (foo (const Int 5)))))
;(symbol-table-var (parser-L11 '(list (let ([x Int (const Int 3)]) (primapp + x x)) (let ([y Int (const Int 4)]) (primapp + y y)))))
;(symbol-table-var (parser-L11 '((let ([x Int (const Int 3)]) (primapp + x x)) (let ([y Int (const Int 4)]) (primapp + y y)))))

;Preproceso que modifica a los constructores let,
;letrec y letfun, eliminando el valor asociado
;a los identificadores y el tipo correspondiente.
(define-pass assignment : L11 (ir) -> L12 (table)
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body])    `(let ,body)]
       	[(letrec ([,x ,t ,[e]]) ,[body]) `(letrec ,body)]
       	[(letfun ([,x ,t ,[e]]) ,[body]) `(letfun ,body)])
  (values (Expr ir) (symbol-table-var ir)))

;(assignment (parser-L11 '(letrec ([foo (Int → Int) (lambda ([x Int]) x)]) (foo (const Int 5)))))
;(assignment (parser-L11 '(letrec ([foo (Int → Int) (lambda ([x Int]) x)]) (let ([x Int (const Int 5)]) (foo x)))))

