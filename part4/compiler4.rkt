#lang nanopass

(require nanopass/base)
(require racket/set)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

(define (primitiva? pr) (memq pr '(+ - * / length car cdr)))

;encapsulamos los elementos que pueden ser quoteados
(define (quotable? q) (or (constant? q) (and (symbol? q) (not (primitive? q))))) 

;; SISTEMA DE TIPOS

;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
;;Verifica si es un tipo basico
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
;; Verifica si es un tipo compuesto
(define (c-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)])
	(or (and (equal? f 'List) (equal? s 'of) (type? t)) 
		(and (type? f) (equal? s '→) (type? t))))
	#f))

;; Verifica si es una primitiva aritmtica
(define (arit? x) (memq x '(+ - * /)))

;; Verifica si es una primitiva de listas
(define (lst? x) (memq x '(length car cdr)))

;; LENGUAJES

;Lenguaje Fuente
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
    c
    l
    s
    pr
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* ...)
    (e0 e1 ...)))


;Lenguaje en el que se sustituye las multiples expresiones en el cuerpo de
;lambda, let y letrec por una única expresión begin
(define-language L0
  (extends LF)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body* ... body)
           (let ([x* t* e*] ...) body* ... body)
           (letrec ([x* t* e*] ...) body* ... body))
        (+ (lambda ([x* t*] ...) body)
           (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))))

;; Definición de un Lenguaje alterno para remove-one-armed-if
(define-language IF
  (extends L0)
  (terminals
    (+ (void (v))))
  (Expr (e body)
    (- (if e0 e1))
    (+ v
       (void))))

;; Definición de un lenguaje alterno para remove-string 
(define-language L2
  (extends IF)
  (terminals
    (- (string (s))))
  (Expr (e body)
    (- s)))

;; Deficinicion de un lenguaje alterno para renombrar variables
(define-language L3 (extends L2))

;; Deficinicion de un lenguaje alterno para remove-logical-operators
(define-language NO-LOGIC-OPS
  (extends L3)
  (terminals
   (- (primitive (pr)))
   (+ (primitiva (pr))))
  (Expr (e body)
        (-  pr)
        (+  pr
            (and e* ...)
            (or e* ...)
            (not e))))

;; Definicion del lenguaje de salida para  remove-logical-operators
(define-language L4
  (extends NO-LOGIC-OPS)
  (Expr (e body)
        (- (and e* ...)
           (or e* ...)
           (not e))))

;; Definición del lenguaje de salida para eta-expand 
(define-language L5
  (extends L4)
  (terminals
    (+ (quotable (q))))
  (Expr (e body)
        (- pr)
        (+ q
           (primapp pr e* ... e0))))

;Lenguaje Resultante de la práctica 3
(define-language L6
  (terminals
   (variable (x))
   (primitiva (pr))
   (constant (c))
   (type (t))
   (quotable (q)))
  (Expr (e body)
    x
    (cuote q)
    (begin e* ... e)
    (primapp pr e* ... e0)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x* t* e*] ...) body)
    (letrec ([x* t* e*] ...) body)
    (list e* ...)
    (e0 e1 ...)))

;Lenguaje para el curry-let
(define-language L7
  (extends L6)
  (Expr (e body)
   (- (let ([x* t* e*] ...) body)
      (letrec ([x* t* e*] ...) body))
   (+ (let ([x t e]) body)
      (letrec ([x t e]) body)
      (let () body)
      (letrec () body))))

; Lenguaje de entrada para la práctica
(define-language L8
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (cuote c)
    (begin e* ... e)
    (primapp pr e* ... e0)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)       ;En L8 debe ser multiparametrico, sino 'curry' no tiene sentido
    ;(lambda ([x t]) body)
    (let ([x t e]) body)
    (letrec ([x t e]) body)
    (letfun ([x t e]) body)
    (list e* ...)
    (e0 e1 ...)))

;Lenguaje para el preproceso curry
(define-language L9
  (extends L8)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body)
           (e0 e1 ...))
        (+ (lambda ([x t]) body)
           (e0 e1))))

;Lenguaje para el preproceso type-const
(define-language L10
  (extends L9)
  (Expr (e body)
        (- (cuote c))
        (+ (const t c))))

;; PARSERS
(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-IF IF)
(define-parser parser-L2 L2)
(define-parser parser-NLO NO-LOGIC-OPS)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)

;; PROCESOS

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))

;; Preproceso del compilador para convertir cadenas en una
;; lista de caracteres.
(define-pass remove-string : LF (ir) -> L2 ()
  (Expr : Expr (ir) -> Expr ()
        [(,s) (string->list s)]))

;; Preproceso del compilador para quitar los if's que no tienen
;; dos clausulas.
(define-pass remove-one-armed-if : LF (ir) -> IF ()
  (Expr : Expr (ir) -> Expr ()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))

;; Preproceso necesario para traducir una expresion de L3 a NLO
(define-pass L3-to-NLO : L3 (ir) -> NO-LOGIC-OPS ()
  (Expr : Expr (ir) -> Expr ()
        [else `(parser-NLO (unparse-L3 ir))]))


;;Preproceso del compilador para sustituir los operadores and,
;;or y not por sus expresiones correspondientes solo con if's
(define-pass remove-logical-operators : NO-LOGIC-OPS (ir) -> L4 ()
  (Expr : Expr (ir) -> Expr ()
        [(and) `(#t)]
        [(and ,[e1]) `(#t)]
        [(and ,[e1] ,[e2]) `(if ,e1 ,e2 #f)] ;Si e1 es false entonces ya todo es false
        [(or) `(#t)]
        [(or ,[e1]) `(#t)]
        [(or ,[e1] ,[e2]) `(if ,e1 #t ,e2)] ;Si e1 es true entonces, ya el or es true
        [(not ,[e1]) `(if ,e1  #f #t)] ;Si se cumple e1 entonces, regreso el negado
        ))

;;Preproceso del compilador para sustituir las expresiones primitivas 
;;por su versión con lamba. Ademas de eso verifica que el operador
;;de la expresion tenga la aridad correcta
(define-pass eta-expand : L4 (ir) -> L5 ()
  (definitions
    (define binarios #hash(                              
                        (+ . ([x0 Int] [x1 Int]))
                        (- . ([x0 Int] [x1 Int]))
                        (* . ([x0 Int] [x1 Int]))
                        (/ . ([x0 Int] [x1 Int]))))
    (define unarios #hash(                               
                        (length . ([x0 List]))
                        (car . ([x0 List]))
                        (cdr . ([x0 List])))))
  (Expr : Expr (ir) -> Expr ()
        [,pr `,(if (hash-has-key? binarios `,pr)
                     `((lambda ,(hash-ref binarios `,pr) (primapp ,pr x0 x1))) 
                     `((lambda ,(hash-ref unarios `,pr) (primapp ,pr x0))))]   
        [(,pr ,[e0]) `,(if (hash-has-key? unarios `,pr)
                             `((lambda ,(hash-ref unarios `,pr) (primapp ,pr x0)) ,e0) 
                             (error "Arity in" `,pr  "must be 2"))]                    
        [(,pr ,[e0] ,[e1]) `,(if (hash-has-key? binarios `,pr)
                                   `((lambda ,(hash-ref binarios `,pr) (primapp ,pr x0 x1)) ,e0, e1) 
                                   (error "Arity in" `,pr "must be 1"))]))

;(eta-expand (parser-L4 '(+ ())))    


;;Preoproceso del compilador para sustituir las constantes del lenguaje
;;por "constantes quoteadas" 
(define-pass quote-const : L5 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr ()
        [,q `(cuote ,q)]))

;;Preproceso del compilador para traducir una aplicacion de funcion a una
;;expresion let tomando como nombres de variables los parametros formales
;;y como valores los parametros reales.
(define-pass direct-app : L6 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr ()
        [((lambda ([,x* ,t*] ...) ,[body]) ,[e*] ...)
         `(let ([,x* ,t* ,e*] ...) ,body)]))

;;Preproceso del compilador para currificar las expresiones let y letrec.
(define-pass curry-let : L6(ir) -> L7 ()
  (definitions
    ;op denota si es un let o un let-rec
    (define (curry vars types exps body op)
      (cond
        [(empty? vars) (unparse-L7 body)]
        [else `(,op ([,(car vars) ,(car types) ,(unparse-L7 (car exps))])
              ,(curry (cdr vars) (cdr types) (cdr exps) body op))])))
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x* ,t* ,[e*]] ... ) ,[body])
         (parser-L7 (curry x* t* e* body 'let))]
        [(letrec ([,x* ,t* ,[e*]] ... ) ,[body])
         (parser-L7 (curry x* t* e* body 'letrec))]))

;;Preproceso del compilador para reemplazar los let utilizados para 
;;definir funciones, por letrec.
(define-pass identify-assigments : L7(ir) -> L7()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,[e]]) ,[body])
         (if (equal? t 'lambda)
             `('letrec ([,x ,t ,e]) ,body)
             ir)]))

;;Preproceso del compilador encargado de  asignarle un identificador 
;;a las funciones anónimas, es decir a las lambas.

;definimos un contador para el renombre
(define fun-count 0)

(define-pass un-anonymous : L7(ir) -> L8 ()
  (definitions
    (define (new-name)
      (begin
        (define str (string-append "foo" (number->string fun-count)))
        (set! fun-count (+ 1 fun-count))
        (string->symbol str))))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t] ...) ,[body])
         (let ([name (new-name)])
           `(letfun ([,name Lambda ,(parser-L8 (unparse-L7 ir))]) ,name))]))

;;Preproceso del compilador que verifica que la expresión no tenga
;;variables libres, de existir variables libres se regresa un error.
;funcion auxiliar para encontar las variables libres en los casos de
;nuestra gramatica.
(define (FV exp)
  (nanopass-case (L8 Expr) exp
                 [,x `(,x)]
                 [(cuote ,c) '()]
                 [(begin ,e* ... ,e) (append (FV e)   (foldr append '() (map FV e*)))]
                 [(primapp ,pr ,e* ... ,e0) (append (FV e0) (foldr append '() (map FV e*)))]
                 [(list ,e* ...) (foldr append '() (map FV e*))]
                 [(if ,e0 ,e1 ,e2) (append (FV e0) (FV e1) (FV e2))]
                 [(lambda ([,x* ,t*]) ,body) (remove (FV body) x*)]
                 [(let ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 [(letrec ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 [(letfun ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 [(,e0 ,e1 ...) (append (FV e0) (foldr append '() (map FV e1)))]
                 ))

(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [else (if (empty? (FV ir))
                  ir
                  (error "There are free variables in your expression"))]))


;;Preporceso encargado de currificar las expresiones lambda así
;;como las aplicaciones de función.
(define-pass curry : L8 (ir) -> L9 ()
  (definitions
    (define (currify-lambda vars types body)
      (cond
        [(empty? vars) (unparse-L9 body)]
        [else `(lambda ([,(car vars) ,(car types)])
              ,(currify-lambda (cdr vars) (cdr types) body))]))
    (define (currify-app e0 e1)
      (cond
        [(empty? e1) e0]
        [else (currify-app `(,e0 ,(car e1)) (cdr e1))])))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x* ,t*] ...) ,[body])
         (parser-L9 (currify-lambda x* t* body))]
        [(,e0 ,e1 ...) (parser-L9 (currify-app (unparse-L8 e0) (map unparse-L8 e1)))])) 

;(curry (parser-L8 '(foo x (cuote 5))))

;;Preporceso encargado decirnos que tipo de constante es
;;el parametro (int, char o boolean).
(define-pass type-const : L9 (ir) -> L10 ()
  (definitions
    (define (type c)
      (cond
        [(integer? c) `(const Int ,c)]
        [(char? c) `(const Char ,c)]
        [(boolean? c) `(const Bool ,c)])))
  (Expr : Expr (ir) -> Expr ()
        [(cuote ,c) (parser-L10 (type c))]))

;;Funcion J que implementa las reglas definidas para L10
;;segun el algoritmo J.

;FUNCIONES AUXILIARES 

; Función que verifica si dos tipos son unificables, para mas detalle consultar 
; la especificación.
(define (unify t1 t2)
  (if (and (type? t1) (type? t2))
    (cond 
      [(equal? t1 t2) #t]
      [(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
      [(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
      [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
      [else #f])
    (error "Expected 2 types")))

; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
  (if (equal? (car lst) 'List)
    (part (cdr lst))
    (car lst)))

(define (J exp context)
  (nanopass-case (L10 Expr) exp
			     [,x (let ([searched-variable (findf (lambda (y) (equal? (car y) x)) context)])
			           (if searched-variable 
			              (cdr searched-variable) 
			              (error "Variable not in context")))]
			     [(const ,t ,c) t]
			     [(list) 'List]
			     [(begin ,e* ... ,e) (first (append 
			                                  (list (J e context)) 
			                                  (foldl append '() (list (map (lambda (x) (J x context)) e*)))))]
			     [(primapp ,pr ,e* ... ,e0) 
			      (cond
			        [(arit? pr) (if (and (equal? (J e0 context) 'Int) (equal? (first (map (lambda (x) (J x context)) e*)) 'Int))
			                                    'Int
			                                    (error "Binary operators must have Integer parameters"))]
			        [(lst? pr) (let ([type-lst-operators (J e0 context)])
			                        (if (c-type? type-lst-operators)
			                            (match pr
			                              ['car (third type-lst-operators)]
			                              ['cdr type-lst-operators]
			                              ['length 'Int])
			                            (error "Type does not match the list operator")))])]
			     [(if ,e0 ,e1 ,e2) (let ([t0 (J e0 context)]
			                             [t1 (J e1 context)]
			                             [t2 (J e2 context)])
			                          (if (and (equal? 'Bool (J e0 context)) (unify t1 t2))
			                            t1
			                            (error "Different type between expresions")))]
			     [(lambda ([,x ,t]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                      [s (J body new-context)])
			                              		  `(,t → ,s))]
			     [(let ([,x ,t ,e]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                      [t0 (J e context)]
			                                      [s (J body new-context)])
			                                  (if (unify t t0)
			                                    s
			                                    (error "The type doesn't correspond to the value")))]
			     [(letrec ([,x ,t ,e]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                         [t0 (J e new-context)]
			                                         [s (J body new-context)])
			                                  (if (unify t t0)
			                                    s
			                                    (error "The type doesn't correspond to the value")))]
			     [(letfun ([,x ,t ,e]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                         [t0 (J e context)]
			                                         [s (J body new-context)])
			                                  (if (and (unify t t0) (equal? (cadr t) '→))
			                                      s
			                                      (error "The type doesn't correspond to the value")))]
			     [(list ,e* ... ,e) (let* ([types (append (list (J e context))(map (lambda (x) (J x context)) e*))]
			                               [t (part types)]
			                               [eqt (map (lambda (x) (unify t x)) types)])
			                      (if (foldr (lambda (x y) (and x y)) #t eqt)
			                      `(List of ,t)
			                      (error "Lists must be homogeneous")))]
			     [(,e0 ,e1) (let* ([t0 (J e0 context)]
			                       [R (third t0)]
			                       [t1 (J e1 context)])
			                  (if (unify t0 (t1 '→ R))
			                      R
			                      (error "Types can not be inferred. Can not unify")))]
			     [else (error "Types can not be inferred")]))

;;Preproceso que se encarga de sustituir las Lambdas por su tipo,
;;es decir, (T → T), asi como tambien las listas (List of T).

;Funcion auxiliar que obtiene el contexto general de la 
;expresion. Solo necesitamos checar aquellos constructores que 
;pueden agregar nuevas variables al contexto.
;En el body de las expresiones tenemos que asegurarnos de no 
;agregar repetidas veces las nuevas variables.
(define (get-abs-context e)
    (nanopass-case (L10 Expr) e
			       [(begin ,e* ... ,e) (append (map (lambda (x) (get-abs-context x)) e*) 
			       							   (get-abs-context e))]
			       [(if ,e0 ,e1 ,e2) (append (get-abs-context e0) 
			       							 (get-abs-context e1) 
			       							 (get-abs-context e2))] 
			       [(lambda ([,x ,t]) ,body) (set-add (get-abs-context body) 
			       									  (cons x t))]
			       [(let ([,x ,t ,e]) ,body) (append (set-add (get-abs-context body) (cons x t)) 
			       									 (get-abs-context e))]
			       [(letrec ([,x ,t ,e]) ,body) (append (set-add (get-abs-context body) (cons x t)) 
			       										(get-abs-context e))]
			       [(letfun ([,x ,t ,e]) ,body) (append (set-add (get-abs-context body) (cons x t))
			       										(get-abs-context e))]
			       [(,e1 ,e2) (append (get-abs-context e1) 
			       					  (get-abs-context e2))]
			       [else '()] ;Si no se ha agregado nada, entonces lidiamos con un contexto vacio
			       ))

;Solo se sustituyen expresiones que sean del tipo Lambda o List.
(define-pass type-infer : L10 (ir) -> L10 ()
  (definitions
  	(define context (get-abs-context ir)))
  (Expr : Expr (ir) -> Expr()
    [(lambda ([,x ,t]) ,[body]) (if (or (equal? t 'Lambda) (equal? t 'List))
                                    `(lambda ([,x ,(J body context)]) ,body) 
                                    ir)]
    [(let ([,x ,t ,[e]]) ,[body]) (if (equal? t 'List)
                                  	  `(let ([,x ,(J e context) ,e]) ,body)
                                  	  ir)]
    [(letrec ([,x ,t ,[e]]) ,[body]) (if (or (equal? t 'Lambda) (equal? t 'List))
                                  		 `(letrec ([,x ,(J e context) ,e]) ,body)
                                      	 ir)]
    [(letfun ([,x ,t ,[e]]) ,[body]) (if (or (equal? t 'Lambda) (equal? t 'List))
                                  		 `(letfun ([,x ,(J e context) ,e]) ,body)
                                      	 ir)]))

;;PREUBAS PARA EL PROCESO TYPE-INFER
;(type-infer (parser-L10 '(letrec ([foo Lambda (lambda ([x Int]) x)]) (foo (const Int 5)))))
;(type-infer (parser-L10 '(let ([x List (list)]) x)))
;(type-infer (parser-L10 '(let ([x List (list (const Bool #t) (const Bool #t) (const Bool #f) (const Bool #t))]) x)))
;(type-infer (parser-L10 '(list (const Bool #t) (const Bool #f))))

(J (parser-L10 '(let ([x Bool (const Bool #f)]) x)) '())

;; PRUEBAS PARA LA FUNCIÓN J				
#|(J (parser-L10 'x) `( ,(cons 'x 'Int)))
;; Salida : 'Int
(J (parser-L10 '(const Int 5)) '())
;; Salida : 'Int
(J (parser-L10 '(begin x x x (const Int 5) x x x x (const Bool #t))) `( ,(cons 'x 'Int)))
;; Salida : 'Bool
(J (parser-L10 '(primapp + (const Int 6) (const Int 5))) '())
;; Salida : 'Int
(J (parser-L10 '(primapp cdr (list (const Int 6) (const Int 5)))) '())
;; Salida : '(List of Int)
(J (parser-L10 '(primapp car (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
(J (parser-L10 '(primapp length (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
(J (parser-L10 '(if (const Bool #t) x (const Int 5))) `( ,(cons 'x 'Int)))
;; Salida : 'Int
(J (parser-L10 '(lambda ([x Int]) x)) '())
;; Salida : '(Int → Int)
(J (parser-L10 '(let ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
(J (parser-L10 '(letrec ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
(J (parser-L10 '(list)) '())
;; Salida : 'List
(J (parser-L10 '(list (const Bool #t) (const Bool #f))) '())
;; Salida : '(List of Bool)
(J (parser-L10 '(list (list) (list (const Bool #f) (const Bool #t)))) '())
;; Salida : '(List of (List of Bool))
;; CASOS DE ERROR
(J (parser-L10 '(list (const Int 5) (const Bool #f))) '())
;; Salida : error : Listas homogeneas
(J (parser-L10 '(list (list) (list (list (const Bool #t) (const Bool #f))) (list (list (const Int 5) (const Int 6))))) '())
;; Salida : error : Listas homogeneas|#

(boolean? #t)
