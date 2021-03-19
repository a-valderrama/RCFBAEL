#lang nanopass

(require nanopass/base)
(require racket/set)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr and or not)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

(define (type? x) (memq x '(Bool Char Int List String Lambda)))

(define (primitiva? pr) (memq pr '(+ - * / length car cdr)))

;encapsulamos los elementos que pueden ser quoteados
(define (quotable? q) (or (constant? q) (and (symbol? q) (not (primitive? q))))) 

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

;Lenguaje para un-anonymous
(define-language L8
  (extends L7)
  (Expr (e body)
        (+ (letfun ([x t e]) body))))

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
        [(,pr) `,(if (hash-has-key? binarios `,pr)
                     `((lambda ,(hash-ref binarios `,pr) (primapp ,pr x0 x1))) 
                     `((lambda ,(hash-ref unarios `,pr) (primapp ,pr x0))))]   
        [((,pr) ,[e0]) `,(if (hash-has-key? unarios `,pr)
                             `((lambda ,(hash-ref unarios `,pr) (primapp ,pr x0)) ,e0) 
                             (error "Arity in" `,pr  "must be 2"))]                    
        [((,pr) ,[e0] ,[e1]) `,(if (hash-has-key? binarios `,pr)
                                   `((lambda ,(hash-ref binarios `,pr) (primapp ,pr x0 x1)) ,e0, e1) 
                                   (error "Arity in" `,pr "must be 1"))]))                           

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
        [(lambda ([,x ,t]) ,[body])
         (let ([name (new-name)])
           `(letfun ([,name Lambda ,(parser-L8 (unparse-L7 ir))]) ,name))]))

;(un-anonymous (parser-L7 '(lambda ([x Bool]) (if x (cuote 1) (cuote 2)))))

;;Preproceso del compilador que verifica que la expresión no tenga
;;variables libres, de existir variables libres se regresa un error.

;funcion auxiliar para encontar las variables libres en los casos de
;nuestra gramatica.
(define (FV exp)
  (nanopass-case (L8 Expr) exp
                 [,x `(,x)]
                 [(cuote ,q) '()]
                 [(begin ,e* ... ,e) (append (FV e) (foldr append '() (map FV e*)))]
                 [(primapp ,pr ,e* ... ,e0) (append (FV e0) (foldr append '() (map FV e*)))]
                 [(list ,e* ...) (foldr append '() (map FV e*))]
                 [(if ,e0 ,e1 ,e2) (append (FV e0) (FV e1) (FV e2))]
                 [(lambda ([,x* ,t*]) ,body) (remove (FV body) x*)]
                 [(let ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) (list x))]
                 [(letrec ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 [(letfun ([,x ,t ,e]) ,body) (remove (append (FV body) (FV e)) x)]
                 [(,e0 ,e1 ...) (append (FV e0) (foldr append '() (map FV e1)))]
                 ))

(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [else (if (empty? (FV ir))
                  ir
                  (error "There are free variables in your expression"))]))



(verify-vars (parser-L8 '(let ([x Int (cuote 3)]) (primapp + x (cuote 3))))) 
;(verify-vars (parser-L8 '(primapp + (cuote 3) x)))
;(verify-vars (parser-L8 '(x)))



