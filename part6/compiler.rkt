#! /usr/bin/env racket

#lang nanopass

(require racket/hash)

(define fun-count 0)

;;Contador de las variables utilizadas (para los indices)
(define counter 0)

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x)) (not (type? x)) (not (reservada? x))))

(define (reservada? x) (memq x '(let letrec letfun while for define list lambda if)))

(define (primitiva? x) (or (arit? x) (lst? x)))

(define (primitive? x) (memq x '(+ - * / < > equal? iszero? ++ -- and or not length car cdr equal-lst? empty? elem? append concat cons)))

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

(define (arit? x) (memq x '(+ - * / > < equal?)))

(define (lst? x) (memq x '(length car cdr equal-lst? elem? concat)))

(define (lst1? x) (memq x '(car cdr length)))
(define (lst2? x) (memq x '(concat equal-lst? elem?)))

(define (length? x) (integer? x))

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
    (while [e0] e1)
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

;;Extensión del lenguaje para agregar el pass remove-one-armed-if
(define-language L1
  (extends L0)
  (terminals
   (+ (void(v))))
  (Expr (e body)
        (- (if e0 e1))
        (+ v)))

;;Extensión del lenguaje para tener manejar ahora a las cadenas como
;;listas de caracteres. Por ello, eliminamos el tipo String
(define-language L2
  (extends L1)
    (terminals
      (- (string (s))))
    (Expr (e body)
          (- s)))

(define-language L-NLO
  (extends L2)
  (terminals
   (- (primitive (pr)))
   (+ (primitiva (pr))))
  (Expr (e body)
        (+ (and e* ...)
           (or e* ...)
           (not e)
           (iszero? e0)
           (++ e0)
           (-- e0)
           (empty? e0)
           (cons e0 e1)
           (append e0 e1))))

;;Extensión del lenguaje en la que se redefinen los operadores lógicos del
;;lenguaje con sus equivalentes en expresiones if
;;Definimos una nueva extensión del lenguaje (L4)
(define-language L3
  (extends L-NLO)
  (Expr (e body)
        (- (and e* ...)
           (or e* ...)
           (not e)
           (iszero? e0)
           (++ e0)
           (-- e0)
           (empty? e0)
           (cons e0 e1)
           (append e0 e1))))

(define-language L4
  (extends L3)
  (Expr (e body)
        (- pr)
        (+ (primapp pr e* ... e0))))

(define-language L5
  (extends L4)
  (Expr (e body)
        (- c)
        (+ (cuote c))))

(define-language L6
  (extends L5)
  (Expr (e body)
        (- (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))
        (+ (letrec ([x t e]) body)
           (let ([x t e]) body))))

(define-language L7
  (extends L6)
  (Expr (e body)
        (+ (letfun ([x t e]) body))))

(define-language L8
  (extends L7)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body)
           (e0 e1 ...))
        (+ (lambda ([x t]) body)
           (e0 e1))))

(define-language L9
  (extends L8)
  (Expr (e body)
        (- (cuote c))
        (+ (const t c))))

(define-language L10
  (extends L9)
  (Expr (e body)
    (- (lambda ([x t]) body))
    (+ (lambda ([x* t*] ...) body))))

(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L1 L1)
(define-parser parser-L2 L2)
(define-parser parser-L-NLO L-NLO)
(define-parser parser-L3 L3)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)

;;;;;;;;;PROCESOS;;;;;;;;;

(define var-count 0)

(define (new-var)
      (begin
        (define nv (string-append "x" (number->string var-count)))
        (set! var-count (+ var-count 1))
        (string->symbol nv)))

#|(define (zip l1 l2)
  (if (or (empty? l1) (empty? l2))
      '()
      (cons `(,(car l1) ,(car l2)) (zip (cdr l1) (cdr l2)))))

(define (zip3 l1 l2 l3)
  (if (or (empty? l1) (empty? l2) (empty? l3))
      '()
      (cons `(,(car l1) ,(car l2) ,(car l3))
            (zip3 (cdr l1) (cdr l2) (cdr l3)))))

(define (hash-merge h1 h2)
  (begin (define res (make-hash))
         (hash-union! res h1)
         (hash-union! res h2)
         res))

(define (sublist list start number)
  (cond ((> start 0) (sublist (cdr list) (- start 1) number))
        ((> number 0) (cons (car list)
                      (sublist (cdr list) 0 (- number 1))))
        (else '())))

(define is-def #f)
;; (zip '(1 2 3) '(a b c))
;; (zip3 '(1 2 3) '(a b c) '(x y z))

(define-pass rename-var : LF(ir) -> LF()
  (definitions
    (define (get-names lv)
      (begin
        (define res (make-hash))
        (for ([v lv])
          (hash-set! res v (new-var)))
        res))
    (define (rnm expr m)
      (nanopass-case (LF Expr) expr
                     [,x (if (hash-has-key? m x)
                             (hash-ref m x)
                             (new-var))]
                    [(begin ,e* ... ,e)
                      (append '(begin) (for/list ([i (append e* `(,e))])
                                         (rnm i m)))]
                     [(if ,e0 ,e1)
                      `(if ,(rnm e0 m) ,(rnm e1 m))]
                     [(if ,e0 ,e1 ,e2)
                      `(if ,(rnm e0 m) ,(rnm e1 m) ,(rnm e2 m))]
                     [(while [,e0] ,e1)
                      `(while [,(rnm e0 m)] ,(rnm e1 m))]
                     [(lambda ([,x* ,t*] ...) ,body* ... ,body)
                      (letrec ([namemap (get-names x*)]
                               [renames (for/list ([i x*])
                                          (hash-ref namemap i))])
                        (append
                         `(lambda ,(zip renames t*))
                         (for/list ([i (append body* `(,body))])
                           (rnm i (hash-merge m namemap)))))]
                     [(let ([,x* ,t* ,e*] ...) ,body* ... ,body)
                      (letrec ([namemap (get-names x*)]
                               [renames
                                (map (lambda (v) (hash-ref namemap v)) x*)]
                               [ers (map (lambda (x) (rnm x m)) e*)]
                               [bodyrs (map (lambda (x)
                                              (rnm x (hash-merge m namemap)))
                                            (append body* `(,body)))])
                        (append `(let ,(zip3 renames t* ers)) bodyrs))]
                     [(letrec ([,x* ,t* ,e*] ...) ,body* ... ,body)
                      (letrec ([namemap (get-names x*)]
                               [renames
                                (map (lambda (v) (hash-ref namemap v)) x*)]
                               [ers (map (lambda (x) (rnm x m)) e*)]
                               [bodyrs (map (lambda (x)
                                              (rnm x (hash-merge m namemap)))
                                            (append body* `(,body)))])
                        (append `(letrec ,(zip3 renames t* ers)) bodyrs))]

                     ;; Este caso esta comentado porque interfiere con
                     ;; el caso (pr c* ... c)
                     
                     ;; [(,e ,e* ...)
                     ;;  (map (lambda (x) (rnm x m))
                     ;;       (cons e e*))]

                     [else (unparse-LF expr)]
                     )))
  (Expr : Expr(ir) -> Expr()
        [else (parser-LF (rnm ir (make-hash '[])))]))|#

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `,c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))


;;Pass que permite la existencia de expresiones if sin else
(define-pass remove-one-armed-if : L0 (ir) -> L1 ()
  (Expr : Expr (ir) -> Expr ()
  [(if ,[e1] ,[e2]) `(if ,e1 ,e2 (void))]))

;;Pass que redefine la naturaleza de las cadenas en el lenguaje.
;;En lugar de ser cadenas per se, son listas de caracteres
;;Similar a lo que se sucede en C o Haskell
(define-pass remove-string : L1 (ir) -> L2 ()
  (Expr : Expr (ir) -> Expr ()
        [,s (parser-L2 (append '(list) (string->list s)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-pass L2-to-NLO : L2 (ir) -> L-NLO ()
  (Expr : Expr (ir) -> Expr ()
        [else (parser-L-NLO (unparse-L2 ir))]))

(define-pass remove-stupid-operators : L-NLO (ir) -> L3 ()
  (Expr : Expr (ir) -> Expr ()
        [(and) `(#t)]
        [(and ,[e1]) `(#t)]
        [(and ,[e1] ,[e2]) `(if ,e1 ,e2 #f)]
        [(or) `(#t)]
        [(or ,[e1]) `(#t)]
        [(or ,[e1] ,[e2]) `(if ,e1 #t ,e2)]
        [(iszero? ,[e0]) `(equal? ,e0 0)]
        [(++ ,[e0]) `(+ ,e0 1)]
        [(-- ,[e0]) `(- ,e0 1)]
        [(empty? ,[e0]) `(equal-lst? ,e0 (list))]
        [(append ,[e0] ,[e1]) `(concat  ,e1 (list ,e0))]
        [(cons ,[e0] ,[e1]) `(concat (list ,e0) ,e1)]
        [(not ,[e1]) `(if ,e1 #f #t)]))


;;Preproceso del compilador para sustituir las expresiones primitivas 
;;por su versión con lamba. Ademas de eso verifica que el operador
;;de la expresion tenga la aridad correcta
(define tipos #hash(
                    (+ . Int)
                    (- . Int)
                    (* . Int)
                    (/ . Int)
                    (length . List)
                    (car . List)
                    (cdr . List)
                    (< . Int)
                    (> . Int)
                    (equal? . Int)
                    (equal-lst? . List)
                    (concat . List)
                    (elem? . List)))

;;Pass que recibe una primitiva de L4 y la devuelve como una lambda o aplicación de función en el lenguaje L5.
(define-pass eta-expand : L3 (ir) -> L4 ()
  (definitions
    (define var1 (new-var))
    (define var2 (new-var))
    (define (elem-type e0)
    	(cond
    		[(integer? e0) 'Int]
    		[(char? e0) 'Char]
    		[(boolean? e0) 'Bool])))
  (Expr : Expr (ir) -> Expr ()
        [(,pr) (if (equal? `,(hash-ref tipos `,pr) 'Int)
                   `(lambda ([,var1 ,(hash-ref tipos `,pr)] [,var2 ,(hash-ref tipos `,pr)]) (begin (primapp ,pr ,var1 ,var2)))
                   `(lambda ([,var1 ,(hash-ref tipos `,pr)]) (begin (primapp ,pr ,var1))))]
        [(,pr ,[e0]) `((lambda ([,var1 ,(hash-ref tipos `,pr)]) (begin (primapp ,pr ,var1))) ,e0)]
        [(,pr ,[e0] ,[e1])  (if (equal? pr 'elem?)
    							`((lambda ([,var1 ,(elem-type `,e0)] [,var2 ,(hash-ref tipos `,pr)]) (begin (primapp ,pr ,var1 ,var2))) ,e0 ,e1)
        						`((lambda ([,var1 ,(hash-ref tipos `,pr)] [,var2 ,(hash-ref tipos `,pr)]) (begin (primapp ,pr ,var1 ,var2))) ,e0 ,e1))]))


(define-pass quote-const : L4 (ir) -> L5 ()
  (Expr : Expr (ir) -> Expr ()
        [,c `(cuote ,c)]))

(define-pass purify-recursion : L5 (ir) -> L5 ()
  (definitions
    (define (curry vars types exps body)
      (cond
        [(empty? vars) (unparse-L5 body)]
        [(not (equal? (car types) 'Lambda))
         `(let ([,(car vars) ,(car types) ,(unparse-L5 (car exps))])             ;variables -> de la "currificacion"
            ,(curry (cdr vars) (cdr types) (cdr exps) body))]                    ;body
        [else `(letrec ([,(car vars) ,(car types) ,(unparse-L6 (car exps))])     ;variables -> cuando no hay "currificacion
                 ,(curry (cdr vars) (cdr types) (cdr exps) body))])))            ;body
  (Expr : Expr (ir) -> Expr ()
        [(letrec ([,x* ,t* ,[e*]] ... ) ,[body])
         (parser-L5 (curry x* t* e* body))
         ]))

;;Pass que transforma las aplicaciones de funciones a una
;;expresión let equivalente
(define-pass direct-app : L5 (ir) -> L5 ()
  (Expr : Expr (ir) -> Expr ()
        [((lambda ([,x* ,t*] ...) ,[body]) ,[e*] ...)
         `(let ([,x* ,t* ,e*] ...) ,body)]))

;;Pass que currifica las expresiones let y letrec
(define-pass curry-let : L5 (ir) -> L6 ()
  (definitions
    (define (curry vars types values body op)
      (cond
        [(empty? vars) (unparse-L6 body)]
        [else `(,op ([,(car vars) ,(car types) ,(unparse-L6 `,(car values))]) ,(curry (cdr vars) (cdr types) (cdr values) body op))])))
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x* ,t* ,[e*]] ...) ,[body]) (parser-L6 (curry x* t* e* body 'let))]
        [(letrec ([,x* ,t* ,[e*]] ...) ,[body]) (parser-L6 (curry x* t* e* body 'letrec))]))

;;Pass para identificar las funciones definidas en let y pasarlas a un letrec
(define-pass identify-assigments : L6 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,[e]]) ,body)
         (if (equal? t 'Lambda) `(letrec ([,x ,t ,e]) ,body) ir)]))

;;contador auxiliar para crear un nombre de función
(define contador 0)

;;Pass para asignarle un nombre a las variables anónimas
(define-pass un-anonymous : L6 (ir) -> L7 ()
  (definitions
    (define (new-name)
      (begin
        (define str (string-append "foo" (number->string contador)))
        (set! contador (+ 1 contador))
        (string->symbol str))))
  (Expr : Expr (ir) -> Expr ()
        ([lambda ([,x ,t] ...) ,[body]]
         (let ([name (new-name)]) `(letfun ([,name Lambda ,(parser-L7 (unparse-L6 ir))]) ,name)))))

;;Expresión que encuentra las variables libres
(define (free-var exp)
  (nanopass-case (L7 Expr) exp
         [,x (if (equal? x 'void) '() `(,x))]
         [(cuote ,c) '()]
         [(begin ,e* ... ,e) (append (free-var e) (foldr append '() (map free-var e*)))]
         [(primapp ,pr ,e* ... ,e0) (append (free-var e0) (foldr append '() (map free-var e*)))]
         [(if ,e0 ,e1 ,e2) (append (free-var e0) (free-var e1) (free-var e2))]
         [(lambda ([,x* ,t*] ...) ,body) (remove* x* (free-var body))]
         [(let ([,x ,t ,e]) ,body) (remove* (list x) (append (free-var body) (free-var e)))]
         [(letrec ([,x ,t ,e]) ,body) (remove* (list x) (append (free-var body) (free-var e)))]
         [(while [,[e0]] ,[e1]) (append (free-var e0) (free-var e1))]
         [(letfun ([,x ,t ,e]) ,body) (remove* (list x) (append (free-var body) (free-var e)))]
         [(list ,e* ...) (foldr append '() (map free-var e*))]
         [(,e0 ,e1 ...) (append (free-var e0) (foldr append '() (map free-var e1)))]
         [else '()]))


(define-pass verify-vars : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [else (if (empty? (free-var ir)) ir (error "No pueden haber variables libres"))]))

;;Verifica que las operaciones tengan la aridad deseada
(define-pass verify-arity : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(primapp ,pr ,[e0]) (if (lst1? pr) ir (error "Aridad incorrecta"))]
        [(primapp ,pr ,[e0] ,[e1]) (if (or (lst2? pr) (arit? pr)) ir (error "Aridad incorrecta"))]))

;;Pass que currifica las expresiones lambda
(define-pass curry : L7 (ir) -> L8 ()
  (definitions
    (define (curry-lambda vars types body)
      (cond
        [(empty? vars) (unparse-L8 body)]
        [else `(lambda ([,(car vars) ,(car types)]) ,(curry-lambda (cdr vars) (cdr types) body))]))
    (define (curry-app primero resto)
      (cond
        [(empty? resto) primero]
        [else (curry-app `(,primero ,(car resto)) (cdr resto))])))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x* ,t*] ...) ,[body]) (parser-L8 (curry-lambda x* t* body))]
        [(,e0 ,e1 ...) (parser-L8 (curry-app (unparse-L7 e0) (map unparse-L7 e1)))]))

;;Pass que envuelve las constantes del lenguaje, especificando su tipo
(define-pass type-const : L8 (ir) -> L9 ()
  (Expr : Expr (ir) -> Expr ()
        [(cuote ,c)
         (cond
           [(integer? c) `(const Int ,c)]
           [(char? c) `(const Char ,c)]
           [(boolean? c) `(const Bool ,c)])]))

;; Función que verifica si dos tipos son unificables, para mas detalle consultar 
;; la especificación.
(define (unify t1 t2)
  (if (and (type? t1) (type? t2))
    (cond 
      [(equal? t1 t2) #t]
      [(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
      [(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
      [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
      [else #f])
    (error "Se esperan 2 tipos para unificar")))

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
  (if (equal? (car lst) 'List)
    (part (cdr lst))
    (car lst)))


;;Función auxiliar para extraer la ocurrencia de una variable en un contexto
(define (busca-variable x lst)
  (findf (lambda (w) (equal? (car w) x)) lst))

;;Función J, para encontrar el tipo de una expresión
(define (J exp context)
  (nanopass-case (L9 Expr) exp
			     [,x (let ([searched-variable (findf (lambda (y) (equal? (car y) x)) context)])
			           (if searched-variable
			             (cdr searched-variable) 
			             (error "La variable no está en el contexto")))]
			     [(const ,t ,c) t]
			     [(list) 'List]
			     [(begin ,e* ... ,e) (first (append 
			                                  (list (J e context)) 
			                                  (foldl append '() (list (map (lambda (x) (J x context)) e*)))))]
			     [(primapp ,pr ,e* ... ,e0) 
			      (cond
			        [(arit? pr) (if (and (equal? (J e0 context) 'Int) (equal? (first (map (lambda (x) (J x context)) e*)) 'Int))
			                                    'Int
			                                    (error "Los operadores binarios deben tener parámetros de tipo Integer"))]
			        [(lst1? pr) (let ([type-lst-operators (J e0 context)])
			                        (if (c-type? type-lst-operators)
			                            (match pr
			                              ['car (third type-lst-operators)]
			                              ['cdr type-lst-operators]
			                              ['length 'Int])
			                            (error "El tipo no concuerda con el operador de listas")))]
              [(lst2? pr) (let ([type-fst (J e0 context)]
                                [type-snd (J (car e*) context)])
                                (match pr
                                  ['concat 
                                    (if (and (c-type? type-fst) (c-type? type-snd) (equal? type-fst type-snd))
                                          type-fst (error "El tipo no concuerda con el operador de listas"))]
                                  ['equal-lst? 
                                    (if (and (c-type? type-fst) (c-type? type-snd) (equal? type-fst type-snd))
                                          'Bool (error "El tipo no concuerda con el operador de listas"))]
                                  ['elem? 
                                    (if (and (equal? type-fst (third type-snd)) (c-type? type-snd))
                                          'Bool (error "El tipo no concuerda con el operador de listas"))]))])]
			     [(if ,e0 ,e1 ,e2) (let ([t0 (J e0 context)]
			                             [t1 (J e1 context)]
			                             [t2 (J e2 context)])
			                          (if (and (equal? 'Bool (J e0 context)) (unify t1 t2))
			                            t1
			                            (error "Diferentes tipos en cláusulas del if")))]
			     [(while [,e0] ,e1) (if (equal? (J e0 context) 'Bool) 
			     							(J e1 context) 
			     							(error "El tipo no corresponde con el valor"))]
			     [(lambda ([,x ,t]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                      [s (J body new-context)])
			                              		  `(,t → ,s))]
			     [(let ([,x ,t ,e]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                      [t0 (J e context)]
			                                      [s (J body new-context)])
			                                  (if (unify t t0)
			                                    s
			                                    (error "El tipo no corresponde con el valor")))]
			     [(letrec ([,x ,t ,e]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                         [t0 (J e new-context)]
			                                         [s (J body new-context)])
			                                  (if (unify t t0)
			                                    s
			                                    (error "El tipo no corresponde con el valor")))]
			     [(letfun ([,x ,t ,e]) ,body) (let* ([new-context (set-add context (cons x t))]
			                                         [t0 (J e context)]
			                                         [s (J body new-context)])
			                                  (if (and (unify t t0) (equal? (cadr t) '→))
			                                      s
			                                      (error "El tipo no corresponde con el valor")))]
			     [(list ,e* ... ,e) (let* ([types (append (list (J e context))(map (lambda (x) (J x context)) e*))]
			                               [t (part types)]
			                               [eqt (map (lambda (x) (unify t x)) types)])
			                      (if (foldr (lambda (x y) (and x y)) #t eqt)
			                      `(List of ,t)
			                      (error "Las listas degen ser homogéneas")))]
			     [(,e0 ,e1) (let* ([t0 (J e0 context)]
			                       [R (third t0)]
			                       [t1 (J e1 context)])
			                  (if (unify t0 (t1 '→ R))
			                      R
			                      (error "No se puede inferir el tipo. No se puede unificar")))]
			     [else (error "No se pueden inferir los tipos")]))


;; Proceso auxiliar que obtiene el contexto. 
(define (getCtx e)
    (nanopass-case (L9 Expr) e
      [(begin ,e* ... ,e) (append (map (lambda (x) (getCtx x)) e*) (getCtx e))]
      [(if ,e0 ,e1 ,e2) (append (getCtx e0) (getCtx e1) (getCtx e2))]
      [(lambda ([,x ,t]) ,body) (set-add (getCtx body) (cons x t))]
      [(let ([,x ,t ,e]) ,body) (append (set-add (getCtx body) (cons x t)) (getCtx e))]
      [(letrec ([,x ,t ,e]) ,body) (append (set-add (getCtx body) (cons x t)) (getCtx e))]
      [(letfun ([,x ,t ,e]) ,body) (append (set-add (getCtx body) (cons x t)) (getCtx e))]
      [(while [,e0] ,e1) (append (getCtx e0) (getCtx e1))]
      [(,e1 ,e2) (append (getCtx e1) (getCtx e2))]
      [else '()]))

;; Se encarga de quitar las anotaciones de tipo Lambda y de tipo List (de ser necesario). 
(define-pass type-infer : L9 (ir) -> L9 ()
  (definitions)
  (Expr : Expr (ir) -> Expr()
    [(lambda ([,x ,t]) ,[body]) (if (or (equal? t 'List) (equal? t 'Lambda))
                                    `(lambda ([,x ,(J body (getCtx ir))]) ,body) 
                                     ir)]
    [(let ([,x ,t ,[e]]) ,[body]) (if (equal? t 'List)
                                  `(let ([,x ,(J e (getCtx ir)) ,e]) ,body)
                                  ir)]
    [(letrec ([,x ,t ,[e]]) ,[body]) (if (or (equal? t 'List) (equal? t 'Lambda))
                                  `(letrec ([,x ,(J e (getCtx ir)) ,e]) ,body)
                                      ir)]
    [(letfun ([,x ,t ,[e]]) ,[body]) (if (or (equal? t 'List) (equal? t 'Lambda))
                                  `(letfun ([,x ,(J e (getCtx ir)) ,e]) ,body)
                                  ir)]))

(define-pass uncurry : L9 (ir) -> L10 ()
  (definitions
    (define (des-curry espl lst)
      (nanopass-case (L9 Expr) espl
      [(lambda ([,x ,t]) ,body) (des-curry body (append lst (list (cons x t))))]
      [else (values espl lst)])))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,[body]) (let-values ([(e elem) (des-curry ir '())])
                                      (let ([x* (map car elem)]
                                            [e* (map cdr elem)])
                                        `(lambda ([,x* ,e*] ...) ,(parser-L10 (unparse-L9 e)))))]))

(define (tabs n) (make-string n #\tab))

(define (to-python expr level)
  (nanopass-case (L10 Expr) expr
                 [,x
                  (string-append
                   (tabs level)
                   (symbol->string x))]
                 
                 [(const ,t ,c)
                  (string-append
                   (tabs level)
                   (cond [(equal? c #t) "True"]
                         [(equal? c #f) "False"]
                         [(integer? c) (number->string c)]
                         [(char? c) (make-string 1 c)]))]

                 [(begin ,e* ... ,e)
                  (string-append*
                   (let ([et (append e* `(,e))]
                         [f (lambda (x)
                              (string-append
                               (to-python x level)
                               "\n"))])
                     (map f et)))]


                 [(primapp ,pr ,e* ... ,e0)
                  (let ([et (append e* `(,e0))])
                    (if (arit? pr)
                        (string-append
                         (tabs level)
                         (to-python (car et) 0)
                         " "
                         (if (equal? pr 'equal?) ;; :c
                             "=="
                             (symbol->string pr))
                         " "
                         (to-python (cadr et) 0))
                        (string-append
                         (tabs level)
                         (cond [(equal? pr 'length) "len("]
                               [else ""])
                         (to-python (car et) 0)
                         (cond [(equal? pr 'length) ")"]
                               [(equal? pr 'car) "[0]"]
                               [(equal? pr 'cdr) "[1:]"]
                               [(equal? pr 'equal-lst?) " == "]
                               [(equal? pr 'elem?) " in "]
                               [(equal? pr 'concat) " + "]
                               [else ""])
                         (if (memq pr '(equal-lst? elem? concat))
                             (to-python (cadr et) 0)
                             "")
                         )))]
                 
                 [(if ,e0 ,e1 ,e2)
                  (string-append
                   (tabs level)
                   "if "
                   (to-python e0 0)
                   " then:\n"
                   (to-python e1 (+ level 1))
                   "\n"
                   (tabs level)
                   "else:\n"
                   (to-python e2 (+ level 1)))]

                 [(while [,e0] ,e1)
                  (string-append
                   (tabs level)
                   "while "
                   (to-python e0 0)
                   " :\n"
                   (to-python e1 (+ level 1)))]

                 [(let ([,x ,t ,e]) ,body)
                  (string-append
                   (tabs level)
                   (symbol->string x)
                   " = "
                   (to-python e 0)
                   "\n"
                   (to-python body level))]

                 ;; por el momento solo consideramos funciones de una
                 ;; variable porque son las unicas que tienen sentido
                 ;; segun el lenguaje
                 [(letrec ([,x ,t ,e]) ,body)
                  (nanopass-case (L10 Expr) e
                                 [(lambda ([,x2 ,t2]) ,body2)
                                  (string-append
                                   (tabs level)
                                   "def "
                                   (symbol->string x)
                                   "("
                                   (symbol->string x2)
                                   "):\n"
                                   (to-python body2 (+ level 1))
                                   "\n"
                                   (to-python body level)
                                   )])]
                 [(letfun ([,x ,t ,e]) ,body)
                  (nanopass-case (L10 Expr) e
                                 [(lambda ([,x2 ,t2]) ,body2)
                                  (string-append
                                   (tabs level)
                                   "def "
                                   (symbol->string x)
                                   "("
                                   (symbol->string x2)
                                   "):\n"
                                   (to-python body2 (+ level 1))
                                   "\n"
                                   (to-python body level)
                                   )])]
                 
                 [(list ,e* ...)
                  (string-append
                   (tabs level)
                   "["
                   (if (empty? e*)
                       ""
                       (to-python (car e*) 0))
                   (if (empty? e*)
                       ""
                       (string-append*
                        (let ([conv
                               (lambda (x)
                                 (string-append
                                  ", "
                                  (to-python x 0)))])
                          (map conv (cdr e*)))))
                   "]")]
                 
                 [(,e0 ,e1)
                  (string-append
                   (tabs level)
                   (to-python e0 0)
                   "("
                   (to-python e1 0)
                   ")")]
                 ))

;; (define texp
;;   (parser-L10 '(if (const Bool #t) (const Int 3) (const Int 5))))

;; (define texp
;;   (parser-L10
;;    '(let ([x Int (const Int 3)])
;;       (let ([y Int (const Int 4)])
;;         (if (const Bool #t)
;;             x
;;             y)))))

;; (define texp
;;   (parser-L10
;;    '(let ([x Int (const Int 3)])
;;       (let ([y Int (const Int 4)])
;;         (letrec ([selxy Lambda
;;                         (lambda ([z Bool])
;;                           (if z
;;                               (list (const Int 2))
;;                               y))])
;;           (selxy (const Bool #t)))))))

#|(define texp
  (parser-L10
   '(begin
      (primapp + x y)
      (primapp + x (primapp / z (primapp equal? w y)))
      (primapp length (list x y z))
      (primapp car (list x y z w s))
      (primapp cdr (list x y z w s))
      (let ([l1 List (list x y z)])
        (let ([l2 List (list a b c)])
          (begin
            (primapp equal-lst? l1 l2)
            (primapp elem? (const Int 1) l1)
            (primapp concat l1 l2)))))))
(display (to-python texp 0))|#



(define-pass front-end : LF (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [else (verify-vars 
        	   (verify-arity
        	    (un-anonymous
        	     (identify-assigments
        	      (curry-let
        	       (direct-app
        	        (quote-const
        	         (eta-expand
        	          (remove-stupid-operators
        	           (L2-to-NLO
        	            (remove-string
        	             (remove-one-armed-if
        	              (make-explicit ir)))))))))))))]))


(define-pass middle-end : L7 (ir) -> L10 ()
  (Expr : Expr (ir) -> Expr()
        [else (uncurry
               (type-infer
                (type-const
                 (curry ir))))]))


(define (generate-front-end filename)
  (begin
    (define out (open-output-file (string-append (substring filename 0 (- (string-length filename) 3)) ".fe")))
    (for ([line (file->lines filename)])
      (let ([sline (read (open-input-string line))])
        (writeln (unparse-L7 (front-end (parser-LF sline))) out)))
    (close-output-port out)))

(define (generate-middle-end filename)
  (begin
    (define out (open-output-file (string-append filename ".me")))
    (for ([line (file->lines (string-append filename ".fe"))])
      (let ([sline (read (open-input-string line))])
        (writeln (unparse-L10 (middle-end (parser-L7 sline))) out)))
    (close-output-port out)))

(define (generate-back-end filename)
  (begin
    (define out (open-output-file (string-append filename ".py")))
    (for ([line (file->lines (string-append filename ".me"))])
      (let ([sline (read (open-input-string line))])
        (display (to-python (parser-L10 sline) 0) out)))
    (close-output-port out)))

(define (mt-compile filename)
  (begin
  	(define name (substring filename 0 (- (string-length filename) 3)))
    (generate-front-end filename)
    (generate-middle-end name)
    (generate-back-end name)))
