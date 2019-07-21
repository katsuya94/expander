#lang racket

(module+ test
  (require rackunit))

(struct scope (id) #:transparent)

(define/contract (make-scope)
  (-> (struct/c scope symbol?))
  (scope (gensym)))

(struct syntax (datum scopes) #:transparent)

(define identifier? (struct/c syntax symbol? (set/c scope?)))

(define literal?
  (or/c
    integer?
    boolean?))

(define (input? v)
  (or
    (literal? v)
    (symbol? v)
    ((listof input?) v)))

(define (datum? v)
  (or
    (literal? v)
    (identifier? v)
    ((listof datum?) v)))

(define (extended-datum? v)
  (or
    (void? v)
    (literal? v)
    (symbol? v)
    (procedure? v) ; more specifically (-> extended-datum? extended->datum?)
    (identifier? v)
    (null? v)
    ((cons/c extended-datum? extended-datum?) v)))

(define (output? v)
  (or
    ((list/c 'quote extended-datum?) v)
    (symbol? v)
    ((listof output?) v)))

(define-syntax datum-case
  (syntax-rules (literal? identifier? listof datum?)
    [(datum-case datum
       [literal? literal-body ...]
       [identifier? identifier-body ...]
       [(listof datum?) listof-datum-body ...])
     (cond
       [(literal? datum) literal-body ...]
       [(identifier? datum) identifier-body ...]
       [((listof datum?) datum) listof-datum-body ...]
       [else (error "unexpected datum:" datum)])]))

(define/contract (datum->syntax input)
  (-> input? datum?)
  (cond
    [(literal? input) input]
    [(symbol? input) (syntax input (set))]
    [((listof input?) input) (map datum->syntax input)]
    [else (error "unexpected input:" input)]))

(module+ test
  (check-equal? (datum->syntax 'id) (syntax 'id (set))))

(define/contract (syntax->datum syntax)
  (-> datum? input?)
  (datum-case syntax
    [literal? syntax]
    [identifier? (syntax-datum syntax)]
    [(listof datum?) (map syntax->datum syntax)]))

(define/contract (adjust-scope datum scope proc)
  (-> datum? scope? (-> (set/c scope?) scope? (set/c scope?)) datum?)
  (datum-case datum
    [literal? datum]
    [identifier? datum
     (syntax (syntax-datum datum) (proc (syntax-scopes datum) scope))]
    [(listof datum?)
     (map (lambda (d) (adjust-scope d scope proc)) datum)]))

(define/contract (add-scope datum scope)
  (-> datum? scope? datum?)
  (adjust-scope datum scope set-add))

(define/contract (map-scope data scope)
  (-> (listof datum?) scope? (listof datum?))
  (map (lambda (d) (add-scope d scope)) data))

(define/contract (flip-scope datum scope)
  (-> datum? scope? datum?)
  (adjust-scope datum scope set-flip))

(define/contract (set-flip scopes scope)
  (-> (set/c scope?) scope? (set/c scope?))
  (if (set-member? scopes scope)
    (set-remove scopes scope)
    (set-add scopes scope)))

(module+ test
  (define scope/a (make-scope))
  (check-equal? (add-scope (syntax 'id (set)) scope/a) (syntax 'id (set scope/a))))

(define/contract (introduce datum)
  (-> datum? datum?)
  (add-scope datum core-scope))

(module+ test
  (check-equal? (introduce (syntax 'id (set)) ) (syntax 'id (set core-scope))))

(module+ test
  (check-equal? (syntax->datum (syntax 'id (set))) 'id))

(define binding? symbol?)
(define all-bindings (make-hash))

(define/contract (add-binding! id binding)
  (-> identifier? binding? void?)
  (hash-set! all-bindings id binding))

(define/contract (add-local-binding! id)
  (-> identifier? binding?)
  (define binding (gensym (syntax-datum id)))
  (add-binding! id binding)
  binding)

(module+ test
  (add-binding! (syntax 'id (set)) 'binding)
  (check-equal? (hash-ref all-bindings (syntax 'id (set))) 'binding))

(define core-scope (make-scope))
(define core-forms (set 'lambda 'begin 'define 'define-syntax 'module 'import 'quote 'quote-syntax))
(define core-primitives (set 'datum->syntax 'syntax->datum 'syntax 'if 'list 'cons 'car 'cdr 'map 'null? 'set! 'void))

(for ([sym (in-set (set-union core-forms core-primitives))])
  (add-binding! (syntax sym (set core-scope)) sym))

(define pristine-all-bindings (hash-copy all-bindings))

(define (reset-all-bindings)
  (set! all-bindings (hash-copy pristine-all-bindings)))

(define transformer? (-> datum? datum?))

(define interface? (set/c scope?))

(define location?
  (or/c 'variable transformer? interface?))

(define env? (hash/c binding? location?))

(define/contract (env-extend env binding location)
  (-> env? binding? location? env?)
  (hash-set env binding location))

(define empty-env (hash))

(define/contract (binds? binding-id id)
  (-> identifier? identifier? boolean?)
  (and (eq? (syntax-datum binding-id) (syntax-datum id))
       (subset? (syntax-scopes binding-id) (syntax-scopes id))))

(define/contract (resolve id)
  (-> identifier? (or/c binding? #f))
  (define candidate-id-counts
    (for/list
      ([candidate-id (in-hash-keys all-bindings)]
       #:when (binds? candidate-id id))
      (cons candidate-id (set-count (syntax-scopes candidate-id)))))
  (cond
    [(empty? candidate-id-counts)
     #f]
    [else
     (define max-id-count (argmax cdr candidate-id-counts))
     (define max-id (car max-id-count))
     (define max-count (cdr max-id-count))
     (when (> (count (lambda (n) (= n max-count)) (map cdr candidate-id-counts)) 1)
       (error "ambiguous:" id))
     (hash-ref all-bindings max-id)]))

(define/contract (env-lookup env binding)
  (-> env? binding? (or/c location? #f))
  (hash-ref env binding #f))

(define/contract (expand datum env [body #f])
  (->* (datum? env?) (boolean?) datum?)
  (cond
    [(identifier? datum)
     (expand-identifier datum env)]
    [((cons/c identifier? (listof datum?)) datum)
     (expand-id-list-form datum env body)]
    [((listof datum?) datum)
     (expand-application-form datum env)]
    [else (error "bad syntax:" datum)]))

(define/contract (expand-identifier id env)
  (-> identifier? env? datum?)
  (define binding (resolve id))
  (cond
    [(not binding)
     (error "free variable:" id)]
    [(set-member? core-primitives binding)
     id]
    [(set-member? core-forms binding)
     (error "bad syntax: unexpected core form in expression context:" id)]
    [else
     (define location (env-lookup env binding))
     (cond
       [(not location)
        (error "out of context:" id)]
       [(eq? location 'variable)
        id]
       [else
        (error "bad syntax:" id)])]))

(define/contract (expand-id-list-form datum env [body #f])
  (->* ((cons/c identifier? (listof datum?)) env?) (boolean?) datum?)
  (define binding (resolve (car datum)))
  (case binding
    [(quote)
     (expand-quote datum env)]
    [(quote-syntax)
     (expand-quote-syntax datum env)]
    [(lambda)
     (expand-lambda datum env)]
    [(begin)
     (if body datum (expand-begin datum env))]
    [(define)
     (unless body
       (error "define in expression context:" datum))
     datum]
    [(define-syntax)
     (unless body
       (error "define-syntax in expression context:" datum))
     datum]
    [(module)
     (unless body
       (error "module in expression context:" datum))
     datum]
    [(import)
     (unless body
       (error "import in expression context:" datum))
     datum]
    [else
     (define location (and binding (env-lookup env binding)))
     (if (procedure? location)
       (expand (apply-transformer datum location) env body)
       (expand-application-form datum env))]))

(define/contract (expand-quote datum env)
  (-> (list/c identifier? datum?) env? datum?)
  (match-define `(,quote-id ,arg) datum)
  `(,quote-id ,arg))

(define/contract (expand-quote-syntax datum env)
  (-> (list/c identifier? datum?) env? datum?)
  (match-define `(,quote-syntax-id ,arg) datum)
  `(,quote-syntax-id ,arg))

(define/contract (expand-lambda datum env)
  (-> (cons/c identifier? (cons/c (list/c identifier?) (listof datum?))) env? datum?)
  (match-define `(,lambda-id (,formal) ,@body) datum)
  (define s (make-scope))
  (define binding-id (add-scope formal s))
  (define binding (add-local-binding! binding-id))
  (define bound-body (map (lambda (d) (add-scope d s)) body))
  (define extended-env (env-extend env binding 'variable))
  (define expanded-body (expand-body bound-body extended-env))
  `(,lambda-id (,binding-id) ,expanded-body))

(define/contract (expand-begin datum env)
  (-> (cons/c identifier? (listof datum?)) env? datum?)
  (match-define `(,begin-id ,@body) datum)
  (define expanded-body (expand-body body env))
  `(,begin-id ,expanded-body))

(define/contract (apply-transformer datum transformer)
  (-> datum? transformer? datum?)
  (define s (make-scope))
  (define bound-datum (add-scope datum s))
  (define transformed-datum (transformer bound-datum))
  (flip-scope transformed-datum s))

(define/contract (expand-application-form datum env)
  (-> (listof datum?) env? datum?)
  (map (lambda (d) (expand d env)) datum))

(define/contract (expand-body data env)
  (-> (listof datum?) env?  datum?)
  (define-values (body-forms extended-env definition-ids _) (process-body data env '() '() (hash)))
  (define expanded-body-forms (map (lambda (d) (expand d extended-env)) body-forms))
  (define expanded `(,(syntax 'begin (set core-scope)) ,@expanded-body-forms))
  (for ([id (in-list definition-ids)])
    (set! expanded
      `((,(syntax 'lambda (set core-scope)) (,id) ,expanded)
        (,(syntax 'void (set core-scope))))))
  expanded)

(define/contract (process-body data env definition-ids pre-forms id-scopes)
  (-> (listof datum?) env? (listof identifier?) (listof datum?) (hash/c identifier? scope?)
      (values (listof datum?) env? (listof identifier?) (hash/c identifier? scope?)))
  (define expanded 
    (and (pair? data)
         (with-handlers ([exn:fail? (lambda (exn) #f)]) ; ugly hack in lieu of partial expansion
           (expand (car data) env #t))))
  (define id (and expanded (pair? expanded) (identifier? (car expanded)) (car expanded)))
  (define id-binding (and id (resolve id)))
  (case id-binding
    [(begin)
     (define forms (process-begin expanded))
     (process-body
       (append forms (cdr data))
       env
       definition-ids
       pre-forms
       id-scopes)]
    [(define)
     (define-values (s extended-env id set-form) (process-define expanded env))
     (process-body
       (map-scope (cdr data) s)
       extended-env
       (map-scope (append definition-ids (list id)) s)
       (map-scope (append pre-forms (list set-form)) s)
       (hash-set id-scopes id s))]
    [(define-syntax)
     (define-values (s extended-env id) (process-define-syntax expanded env))
     (process-body
       (map-scope (cdr data) s)
       extended-env
       (map-scope definition-ids s)
       (map-scope pre-forms s)
       (hash-set id-scopes id s))]
    [(module)
     (define-values (s extended-env id module-body-forms module-definition-ids) (process-module expanded env))
     (process-body
       (map-scope (cdr data) s)
       extended-env
       (map-scope (append definition-ids module-definition-ids) s)
       (map-scope (append pre-forms module-body-forms) s)
       (hash-set id-scopes id s))]
    [(import)
     (define interface (process-import expanded env))
     (define scopes (set->list interface))
     (process-body
       (foldl (lambda (s ds) (map-scope ds s)) (cdr data) scopes)
       env
       (foldl (lambda (s ds) (map-scope ds s)) definition-ids scopes)
       (foldl (lambda (s ds) (map-scope ds s)) pre-forms scopes)
       id-scopes)]
    [else
     (values `(,@pre-forms ,@data) env definition-ids id-scopes)]))

(define/contract (process-begin datum)
  (-> (cons/c identifier? (listof datum?)) (listof datum?))
  (match-define `(,begin-id ,@body) datum)
  body)

(define/contract (process-define datum env)
  (-> (list/c identifier? identifier? datum?) env?
      (values scope? env? identifier? datum?))
  (match-define `(,define-id ,id ,rhs) datum)
  (define s (make-scope))
  (define binding-id (add-scope id s))
  (define binding (add-local-binding! binding-id))
  (define extended-env (env-extend env binding 'variable))
  (define set-form `(,(syntax 'set! (set core-scope)) ,id ,rhs))
  (values s extended-env binding-id set-form))

(define/contract (process-define-syntax datum env)
  (-> (list/c identifier? identifier? datum?) env?
      (values scope? env? identifier?))
  (match-define `(,define-syntax-id ,id ,transformer) datum)
  (define s (make-scope))
  (define binding-id (add-scope id s))
  (define binding (add-local-binding! binding-id))
  (define bound-transformer (add-scope transformer s))
  (define transformer-value (eval-compiled (compile (expand bound-transformer empty-env))))
  (define extended-env (env-extend env binding transformer-value))
  (values s extended-env binding-id))

(define/contract (process-module datum env)
  (-> (cons/c identifier? (cons/c identifier? (cons/c (listof identifier?) (listof datum?)))) env?
      (values scope? env? identifier? (listof datum?) (listof identifier?)))
  (match-define `(,module-id ,id (,@export-ids) ,@body) datum)
  (define s (make-scope))
  (define binding-id (add-scope id s))
  (define binding (add-local-binding! binding-id))
  (define bound-body (map-scope body s))
  (define-values (body-forms extended-env definition-ids id-scopes) (process-body bound-body env '() '() (hash)))
  (define interface
    (list->set
      (for/list ([export-id (in-list export-ids)])
	(for/first ([id+scope (in-hash-pairs id-scopes)]
	            #:when (binds? export-id (car id+scope)))
	  (cdr id+scope)))))
  (set! extended-env (env-extend extended-env binding interface))
  (values s extended-env binding-id body-forms definition-ids))

(define/contract (process-import datum env)
  (-> (list/c identifier? identifier?) env? interface?)
  (match-define `(,import-id ,id) datum)
  (define binding (resolve id))
  (define interface (env-lookup env binding))
  interface)

(module+ test
  (define binding/a (gensym))
  (add-binding! (syntax 'id (set core-scope)) binding/a)
  (check-equal? (expand (syntax 'id (set core-scope)) (hash binding/a 'variable)) (syntax 'id (set core-scope))))

(define/contract (compile datum)
  (-> datum? output?)
  (cond
    [(pair? datum)
     (define car-binding (and (identifier? (car datum)) (resolve (car datum))))
     (case car-binding
       [(quote)
        (match-define `(,quote-id ,quote-datum) datum)
        `(quote ,(syntax->datum quote-datum))]
       [(quote-syntax)
        (match-define `(,quote-syntax-id ,quote-syntax-datum) datum)
        `(quote ,quote-syntax-datum)]
       [(lambda)
        (match-define `(,lambda-id (,id) ,@body) datum)
        `(lambda (,(resolve id)) ,@(map compile body))]
       [(begin)
        (match-define `(,begin-id ,@body) datum)
        `(begin ,@(map compile body))]
       [else
        (when (set-member? core-forms car-binding)
          (error "unexpected core form after expansion:" datum))
        (map compile datum)])]
    [(identifier? datum)
     (define binding (resolve datum))
     (when (not binding)
       (error "free variable after expansion:" datum))
     binding]
    [else
     (error "bad syntax after expansion:" datum)]))

(module+ test
  (define binding/b (gensym))
  (add-binding! (syntax 'id (set core-scope)) binding/b)
  (check-equal? (compile (expand (syntax 'id (set core-scope)) (hash binding/b 'variable))) binding/b))

(define namespace (make-base-namespace))

(define/contract (eval-compiled output)
  (-> output? extended-datum?)
  (eval output namespace))

(define/contract (run input)
  (-> input? extended-datum?)
  (reset-all-bindings)
  (define expanded (expand (introduce (datum->syntax input)) empty-env))
  (define compiled (compile expanded))
  (eval-compiled compiled))

(module+ test
  (check-equal? (run ''4) 4)
  (check-equal? (run ''sym) 'sym)
  (check-equal? (run '((lambda (_) '4) '#f)) 4)
  (check-equal? (run '((lambda (_) '4 '6) '#f)) 6)

  (check-equal?
    (run
      '(begin
         (define-syntax macro
           (lambda (stx) (quote-syntax (quote 4))))
         (macro)))
    4)

  (define (with-let . body)
    `(begin
        (define-syntax let
          (lambda (stx)
            (list
              (cons
                (quote-syntax lambda)
                (cons
                  (list (car (car (cdr stx))))
                  (cdr (cdr stx))))
              (car (cdr (car (cdr stx)))))))
        ,@body))

  (check-equal?
    (run
      (with-let
        '(let (x '4) x)))
    4)

  (check-equal?
    (run
      (with-let
        '(let (x 'foo) (cons x 'bar))))
    '(foo . bar))

  (check-exn
    exn:fail?
    (lambda ()
      (run
	(with-let
	  '(begin
	     (define-syntax macro
	       (lambda (stx) (quote-syntax x)))
	     (let (x 'foo)
	       (macro))))))
    "free variable:")

  (check-equal?
    (run
      (with-let
        '(let (x 'foo)
           (define-syntax with-x
             (lambda (stx)
               (cons
                 (quote-syntax let)
                 (cons
                   (quote-syntax (x 'bar))
                   (cdr stx)))))
           (with-x x))))
    'foo)

  (check-equal?
    (run
      (with-let
	'(let (x 'foo)
	   (define-syntax other-x
	     (lambda (stx)
	       (quote-syntax x)))
	   (let (x 'bar)
	     (other-x)))))
    'foo)

  (check-equal?
    (run
      (with-let
        '(let (x 'bar)
           (define x 'foo)
           x)))
    'foo)

  (check-equal?
    (run
      (with-let
        '(let (x '(foo bar baz))
           (define last
             (lambda (l)
               (if (null? (cdr l))
                 (car l)
                 (last (cdr l)))))
           (last x))))
    'baz)

  (check-equal?
    (run
      '(begin
         (begin
           (define x 'foo))
         x))
    'foo)

  (check-equal?
    (run
      '(begin
         (define x 'foo)
         (module A (x)
           (define x 'bar))
         x))
    'foo)

  (check-equal?
    (run
      '(begin
         (define x 'foo)
         (module A ()
           (set! x (cons 'bar x)))
         x))
    '(bar . foo))

  (check-equal?
    (run
      '(begin
         (module A ()
           (set! x (cons 'bar x)))
         (define x (cons 'foo x))
         x))
    `(foo bar . ,(void)))

  (check-equal?
    (run
      '(begin
         (module A (x)
           (define x 'foo))
	 (import A)
         x))
    'foo)
  
  (check-equal?
    (run
      '(begin
	 (module A (x)
	   (define x 'foo))
	 (define x 'bar)
	 (cons x (begin (import A) x))))
    '(bar . foo)))
