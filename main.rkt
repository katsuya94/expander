#lang racket

(module+ test
  (require rackunit))

(struct scope (id) #:transparent)

(define/contract (make-scope)
  (-> (struct/c scope symbol?))
  (scope (gensym)))

; TODO what are the impacts of including env in syntax object?
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
(define core-forms (set 'lambda 'define-syntax 'quote 'quote-syntax))
(define core-primitives (set 'datum->syntax 'syntax->datum 'syntax 'list 'cons 'car 'cdr 'map))

(for ([sym (in-set (set-union core-forms core-primitives))])
  (add-binding! (syntax sym (set core-scope)) sym))

(define pristine-all-bindings (hash-copy all-bindings))

(define (reset-all-bindings)
  (set! all-bindings (hash-copy pristine-all-bindings)))

(define transformer? (-> datum? datum?))

(define location?
  (or/c 'variable transformer?))

(define env? (hash/c binding? location?))

(define/contract (env-extend env binding location)
  (-> env? binding? location? env?)
  (hash-set env binding location))

(define empty-env (hash))

(define/contract (resolve id)
  (-> identifier? (or/c binding? #f))
  (define candidate-id-counts
    (for/list
      ([candidate-id (in-hash-keys all-bindings)]
       #:when (and (eq? (syntax-datum candidate-id) (syntax-datum id))
                   (subset? (syntax-scopes candidate-id) (syntax-scopes id))))
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

(define/contract (expand datum env)
  (-> datum? env? datum?)
  (cond
    [(identifier? datum)
     (expand-identifier datum env)]
    [((cons/c identifier? (listof datum?)) datum)
     (expand-id-list-form datum env)]
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

(define/contract (expand-id-list-form datum env)
  (-> (cons/c identifier? (listof datum?)) env? datum?)
  (define binding (resolve (car datum)))
  (case binding
    [(quote quote-syntax)
     (expand-quote datum env)]
    [(lambda)
     (expand-lambda datum env)]
    [(define-syntax)
     (error "define-syntax in expression context:" datum)]
    [else
     (define location (env-lookup env binding))
     (if (procedure? location)
       (expand (apply-transformer datum location) env)
       (expand-application-form datum env))]))

(define/contract (expand-quote datum env)
  (-> (list/c identifier? datum?) env? datum?)
  (match-define `(,quote-id ,arg) datum)
  `(,quote-id ,arg))

(define/contract (expand-lambda datum env)
  (-> (cons/c identifier? (cons/c (list/c identifier?) (listof datum?))) env? datum?)
  (match-define `(,lambda-id (,formal) ,@body) datum)
  (define s (make-scope))
  (define binding-id (add-scope formal s))
  (define binding (add-local-binding! binding-id))
  (define bound-body (map (lambda (d) (add-scope d s)) body))
  (define extended-env (env-extend env binding 'variable))
  (define expanded-body (expand-body bound-body extended-env))
  `(,lambda-id (,binding-id) ,@expanded-body))

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
  (-> (listof datum?) env? (listof datum?))
  (define rest data)
  (define (define-syntax-form? datum)
    (and
      (pair? datum)
      (identifier? (car datum))
      (eq? (resolve (car datum)) 'define-syntax)))
  (for ([datum (in-list data)])
    ; TODO this doesn't handle the case that something expands to a define-syntax form
    #:break (not (define-syntax-form? datum))
    (set! rest (cdr rest))
    (define-values (s binding transformer) (expand-define-syntax datum))
    (set! rest (map (lambda (d) (add-scope d s)) rest))
    (set! env (env-extend env binding transformer)))
  (map (lambda (d) (expand d env)) rest))

(define/contract (expand-define-syntax datum)
  (-> (list/c identifier? identifier? datum?) (values scope? binding? transformer?))
  (match-define `(,define-syntax-id ,id ,transformer) datum)
  ; TODO: one major difference is new scopes are introduced for every binding, not just macro uses. what are the implications of this?
  (define s (make-scope))
  (define binding-id (add-scope id s))
  (define binding (add-local-binding! binding-id))
  ; TODO: should the transformer expression be in the bound region of the keyword?
  (define transformer-value (eval-compiled (compile (expand transformer empty-env))))
  (values s binding transformer-value))

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
       [else
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
      '((lambda (_)
          (define-syntax macro
            (lambda (stx) (quote-syntax (quote 4))))
          (macro))
        '#f))
    4)

  (define (with-let . body)
    `((lambda (_)
        (define-syntax let
          (lambda (stx)
            (list
              (cons
                (quote-syntax lambda)
                (cons
                  (list (car (car (cdr stx))))
                  (cdr (cdr stx))))
              (car (cdr (car (cdr stx)))))))
        ,@body)
      '#f))

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
    'foo))
