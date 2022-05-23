#lang racket

(require syntax/parse/define)

;; steps:
;; 1. defining the category structure
;; 2. typechecking/elaborating into morphisms

;; # TODO #
;;
;; 0. a list of test programs I'd like to write
;; 1. practical features that I can use to write test programs
;; 2. more "features": Incremental, AutoDiff
;; 3. more backends, eg: JS, WASM
;;
;; # LANG FEATURES #
;;
;; modal types (graded?!)
;; info flow types
;; finite sets, set comprehensions -> Datafun
;;
;; # IMPL FEATURES #
;;
;; incremental computation
;; automatic differentiation
;;
;; # BACKENDS #
;;
;; Quoted Racket code
;; Javascript
;; WASM???
;;
;; # EXAMPLE PROGRAMS #
;;
;; AD: simple formulae for trig stuff
;; Datafun: simple conjunctive queries, transitive closure


;;; ---------- CATEGORICAL STRUCTURE ----------

;; a category maps names to generic morphisms or operations on morphisms.
(define category/c (hash/c symbol? any/c #:flat? #t))

;; instead of using a parameter to pass this around I should maybe use
;; parameterized modules or just a function.
(define/contract the-cat (parameter/c category/c) (make-parameter #f))

;; The category of single-argument racket functions. I use (A -> B) for
;; meta-level functions, (A → B) for morphisms, and (A => B) for exponential
;; objects.
(define/contract racket-cat category/c
  (hash
   'id (lambda (x) x)
   'compose (lambda (f g) (lambda (x) (f (g x))))
   ;; terminal object
   'ignore (lambda (x) '())
   ;; pairs
   'pi1 car 'pi2 cdr
   'pair (lambda (f g) (lambda (x) (cons (f x) (g x))))
   ;; binary sums
   'inl (lambda (x) (cons 'inl x))
   'inr (lambda (x) (cons 'inr x))
   'case2 (lambda (f g) (match-lambda
                     [`(inl ,x) (f x)]
                     [`(inr ,x) (g x)]))
   ;; exponentials
   ;; lambda: (Γ x A → B) -> (Γ → (A => B))
   'lambda (lambda (f)     ;; meta-level
             (lambda (env) ;; morphism
               (lambda (a) ;; exponential
                 (f (cons env a)))))
   ;; apply: (A => B) × A → B
   'apply (match-lambda [(cons f x) (f x)])
   ))

;; morphisms are expressions for single-argument functions
(define/contract racket-expr-cat category/c
  (hash
   ;; 'id '(lambda (x) x)
   ;; 'compose (lambda (f g) `(lambda (x) (,f (,g x))))
   'id 'identity
   'compose (lambda (f g) `(compose1 ,f ,g))
   'into-terminal `(lambda (x) '())
   'pi1 'car 'pi2 'cdr
   'pair (lambda (f g) `(lambda (x) (cons (,f x) (,g x))))
   ;; lambda: (Γ x A → B) -> (Γ → (A => B))
   'lambda (lambda (f) `(lambda (env) (lambda (x) (,f (cons env x)))))
   ;; apply: (A => B) × A → B
   'apply `(lambda (x) ((car x) (cdr x)))
   ))

;; morphisms are syntax transformers.
;; TODO: use (make-syntax-introducer) here for hygiene
(define/contract racket-syntax-cat category/c
  (hash
   'id      identity
   'compose compose1
   'into-terminal (const '())
   'pi1 (lambda (e) `(car ,e))
   'pi2 (lambda (e) `(cdr ,e))
   'pair (lambda (f g) (lambda (e) `(cons ,(f e) ,(g e))))
   ;; lambda: (Γ x A → B) -> (Γ → (A => B))
   'lambda (lambda (f)
             (lambda (e)
               (let ((env (gensym 'env)) (x (gensym 'x)))
                 `(lambda (,env) (lambda (,x) ,(f `(cons ,env ,x)))))))
   ;; apply: (A => B) × A → B
   'apply (lambda (e) `(let ((tmp ,e)) ((car tmp) (cdr tmp))))
   ))


;;; Categorical operators.
(define-syntax-rule (cat x) (hash-ref (the-cat) 'x))

(define (id) (cat id))
(define/match (compose . fs)
  [('()) (cat id)]
  [((cons f fs))
   (let ([compose (cat compose)])
     (for/fold ([f f]) ([g fs])
       (compose f g)))])
(define (pipe . fs) (apply compose (reverse fs)))

(define (into-terminal) (cat into-terminal))
(define (pi1) (cat pi1))
(define (pi2) (cat pi2))
(define (pair f g) ((cat pair) f g))
(define (cat-lambda f) ((cat lambda) f))
(define (cat-apply) (cat apply))


;; ---------- CONTEXTS ----------
;; TODO: Make n-ary products into a categorical structure instead of
;; just using binary products.

;; A ctx represents a map from frontend variables to types or other info, and a
;; backend tuple type with one entry per variable.
;;
;; Currently the context Γ,B,A becomes the type ((Γ × B) × A).
;; We use an alist to represent the key-value mapping.

(define context? list?)

;; context-empty  : ctx
;; context-extend : ctx, key, value --> ctx, (Γ × A → Γ,A)
;; context-get : ctx, key --> value, (Γ → A)
(define (context-empty) '())

(define (context-extend c k v)
  (values (cons (cons k v) c) (id)))

(define (context-get c k)
  (match c
    ['() (error "no matching variable")]
    [`((,(== k) . ,v) . ,_) (values v (pi2))]
    [(cons _ xs)
     (let-values ([(val proj) (context-get xs k)])
       (values val (pipe (pi1) proj)))]))


;;; ---------- FRONTEND / TYPECHECKER ----------
;; Syntax:
;; (isa type term)      -- type ascription
;; (let ([x term] ...) term)
;; (cons term ...)      -- makes a tuple; can be empty, (cons)
;; (pi n term)          -- tuple projection, n must be literal >= 1
;; (lambda (x ...) term)     -- curried lambda
;; (term term ...)      -- curried application
;; x                    -- variable

(define morphism? any/c) ; fixme
(define term? any/c) ; fixme
(define type?
  (flat-rec-contract type?
   (cons/c '* (listof type?))
   (list/c '-> type? type?)
   ;; base types
   symbol?))

(define subtype? equal?)

(define/contract the-context
  (parameter/c context?)
  (make-parameter (context-empty)))

;; synth : term --> type morph
;; check : type term --> morph
;; elab  : type? term --> type morph
(define (synth term) (elab #f term))
(define (check type term) (let-values ([(_ morph) (elab type term)]) morph))

(define/contract (elab expected term)
  (-> (or/c type? #f) term? (values type? morphism?))
  (define (inferred got morph)
    (when (and expected (not (subtype? got expected)))
      (error 'elab "Type error, got ~a but wanted ~a" got expected))
    (values got morph))
  #;(define (checked morph) (values expected morph))
  (define-syntax-rule (expecting pat body ...)
    (values expected (match-let ([pat expected]) body ...)))

  (match term
    [(? symbol? x)
     (define-values (xt xproj) (context-get (the-context) x))
     (inferred xt xproj)]
    [`(isa ,A ,e) (inferred A (check A e))]
    ;; TODO: let-binding
    ;; TODO: n-ary tuples.
    [`(cons) (inferred '(*) (into-terminal))]
    [`(cons ,x ,y)
     ;; TODO: synthesis for tuples
     (expecting `(* ,A ,B) (pair (check A x) (check B y)))]
    [`(pi ,n ,x) #:when (<= 1 n 2)
     (match-define-values (`(* ,A ,B) xm) (synth x))
     (define-values (tp proj)
       (match n [1 (values A (pi1))] [2 (values B (pi2))]))
     (inferred tp (compose proj xm))]
    ;; functions & application
    ;; TODO: curried/multi-argument function syntax
    [`(lambda (,x) ,e)
     (expecting `(-> ,A ,B)
      (define-values (newctx extend-morph) (context-extend (the-context) x A))
      (cat-lambda ;; (Γ x A → B) -> (Γ → A => B)
       (pipe
        extend-morph ; Γ x A → Γ,A
        ;; Γ,A → B
        (parameterize ([the-context newctx]) (check B e)))))]
    [`(,e1 ,e2)
     (match-define-values (`(-> ,A ,B) e1m) (synth e1))
     (define e2m (check A e2))
     (inferred B (pipe (pair e1m e2m) (cat-apply)))]))


;; Tests
(require racket/trace)
#;(trace elab #;context-get #;context-extend)

(module+ examples
  (provide (all-defined-out))
  (the-cat racket-syntax-cat)

  (define id-type '(-> a a))
  (define id-stx '(lambda (x) x))
  (define (id-morph) (check id-type id-stx))

  (define const-type '(-> a (-> b a)))
  (define const-stx '(lambda (x) (lambda (y) x)))
  (define (const-morph) (check const-type const-stx))

  (define flip-type '(-> (-> a (-> b c)) (-> b (-> a c))))
  (define flip-stx '(lambda (f) (lambda (b) (lambda (a) ((f a) b)))))
  (define (flip-morph) (check flip-type flip-stx))
  (define constid-stx
    `((isa (-> (-> a (-> b a)) (-> b (-> a a))) ,flip-stx)
      (lambda (a) (lambda (b) a))))
  (define (constid-morph) (check '(-> b (-> a a)) constid-stx))
  )

(module+ test
  (require (rename-in rackunit (check ru:check))
           racket/splicing)
  (require (submod ".." examples))
  (the-cat racket-cat)

  ;; id-morph: ∅ → (a => a)
  (check-equal? "lol" (((id-morph) '()) "lol"))
  (check-equal? '(b a) (((((flip-morph) '()) (lambda (x) (lambda (y) (list x y)))) 'a) 'b))

  ;; flip const == const id
  (check-equal? 'produced ((((constid-morph) '()) 'ignored) 'produced))
  )
