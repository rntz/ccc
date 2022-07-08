#lang racket

(require (prefix-in racket: racket))
(require syntax/parse/define)

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])

(define-signature cat^ (identity compose))
(define-signature products^ (pi1 pi2 pair into-terminal))
(define-signature sums^ (in1 in2 split from-initial))
(define-signature exponentials^ (eval transpose))

(define-signature contexts^
  (context-empty  ;; ctx
   context-get    ;; ctx, sym -> Γ → A
   context-extend ;; ctx, sym -> ctx, (Γ × A → Γ,A)
   ))

(define-unit racket@
  (import)
  (export cat^ products^ sums^ exponentials^)
  (define identity racket:identity)
  (define compose racket:compose1)
  (define pi1 car)
  (define pi2 cdr)
  (define ((pair f g) x) (cons (f x) (g x)))
  (define (into-terminal x) '())
  (define (in1 x) `(left ,x))
  (define (in2 x) `(rght ,x))
  (define ((split f g) x)
    (match x [`(left ,y) (f y)] [`(rght ,y) (g y)]))
  (define (from-initial _) (error "impossible"))
  (define (eval x) ((car x) (cdr x)))
  (define (((transpose f) a) b) (f (cons a b)))
  )

(define-unit products->contexts@
  (import cat^ products^)
  (export contexts^)
  (define context-empty '())
  (define (context-get ctx sym)
    (match ctx
      ['() (error "unbound symbol")]
      [(cons (== sym) _) pi2]
      [(cons _ xs) (compose pi1 (context-get xs sym))]))
  (define (context-extend ctx sym)
    (values (cons sym ctx) identity)))

(define-compound-unit/infer racket+contexts@
  (import)
  ;; ugh, look at all this boilerplate.
  (export cat^ products^ sums^ exponentials^ contexts^)
  (link racket@ products->contexts@))


;; ---------- SIMPLY TYPED λ-CALCULUS ----------
(define-signature stlc^
  (var     ;; x -> (Γ → A)      where x:A ∈ Γ
   lam     ;; x, (Γ,x:A → B) -> (Γ → A => B)
   app     ;; (Γ → A => B), (Γ → A) -> (Γ → B)
   project ;; i, n, (Γ → Πᵢⁿ Aᵢ) -> (Γ → Aᵢ)
   tuple   ;; (Γ → Aᵢ)ᵢⁿ -> (Γ → Πᵢⁿ Aᵢ)
   ))

(define-signature cat->stlc^ extends stlc^ (finalize))
(define-unit cat->stlc@
  (import cat^ contexts^ products^ (prefix exp: exponentials^))
  (export cat->stlc^)
  ;; our Γ → A is represented as (ctx -> (Γ → A))
  (define (finalize f) ((f context-empty) 'ignored))
  (define ((var name) ctx) (context-get ctx name))
  (define ((app e1 e2) ctx) (compose (pair (e1 ctx) (e2 ctx)) exp:eval))
  (define ((lam x e) ctx)
    (define-values (e-ctx extend-morph) (context-extend ctx x))
    ;; exp:transpose : (Γ × A → B) -> (Γ → A => B)
    (exp:transpose (compose (e e-ctx) extend-morph)))
  (define ((project i n e) ctx)
    (match n
      [1 (e ctx)]
      [2 (compose (match i [0 pi1] [1 pi2]) (e ctx))]
      [_ TODO]))
  (define ((tuple . es) ctx)
    (match es
      [`() into-terminal]
      [`(,e) (e ctx)]
      [`(,e1 ,e2) (pair (e1 ctx) (e2 ctx))]
      [_ TODO])))

(define-compound-unit/infer racket-stlc@
  (import)
  (export cat->stlc^)
  (link racket+contexts@ cat->stlc@))


(module+ test
  (require rackunit)
  (define-values/invoke-unit/infer racket-stlc@)
  (check-eqv? 2 ((finalize (lam 'x (var 'x))) 2))
  (check-eqv? 0 ((finalize (lam 'x (project 0 2 (var 'x)))) '(0 . 1)))
  (check-equal? '(0 . 0)
                ((finalize (lam 'x (tuple (var 'x) (var 'x)))) '0))
  )
