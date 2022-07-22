#lang racket

(require (prefix-in racket: racket))
(require syntax/parse/define)

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])

(define (reverse-compose1 . procs) (apply compose1 (reverse procs)))

(define-signature cat^
  (nop ;; A → A
   seq ;; A → B, B → C, ..., Y → Z -> A → Z
   (define-values (after) (lambda xs (apply seq (reverse xs))))))
(define-signature products^ (pi1 pi2 pair into-terminal))
(define-signature sums^ (in1 in2 split from-initial))
(define-signature exponentials^ (eval transpose))

(define-signature contexts^
  (context-empty  ;; ctx
   context-get    ;; ctx, sym -> Γ → A
   context-extend ;; ctx, sym -> ctx, (Γ × A → Γ,A)
   ))

;; cartesian concategory stuff
(define-signature cartesian^ extends cat^
  (parallel ;; Γ₁ → Δ₁, ..., Γₙ → Δₙ -> (Γ₁ ... Γₙ → Δ₁ ... Δₙ)
   ;permute  ;; π:permutation -> Γ → π(Γ)
   rename   ;; ρ:renaming -> ρ(Γ) → Γ
   merge ;; n -> A₁, ..., Aₙ → A₁ ⊗ ... ⊗ Aₙ
   split ;; n -> A₁ ⊗ ... ⊗ Aₙ → A₁, ..., Aₙ
   ;; ;; swap: A ⊗ B → B ⊗ A
   ;; (define-values (swap) (seq (split 2) (rename 1 0) (merge 2)))
   ))

(define-unit racket@
  (import)
  (export cat^ products^ sums^ exponentials^ contexts^)
  (define nop racket:identity)
  (define seq reverse-compose1)

  (define pi1 car)
  (define pi2 cdr)
  (define ((pair f g) x) (cons (f x) (g x)))
  (define (into-terminal x) '())
  (define (in1 x) `(left ,x))
  (define (in2 x) `(rght ,x))
  (define ((split f g) x)
    (match x [`(left ,y) (f y)] [`(rght ,y) (g y)]))
  (define (from-initial _) (error "impossible"))
  (define (eval x) ((pi1 x) (pi2 x)))
  (define (((transpose f) a) b) (f (cons a b)))

  ;; using hashtables to pass around contexts.
  ;; could use vectors or lists instead.
  (define context-empty (void))
  (define ((context-get _ sym) h) (hash-ref h sym))
  (define (context-extend _ sym)
    (values (void) (match-lambda [(cons h x) (hash-set h sym x)])))
  )

(define-unit products->contexts@
  (import cat^ products^)
  (export contexts^)
  (define context-empty '())
  (define (context-get ctx sym)
    (match ctx
      ['() (error "unbound symbol")]
      [(cons (== sym) _) pi2]
      [(cons _ xs) (after (context-get xs sym) pi1)]))
  ;; Γ × A → Γ,A
  (define (context-extend ctx sym)
    (values (cons sym ctx) nop)))

(define-compound-unit/infer racket+contexts@
  (import)
  ;; ugh, look at all this boilerplate.
  (export cat^ products^ sums^ exponentials^ contexts)
  (link
   (((cat : cat^) (products : products^)
     (_0 : sums^) (_1 : exponentials^))
    racket@)
   (((contexts : contexts^)) products->contexts@ cat products)
   ))


;; ---------- CARTESIAN STRING DIAGRAMS ----------
(define dataflow-nodes (make-parameter '()))
(define/contract (dataflow-node! morphism ins outs)
  (-> (or/c symbol? syntax?) (listof symbol?) (listof symbol?) void?)
  (dataflow-nodes (cons (list morphism ins outs) (dataflow-nodes))))
(define (dataflow-call! function . ins)
  (define out (gensym))
  (dataflow-node! function ins `(,out))
  (list out))


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
  (define (finalize f) ((f context-empty) (hash)))
  (define ((var name) ctx) (context-get ctx name))
  (define ((app e1 e2) ctx) (seq exp:eval (pair (e1 ctx) (e2 ctx))))
  (define ((lam x e) ctx)
    (define-values (e-ctx extend-morph) (context-extend ctx x))
    ;; exp:transpose : (Γ × A → B) -> (Γ → A => B)
    (exp:transpose (seq extend-morph (e e-ctx))))
  (define ((project i n e) ctx)
    (match n
      [1 (e ctx)]
      [2 (seq (e ctx) (match i [0 pi1] [1 pi2]))]
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
  (link racket@ cat->stlc@))


(module+ test
  (require rackunit)
  (define-values/invoke-unit/infer racket-stlc@)
  (check-eqv? 2 ((finalize (lam 'x (var 'x))) 2))
  (check-eqv? 1 (((finalize (lam 'x (lam 'y (var 'x)))) 1) 2))
  (check-eqv? 0 ((finalize (lam 'x (project 0 2 (var 'x)))) '(0 . 1)))
  (check-equal? '(0 . 0)
                ((finalize (lam 'x (tuple (var 'x) (var 'x)))) '0))
  )
