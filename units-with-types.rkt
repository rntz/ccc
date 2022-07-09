#lang racket

(require (prefix-in racket: racket))
(require (only-in racket/hash hash-union))
(require syntax/parse/define)

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])

(define (reverse-compose1 . procs) (apply compose1 (reverse procs)))
(define (reverse-compose . procs) (apply compose (reverse procs)))
(define (list->values l) (apply values l))
(define (length=? A B) (= (length A) (length B)))


;;; ---------- SIGNATURES ----------
(define-signature cat^
  (nop ;; (A: obj) -> A → A
   seq ;; ([A, ..., Z]: list obj), A → B, B → C, ..., Y → Z -> A → Z
   ))
(define-signature products^
  (project ;; i, (Aᵢ: obj)ᵢ -> Πᵢⁿ Aᵢ → Aᵢ
   tuple   ;; Γ, (Aᵢ, fᵢⁿ : Γ → Aᵢ)ᵢ -> Γ → Πᵢ Aᵢ
   ))
(define-signature exponentials^
  (eval      ;; A, B -> (A => B) × A → B
   transpose ;; Γ, A, (Γ × A → B) -> (Γ → A => B)
   ))
(define-signature contexts^
  (context-empty  ;; Γ
   context-get    ;; Γ, x:sym -> Γ → A      where x:A ∈ Γ
   context-extend ;; Γ, x:sym -> (Γ,x:A), (Γ × A → Γ,A)
   ))

;; cartesian concategory stuff
(define-signature cartesian^ extends cat^
  (;;parallel ;; (Γᵢ, Δᵢ, Γᵢ → Δᵢ)ᵢ -> (Γ₁ ... Γₙ → Δ₁ ... Δₙ)
   parallel ;; (Γᵢ)ᵢ, (Δᵢ)ᵢ, (Γᵢ → Δᵢ) -> (Γ₁ ... Γₙ → Δ₁ ... Δₙ)
   ;;permute  ;; Γ, π -> π(Γ) → Γ
   fork ;; Γ, (Δᵢ)ᵢ, (Γ → Δᵢ)ᵢ -> Γ → (Δᵢ)ᵢ
   rename ;; Γ, ρ -> ρ(Γ) → Γ
   merge ;; (Aᵢ)ᵢ -> A₁, ..., Aₙ → A₁ ⊗ ... ⊗ Aₙ
   split ;; (Aᵢ)ᵢ -> A₁ ⊗ ... ⊗ Aₙ → A₁, ..., Aₙ
   (define-values (project) (lambda (Γ . idxs) (rename Γ idxs)))
   ))



#;
(define-unit racket-multi@
  (import)
  (export cartesian^)
  (define (nop As) values)
  (define (seq As . funcs) (apply compose (reverse funcs)))
  (define ((parallel tagged-funcs) . inputs)
    TODO)
  )



;;; ---------- STRINGS ----------
;; TODO: shouldn't we be putting type info here?
(define dataflow-nodes (make-parameter '()))
(define/contract (dataflow-node! morphism ins outs)
  (-> (or/c symbol? syntax?) (listof symbol?) (listof symbol?) void?)
  (dataflow-nodes (cons (list morphism ins outs) (dataflow-nodes))))
(define (dataflow-apply! function ins)
  (define out (gensym (cond [(symbol? function) function]
                            [(identifier? function) (syntax-e function)]
                            [#t "tmp"])))
  (dataflow-node! function ins `(,out))
  (list out))
(define (dataflow-call! function . ins) (dataflow-apply! function ins))

(define-unit strings@
  (import)
  (export cartesian^)
  (define (nop A) identity)
  (define (seq As . funcs) (apply compose1 (reverse funcs)))
  (define ((parallel Γs Δs fs) inputs)
    ;; #:do not available until Racket 8.4
    #;(for/list ([Γ Γs] [Δ Δs] [f fs]
               #:do [(define-values (before after) (split-at inputs (length Γ)))
                     (set! inputs after)]
               [out (f before)])
      out)
    (append*
     (for/list ([Γ Γs] [Δ Δs] [f fs])
       (define-values (before after) (split-at inputs (length Γ)))
       (set! inputs after)
       (define outs (f before))
       (unless (length=? Δ outs) (error "wrong # of outputs"))
       outs)))
  ;; Γ, (Δᵢ)ᵢ, (Γ → Δᵢ)ᵢ -> Γ → (Δᵢ)ᵢ
  (define ((fork Γ Δs fs) inputs)
    (for*/list ([f fs] [x (f inputs)]) x))
  (define ((rename Γ rho) inputs)
    (for/list ([i rho]) (list-ref inputs i)))
  (define ((merge As) inputs)
    (unless (= (length As) (length inputs)) (error "wrong # of inputs"))
    (dataflow-apply! #'list inputs))
  (define ((split As) inputs)
    (unless (= 1 (length inputs)) (error "too many inputs"))
    (dataflow-apply! #'list->values inputs)))


;; ---------- STLC ----------
(define-signature stlc^
  (var       ;; x -> (Γ → A)      where x:A ∈ Γ
   lam       ;; x, (Γ,x:A → B) -> (Γ → A => B)
   app       ;; Γ, A, B, (Γ → A => B), (Γ → A) -> (Γ → B)
   tuple     ;; Γ, (Aᵢ)ᵢ, (Γ → Aᵢ)ᵢ -> (Γ → Πᵢⁿ Aᵢ)
   let-tuple ;; Γ, (xᵢ)ᵢ, (Aᵢ)ᵢ, B, (Γ → Πᵢ Aᵢ), (Γ,(xᵢ:Aᵢ)ᵢ → B) -> Γ → B
   ))

(define stlc-context (make-parameter (hash)))
(define (stlc-extend xs [ctx (stlc-context)])
  (hash-union ctx (for/hash ([x xs] [i (in-naturals (hash-count ctx))])
                    (values x i))))
(define-syntax-rule (stlc-with xs body ...)
  (parameterize ([stlc-context (stlc-extend xs)]) body ...))

(define-unit concat->stlc@
  (import cartesian^)
  (export stlc^)
  (define ((var Γ name))
    (project Γ (hash-ref (stlc-context) name)))
  (define ((lam Γ A e)) TODO)
  (define ((app Γ A B e1 e2)) TODO)
  (define ((tuple Γ As es))
    (seq
     (list Γ As `((tuple ,@As)))
     (fork Γ (map list As) (map (lambda (x) (x)) es))
     (merge As)))
  (define ((let-tuple Γ xs As B expr body))
    (seq
     `(,Γ ,(append Γ As) (,B))
     ;; fork id (expr;split)
     (fork Γ (list Γ As)
           (list nop (seq `(,Γ ((tuple ,@As)) ,As) (expr) (split As))))
     (stlc-with xs (body)))))

(define-compound-unit/infer stlc-strings@
  (import)
  (export stlc^)
  (link strings@ concat->stlc@))

(module+ test
  (require rackunit)
  (define-values/invoke-unit/infer stlc-strings@)

  (define (run xs Γ A term)
    (define string-maker
      (parameterize ([stlc-context (stlc-extend xs (hash))])
        (term)))
    (parameterize ([dataflow-nodes '()])
      (define outs (string-maker xs))
      (values outs (dataflow-nodes))))

  (define Γ '(A B))
  (run '(a b) Γ '((tuple B A))
       (tuple Γ '(B A)
              (list (var Γ 'b) (var Γ 'a))))  )
