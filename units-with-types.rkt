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
   seq ;; ([A, ..., Z]: list obj) -> A → B, B → C, ..., Y → Z -> A → Z
   ))

;; cartesian concategory
(define-signature cartesian-concat^ ; extends cat^
  (;;parallel ;; (Γᵢ, Δᵢ, Γᵢ → Δᵢ)ᵢ -> (Γ₁ ... Γₙ → Δ₁ ... Δₙ)
   ;;permute  ;; Γ, π -> π(Γ) → Γ
   parallel ;; (Γᵢ)ᵢ, (Δᵢ)ᵢ -> (Γᵢ → Δᵢ)ᵢ -> (Γ₁ ... Γₙ → Δ₁ ... Δₙ)
   fork     ;; Γ, (Δᵢ)ᵢ -> (Γ → Δᵢ)ᵢ -> Γ → (Δᵢ)ᵢ
   ;; TODO: fork can be derived from rename & para, omit or define it?
   rename   ;; Γ, ρ -> ρ(Γ) → Γ
   merge    ;; (Aᵢ)ᵢ -> A₁, ..., Aₙ → A₁ ⊗ ... ⊗ Aₙ
   split    ;; (Aᵢ)ᵢ -> A₁ ⊗ ... ⊗ Aₙ → A₁, ..., Aₙ
   (define-values (select) (lambda (Γ . idxs) (rename Γ idxs)))
   ))

;; ;; closed concategory, v1
;; (define-signature closed-concat^
;;   (eval      ;; Γ, Δ    -> (Γ => Δ), Γ → Δ
;;    transpose ;; Γ, Δ, Ω -> (Γ,Δ → Ω) -> Γ → (Δ => Ω)
;;    ))

;; closed concategory, v2 (thanks Jacques Carette for the suggestion)
(define-signature closed-concat^
  (uncurry ;; Γ, Δ, Ω  ->  Γ → (Δ => Ω)  ->  Γ,Δ → Ω
   curry   ;; Γ, Δ, Ω  ->  (Γ,Δ → Ω)     ->  Γ → (Δ => Ω)
   ))


#;
(define-unit racket-multi@
  (import)
  (export cartesian-concat^)
  (define (nop As) values)
  (define (seq As . funcs) (apply compose (reverse funcs)))
  (define ((parallel tagged-funcs) . inputs)
    TODO)
  )



;;; ---------- STRINGS ----------
;; TODO: shouldn't we be putting type info here?
(define dataflow-nodes (make-parameter '()))
(define/contract (dataflow-node! morphism ins outs)
  ;; TODO: probably don't want any/c here
  (-> (or/c symbol? syntax? any/c) (listof symbol?) (listof symbol?) (listof symbol?))
  (dataflow-nodes (cons (list morphism ins outs) (dataflow-nodes)))
  outs)
(define (dataflow-apply! function ins)
  (define out (gensym (cond [(symbol? function) function]
                            [(identifier? function) (syntax-e function)]
                            [#t "tmp"])))
  (dataflow-node! function ins `(,out)))
(define (dataflow-call! function . ins) (dataflow-apply! function ins))

(define-signature string-extras^ (string->racket-body string->racket))
(define-unit strings@
  (import)
  (export cat^ cartesian-concat^ closed-concat^ string-extras^)
  (define (string->racket-body morph inputs)
    (define-values (outs nodes)
      (parameterize ([dataflow-nodes '()])
        (define outs (morph inputs))
        (values outs (reverse (dataflow-nodes)))))
    `(,@(for/list ([n nodes])
          (match-define (list func ins outs) n)
          (match outs
            ['() `(,func ,@ins)]
            [`(,x) `(define ,x (,func ,@ins))]
            [xs `(define-values ,xs (,func ,@ins))]))
      ,(match outs
         ['() '(void)]
         [`(,x) x]
         [outs `(values ,@outs)])))
  (define (string->racket morph inputs)
    `(let () ,@(string->racket-body morph)))

  ;; -- concategory --
  (define (nop A) identity)
  (define ((seq . As) . funcs) (apply compose1 (reverse funcs)))
  (define (((parallel Γs Δs) fs) inputs)
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

  ;; -- cartesian --
  ;; Γ, (Δᵢ)ᵢ -> (Γ → Δᵢ)ᵢ -> Γ → (Δᵢ)ᵢ
  (define (((fork Γ Δs) fs) inputs)
    (for*/list ([f fs] [x (f inputs)]) x))
  (define ((rename Γ rho) inputs)
    (for/list ([i rho]) (list-ref inputs i)))
  (define ((merge As) inputs)
    (unless (= (length As) (length inputs)) (error "wrong # of inputs"))
    (dataflow-apply! 'list inputs))
  (define ((split As) inputs)
    (unless (= 1 (length inputs)) (error "too many inputs"))
    (dataflow-node! 'list->values inputs (for/list ([_ As]) (gensym 'list->values))))

  ;; -- closed --
  (define (((uncurry Γ Δ Ω) morph) inputs)
    (define-values (gamma delta) (split-at inputs (length Γ)))
    (match-define `(,f) (morph gamma))
    (dataflow-apply! 'apply (cons f delta)))
  (define (((curry Γ Δ Ω) morph) gamma)
    ;; TODO: this feels kinda hackish. it also generates slightly ugly code.
    ;; maybe the right way to do this is in Dan Ghica's work somewhere.
    (define delta (for/list ([_ Δ]) (gensym 'arg)))
    (dataflow-node!
     `(lambda _ (lambda ,delta ,@(string->racket-body morph (append gamma delta))))
     gamma
     (for/list ([_ Ω]) (gensym 'result)))
    ;; ;; Version which captures twice but feels more "in the spirit" of dataflow.
    #;
    (dataflow-node!
     `(lambda ,gamma (lambda ,delta ,@(string->racket-body morph (append gamma delta))))
     gamma
     (for/list ([_ Ω]) (gensym 'result)))
    ))


;; ---------- STLC ----------
(define-signature stlc^
  (var       ;; Γ, x, A    ->  Γ → A      where x:A ∈ Γ
   lam       ;; Γ, x, A, B ->  Γ,x:A → B          ->  Γ → A => B
   app       ;; Γ, A, B    ->  Γ → A => B, Γ → A  ->  Γ → B
   tuple     ;; Γ, Aᵢ...   ->  (Γ → Aᵢ)...        ->  Γ → Πᵢⁿ Aᵢ
   let-tuple ;; Γ, (xᵢ)ᵢ, (Aᵢ)ᵢ, B  ->  Γ → Πᵢ Aᵢ, Γ,(xᵢ:Aᵢ)ᵢ → B -> Γ → B
   ))

(define stlc-context (make-parameter (hash)))
(define (stlc-extend xs [ctx (stlc-context)])
  (hash-union ctx (for/hash ([x xs] [i (in-naturals (hash-count ctx))])
                    (values x i))))
(define-syntax-rule (stlc-with xs body ...)
  (parameterize ([stlc-context (stlc-extend xs)]) body ...))

;; uncurry ;; Γ, Δ, Ω  ->  Γ → (Δ => Ω)  ->  Γ,Δ → Ω
;; curry   ;; Γ, Δ, Ω  ->  (Γ,Δ → Ω)     ->  Γ → (Δ => Ω)

(define-unit concat->stlc@
  (import cat^ cartesian-concat^ closed-concat^)
  (export stlc^)
  (define ((var Γ x A))
    (select Γ (hash-ref (stlc-context) x)))
  (define (((lam Γ x A B) e))
    ;; (stlc-with '(x) (e)): Γ,A → B
    ;; want: Γ → (A) => (B)
    ((curry Γ `(,A) `(,B)) (stlc-with '(x) (e))))
  (define (((app Γ A B) e1 e2))
    ;; e1               Γ → A => B
    ;; e2               Γ → A
    ;; fork (id, e2)    Γ → Γ,A         <- we compose
    ;; uncurry e1       Γ,A → B         <- these two
    ;; desired          Γ → B
    ((seq Γ (append Γ `(,A)) `(,B))
     ((fork Γ `(,Γ (,A)))
      (list (nop Γ) (e2)))
     ((uncurry Γ `(,A) `(,B))
      (e1))))
  (define (((tuple Γ . As) . es))
    ((seq Γ As `((tuple ,@As)))
     ((fork Γ (map list As))
      (map (lambda (x) (x)) es))
     (merge As)))
  (define (((let-tuple Γ xs As B) expr body))
    ((seq Γ (append Γ As) `(,B))
     ;; fork id (expr;split)
     ((fork Γ (list Γ As))
      (list nop ((seq `(,Γ ((tuple ,@As)) ,As))
                 (expr) (split As))))
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
    (define-values (outs nodes)
     (parameterize ([dataflow-nodes '()])
       (define outs (string-maker xs))
       (values outs (reverse (dataflow-nodes)))))
    ;; a very simple compilation into Racket code.
    `(let ()
       ,@(for/list ([n nodes])
           (match-define (list func ins outs) n)
           (match outs
             ['() `(,func ,@ins)]
             [`(,x) `(define ,x (,func ,@ins))]
             [xs `(define-values ,xs (,func ,@ins))]))
       ,(match outs
          ['() '(void)]
          [`(,x) x]
          [outs `(values ,@outs)])))

  (define Γ '(A B))
  (pretty-print
   (run '(a b) Γ '((tuple B A))
        ((tuple Γ 'B 'A)
         (var Γ 'b 'B)
         (var Γ 'a 'A))))

  (pretty-print
   (run '(a) '(A) '((-> (B) (A)))
        ((lam '(A) 'b 'B 'A)
         (var '(A B) 'a 'A))))
  )
