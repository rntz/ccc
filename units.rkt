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


;;; ---------- CONTEXTS ----------
(define context? (listof (list/c symbol? any/c)))

(define/contract context-empty context? '())
(define/contract (context-single x A)
  (-> symbol? any/c context?)
  `((,x ,A)))
(define/contract context-append (-> context? ... context?) append)
(define (context-extend cx x A) (context-append cx (context-single x A)))
(define (context-type-of cx x [failure-result
                               (lambda () (error 'context-type-of "unbound variable ~s" x))])
  (match (assoc x (reverse cx))
    [#f (failure-result)]
    [`(,_ ,A) A]))
;; TODO: awful O(n) lookup here.
;; reversed lists? snoc-lists? a different sequence repr?
(define/contract (context-index-of cx x)
  (-> context? symbol? any/c)
  (last (indexes-where cx (lambda (y) (equal? x (first y))))))
(define context-index-ref list-ref)
(define list->context identity)
(define context-size length)
(define (context-vars cx) (map first cx))
;; would be nice if context-types were O(1) and structure-sharing.
(define (context-types cx) (map second cx))
(define/contract (in-context cx)
  (-> context? sequence?)
  (in-parallel (context-vars cx) (context-types cx)))


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
   ;; are these contexts or not?
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
;; TODO: use contexts here, otherwise we forget parameter names
;; when compiling lambdas.

;; shouldn't we be putting type info in our dataflow graph?
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
  (define (nop Γ) identity)
  (define ((seq . Γs) . funcs) (apply compose1 (reverse funcs)))
  (define (((parallel Γs Δs) fs) inputs)
    (append*
     (for/list ([Γ Γs] [Δ Δs] [f fs])
       (define-values (before after) (split-at inputs (context-size Γ)))
       (set! inputs after)
       (define outs (f before))
       (unless (= (length outs) (context-size Δ)) (error "wrong # of outputs"))
       outs)))

  ;; -- cartesian --
  ;; Γ, (Δᵢ)ᵢ -> (Γ → Δᵢ)ᵢ -> Γ → (Δᵢ)ᵢ
  (define (((fork Γ Δs) fs) inputs)
    (unless (= (context-size Γ) (length inputs)) (error "wrong # of inputs"))
    (for*/list ([f fs] [x (f inputs)]) x))
  (define ((rename Γ rho) inputs)
    (unless (= (context-size Γ) (length inputs)) (error "wrong # of inputs"))
    (for/list ([i rho]) (list-ref inputs i)))
  (define ((merge As) inputs)
    (unless (= (length As) (length inputs)) (error "wrong # of inputs"))
    (dataflow-apply! 'list inputs))
  (define ((split As) inputs)
    (unless (= 1 (length inputs)) (error "too many inputs"))
    ;; TODO: pass a context here and use its names for the outputs?
    (dataflow-node! 'list->values inputs (for/list ([_ As]) (gensym 'list->values))))

  ;; -- closed --
  (define (((uncurry Γ Δ Ω) morph) inputs)
    (define-values (gamma delta) (split-at inputs (context-size Γ)))
    (match-define `(,f) (morph gamma))
    (dataflow-apply! 'apply (cons f delta)))
  (define (((curry Γ Δ Ω) morph) gamma)
    ;; TODO: this feels kinda hackish. it also generates slightly ugly code.
    ;; maybe the right way to do this is in Dan Ghica's work somewhere.
    (define delta
      (for/list ([(x A) (in-context Δ)]) (gensym x)))
    (dataflow-node!
     `(lambda _ (lambda ,delta ,@(string->racket-body morph (append gamma delta))))
     gamma
     (for/list ([(x A) (in-context Ω)]) (gensym x)))
    ;; ;; Version which captures twice but feels more "in the spirit" of dataflow.
    #;
    (dataflow-node!
     `(lambda ,gamma (lambda ,delta ,@(string->racket-body morph (append gamma delta))))
     gamma
     (for/list ([_ Ω]) (gensym 'result)))
    ))


;; ---------- Explicitly typed STLC ----------
;; STLC contexts Γ are represented by lists ((x₁ A₁) ... (xₙ Aₙ)).
(define-signature stlc^
  (var       ;; Γ, x, A    ->  Γ → A      where x:A ∈ Γ
   lam       ;; Γ, x, A, B ->  Γ,x:A → B          ->  Γ → A => B
   app       ;; Γ, A, B    ->  Γ → A => B, Γ → A  ->  Γ → B
   tuple     ;; Γ, Aᵢ...   ->  (Γ → Aᵢ)...        ->  Γ → Πᵢⁿ Aᵢ
   let-tuple ;; Γ, (xᵢ)ᵢ, (Aᵢ)ᵢ, B  ->  Γ → Πᵢ Aᵢ, Γ,(xᵢ:Aᵢ)ᵢ → B -> Γ → B
   ))

;; (define stlc-context (make-parameter (hash)))
;; (define (stlc-extend xs [ctx (stlc-context)])
;;   (hash-union ctx (for/hash ([x xs] [i (in-naturals (hash-count ctx))])
;;                     (values x i))))
;; (define-syntax-rule (stlc-with xs body ...)
;;   (parameterize ([stlc-context (stlc-extend xs)]) body ...))

(define-unit concat->stlc@
  (import cat^ cartesian-concat^ closed-concat^)
  (export stlc^)
  (define M context-types)
  (define (var Γ x A)
    (select Γ (context-index-of Γ x)))
  (define ((lam Γ x A B) e)
    ((curry Γ (context-single x A) (context-single 'result B)) e))
  (define ((app Γ A B) e1 e2)
    ;; e1               Γ → A => B
    ;; e2               Γ → A
    ;; fork (id, e2)    Γ → Γ,A         <- we compose
    ;; uncurry e1       Γ,A → B         <- these two
    ;; desired          Γ → B
    (define Acx (context-single 'arg A))
    (define Bcx (context-single 'result B))
    ((seq Γ (context-append Γ Acx) Bcx)
     ((fork Γ `(,Γ ,Acx)) (list (nop Γ) e2))
     ((uncurry Γ Acx Bcx) e1)))
  (define ((tuple Γ . As) . es)
    (define Acxs (for/list ([A As]) (context-single (gensym) A)))
    (define Ascx (apply context-append Acxs))
    (define tuplecx (context-single 'result `(tuple ,@As)))
    ((seq Γ Ascx tuplecx)
     ((fork Γ Acxs) es)
     (merge As)))
  (define ((let-tuple Γ xs As B) expr body)
    (define Ascx (list->context (for/list ([A As]) `(,(gensym) ,A))))
    (define tuplecx (context-single 'tuple `(tuple ,@As)))
    ((seq Γ (context-append Γ Ascx) (context-single 'result B))
     ;; fork id (expr;split)
     ((fork Γ `(,Γ ,As))
      (list nop ((seq Γ tuplecx Ascx)
                 (expr)
                 (split As))))
     body)))


;; ---------- Bidirectional typechecking ----------
(define-signature bidir^ (check infer elab))

(define type? any/c)
(define term? any/c)

(define (subtype? x y) (equal? x y))

(define-unit stlc->bidir@
  (import stlc^)
  (export bidir^)
  ;; TODO: rewrite to use contexts
  (define Γ (make-parameter context-empty))
  (define (elab ctx tp term)
    #;(-> (listof (list/c symbol? type?)) type? term?
          (values type? any/c))
    (parameterize ([Γ ctx]) (infer term tp)))
  (define (check e t)
    (define-values (tp term) (infer e t))
    term)
  (define (infer e [expect #f])
    (define (inferred tp term)
      (when (and expect (not (subtype? tp expect)))
        (error 'infer "found ~s want ~s" tp expect))
      (values tp term))
    (match e
      [(? symbol? x)
       (define A (context-type-of (Γ) x))
       (inferred A (var (Γ) x A))]
      [`(tuple ,@es)
       (match-define `(tuple ,@As) expect)
       (unless (length=? As es) (error 'infer "tuple has wrong length"))
       (values expect (apply (apply tuple (Γ) As)
                             (map check es As)))]
      ;; TODO: let-tuple
      [`(let-tuple ,@_) TODO]
      [`(lambda (,x) ,e)
       (match-define `(-> ,A ,B) expect)
       (values expect
               ((lam (Γ) x A B)
                (parameterize ([Γ (context-extend (Γ) x A)])
                  (check e B))))]
      ;; fallthrough case: function application
      [`(,e1 ,e2)
       (match-define-values  (`(-> ,A ,B) m1) (infer e1))
       (define m2 (check e2 A))
       (inferred B ((app (Γ) A B) m1 m2))]
      )))


;; ---------- TESTS ----------
(define-compound-unit/infer stlc-strings@
  (import)
  (export stlc^ bidir^)
  (link strings@ concat->stlc@ stlc->bidir@))

(module+ test
  (require rackunit)
  (define-values/invoke-unit/infer stlc-strings@)

  (define (run ctx tp term)
    (set! ctx (list->context ctx))
    (define vars (map first ctx))
    (define-values (_ string-maker) (elab ctx tp term))
    (define-values (outs nodes)
     (parameterize ([dataflow-nodes '()])
       (define outs (string-maker vars))
       (values outs (reverse (dataflow-nodes)))))
    ;; A fairly simple compilation into Racket code. this does some simple
    ;; output-inlining. it could be generalized by noticing when a node produces
    ;; a single output which is used only once and inlining that computation
    ;; into its consumer.
    (define direct-outputs (make-hash))
    (define (output x)
      (hash-ref direct-outputs x (lambda () x)))
    (define definitions
      (append*
       (for/list ([n nodes])
         (match-define (list func ins outs) n)
         (match outs
           ['() `((,func ,@ins))]
           [`(,x)
            #:when (member x outs)
            (hash-set! direct-outputs x `(,func ,@ins))
            '()]
           [`(,x) `((define ,x (,func ,@ins)))]
           [xs `((define-values ,xs (,func ,@ins)))]))))
    (define result
      (match outs
        ['() '(void)]
        [`(,x) (output x)]
        [outs `(values ,@(map output outs))]))
    (if (null? definitions)
        result
        `(let () ,@definitions ,result)))

  (pretty-print
   (run '((a A) (b B)) '(tuple B A) '(tuple b a)))
  (pretty-print
   (run '((a A)) '(-> B A) '(lambda (b) a)))
  (pretty-print
   (run '() '(-> A (-> B A)) '(lambda (a) (lambda (b) a))))
  (pretty-print
   (run '() '(-> A (tuple A A)) '(lambda (a) (tuple a a))))
  )
