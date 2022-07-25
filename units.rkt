#lang racket

(require (only-in racket/hash hash-union))
(require syntax/parse/define)

(define-syntax-parser TODO
  [_ #'(error "TODO: unimplemented")])

(define (reverse-compose1 . procs) (apply compose1 (reverse procs)))
(define (reverse-compose . procs) (apply compose (reverse procs)))
(define (list->values l) (apply values l))
(define (length=? A B) (= (length A) (length B)))
(define/contract (chunk sizes inputs)
  (-> (listof natural?) list/c (listof list/c))
  (define result
    (for/list ([n sizes])
      (define-values (before after) (split-at inputs n))
      (set! inputs after)
     before))
  (unless (null? inputs) (error "too many input values"))
  result)

;;; ---------- CONTEXTS ----------
(define type? any/c)
(define context? (listof (list/c symbol? type?)))

(define list->context identity)
(define context-size length)
(define/contract context-empty context? '())
(define/contract (context-single x A)
  (-> symbol? type? context?)
  `((,x ,A)))
(define/contract context-append (-> context? ... context?) append)
(define (context-type-of cx x [failure-result
                               (lambda () (error 'context-type-of "unbound variable ~s" x))])
  (match (assoc x (reverse cx))
    [#f (failure-result)]
    [`(,_ ,A) A]))
;; TODO: awful O(n) lookup here.
;; reversed lists? snoc-lists? a different sequence repr?
(define/contract (context-index-of cx x)
  (-> context? symbol? natural?)
  (last (indexes-where cx (lambda (y) (equal? x (first y))))))
(define (context-vars cx) (map first cx))
;; would be nice if context-types were O(1) and structure-sharing.
(define (context-types cx) (map second cx))

;; derived functions
(define (context-extend cx x A) (context-append cx (context-single x A)))
(define/contract (in-context cx)
  (-> context? sequence?)
  (in-parallel (context-vars cx) (context-types cx)))
(define/contract (types->context types [name #f])
  (-> (listof type?) context?)
  (list->context (for/list ([A types]) `(,(or name "tmp") ,A))))
(define (context->gensyms cx) (map gensym (context-vars cx)))


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
   ;; are these contexts or not? for now, just lists of types.
   merge    ;; (Aᵢ)ᵢ -> A₁, ..., Aₙ → A₁ ⊗ ... ⊗ Aₙ
   split    ;; (Aᵢ)ᵢ -> A₁ ⊗ ... ⊗ Aₙ → A₁, ..., Aₙ
   (define-values (select) (lambda (Γ . idxs) (rename Γ idxs)))
   ))

;; closed concategory, v2
(define-signature closed-concat^
  (curry   ;; Γ, Δ, Ω  ->  (Γ,Δ → Ω)     ->  Γ → (Δ => Ω)
   uncurry ;; Γ, Δ, Ω  ->  Γ → (Δ => Ω)  ->  Γ,Δ → Ω
   ;; previously I used eval:
   ;; eval    ;; Γ, Δ    -> (Γ => Δ), Γ → Δ
   ;; but Jacques Carette suggested uncurry instead.
   ))


;;; ---------- STRINGS ----------
;; shouldn't we be putting type info in our dataflow graph?
(struct node (function inputs outputs) #:prefab)

(define dataflow-nodes (make-parameter '()))
(define/contract (dataflow-node! function ins outs)
  (-> (or/c symbol? syntax? procedure?) (listof symbol?) (listof symbol?)
      (listof symbol?))
  (dataflow-nodes (cons (node function ins outs) (dataflow-nodes)))
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

  ;; this deeply intertwines strings with compiling to racket.
  ;; TODO: find a way to untangle this.
  (define (string->racket-pair morph inputs)
    (define-values (outs nodes)
      (parameterize ([dataflow-nodes '()])
        (define outs (morph inputs))
        (values outs (reverse (dataflow-nodes)))))
    ;; Find variables used linearly. Used for inlining.
    (define used-once
      (let ([usage (make-hash (for/list ([x outs]) (cons x 1)))])
        (for* ([n nodes] [x (node-inputs n)]) (hash-update! usage x add1 0))
        (for/set ([(x n) usage] #:when (= n 1)) x)))
    ;; We inline variables which are produced as the sole output of a node and
    ;; used exactly once.
    (define inlined (make-hash))
    (define (edge-term edge) (hash-ref inlined edge (lambda () edge)))
    (define definitions
      (append*
       (for/list ([n nodes])
         (define args (map edge-term (node-inputs n)))
         (define term
           (match (node-function n)
             [(? procedure? f) (f args)]
             [(? (or/c symbol? syntax?) f) `(,f ,@args)]
             [_ (error "uh oh")]))
         (match (node-outputs n)
           ['() `(,term)]
           [`(,x) #:when (set-member? used-once x)
            (hash-set! inlined x term)
            '()]
           [`(,x) `((define ,x ,term))]
           [xs `((define-values ,xs ,term))]))))
    (define result
      (match outs
        ['() '(void)]
        [`(,x) (edge-term x)]
        [outs `(values ,@(map edge-term outs))]))
    (values definitions result))

  (define (string->racket-body morph inputs)
    (define-values (definitions result) (string->racket-pair morph inputs))
    (append definitions (list result)))

  (define (string->racket morph inputs)
    (define-values (definitions result) (string->racket-pair morph inputs))
    (if (null? definitions) result `(let () ,@definitions ,result)))

  ;; -- concategory --
  (define (nop Γ) identity)
  (define ((seq . Γs) . funcs) (apply compose1 (reverse funcs)))
  (define (((parallel Γs Δs) fs) inputs)
    (error "this seems to be dead code")
    (unless (length=? Γs Δs) (error "what are you doing"))
    (unless (length=? Γs fs) (error "wrong number of functions"))
    (append*
     (for/list ([f fs] [Δ Δs] [ins (chunk (map context-size Γs) inputs)])
       (define outs (f ins))
       (unless (= (context-size Δ) (length outs)) (error "wrong # of outputs"))
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
    (define delta (context->gensyms Δ))
    (dataflow-node!
     ;; yes I mean to shadow gamma here
     (lambda (gamma) `(lambda ,delta ,@(string->racket-body morph (append gamma delta))))
     gamma
     (context->gensyms Ω))))


;; ---------- Explicitly typed STLC ----------
(define-signature stlc^
  (var       ;; Γ, x, A    ->  Γ → A      where x:A ∈ Γ
   lam       ;; Γ, x, A, B ->  Γ,x:A → B          ->  Γ → A => B
   app       ;; Γ, A, B    ->  Γ → A => B, Γ → A  ->  Γ → B
   tuple     ;; Γ, Aᵢ...   ->  (Γ → Aᵢ)...        ->  Γ → Πᵢⁿ Aᵢ
   let-tuple ;; Γ, (xᵢ)ᵢ, (Aᵢ)ᵢ, B  ->  Γ → Πᵢ Aᵢ, Γ,(xᵢ:Aᵢ)ᵢ → B -> Γ → B
   ))

(define-unit concat->stlc@
  (import cat^ cartesian-concat^ closed-concat^)
  (export stlc^)
  (define M context-types)
  (define (var Γ x A)
    (select Γ (context-index-of Γ x)))
  (define ((lam Γ x A B) e)
    ((curry Γ (context-single x A) (context-single 'result B)) e))
  (define ((app Γ A B) e1 e2)
    ;; e2                e1
    ;; Γ → A             Γ → A => B
    ;;
    ;; fork (id, e2)  ;  uncurry e1
    ;;       Γ → Γ,A     Γ,A → B
    ;;       Γ        →        B
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

(define (subtype? x y) (equal? x y))

(define-unit stlc->bidir@
  (import stlc^)
  (export bidir^)
  (define Γ (make-parameter context-empty))
  (define (elab ctx tp term)
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
  (export stlc^ bidir^ string-extras^)
  (link strings@ concat->stlc@ stlc->bidir@))

(module+ test
  (require rackunit)
  (define-values/invoke-unit/infer stlc-strings@)

  (define (run ctx tp term)
    (set! ctx (list->context ctx))
    (define vars (map first ctx))
    (define-values (_ string) (elab ctx tp term))
    (string->racket string vars))

  (pretty-print (run '() '(tuple) '(tuple)))
  (pretty-print (run '((a A)) 'A 'a))
  (pretty-print (run '((a A)) '(tuple) '(tuple)))
  (pretty-print (run '((a A)) '(tuple A A) '(tuple a a)))
  (pretty-print (run '((a A) (b B)) '(tuple B A) '(tuple b a)))
  (pretty-print (run '((a A)) '(-> B A) '(lambda (b) a)))
  (pretty-print (run '() '(-> A (-> B A)) '(lambda (a) (lambda (b) a))))
  (pretty-print (run '() '(-> A (tuple A A)) '(lambda (a) (tuple a a))))
  )
