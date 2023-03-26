
#lang racket
(provide (all-defined-out)) 
(require rackunit)
;; definition of structures for MUPL programs - Do NOT change
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct ifgreater (e1 e2 e3 e4)    #:transparent) ;; if e1 > e2 then e3 else e4
(struct fun  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct call (funexp actual)       #:transparent) ;; function call
(struct mlet (var e body) #:transparent) ;; a local binding (let var = e in body) 
(struct apair (e1 e2)     #:transparent) ;; make a new pair
(struct fst  (e)    #:transparent) ;; get first part of a pair
(struct snd  (e)    #:transparent) ;; get second part of a pair
(struct aunit ()    #:transparent) ;; unit value -- good for ending a list
(struct isaunit (e) #:transparent) ;; evaluate to 1 if e is unit else 0

;; a closure is not in "source" programs but /is/ a MUPL value; it is what functions evaluate to
(struct closure (env fun) #:transparent) 


(define (racketlist->mupllist rkt-lst)
  (cond [(null? rkt-lst) (aunit)]
        [(list? rkt-lst) (apair (car rkt-lst) (racketlist->mupllist (cdr rkt-lst)))]
        [#t (error "Found an unrecognized value o.o")]))


(define (mupllist->racketlist mupl-lst)
  (cond [(aunit? mupl-lst) null]
        [(apair? mupl-lst) (cons (apair-e1 mupl-lst) (mupllist->racketlist (apair-e2 mupl-lst)))]
        [#t (error "Found an unrecognized MUPL value o.o")]))


(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? (car (car env)) str) (cdr (car env))]
        [#t (envlookup (cdr env) str)]))


(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
        [(add? e) 
         (let ([v1 (eval-under-env (add-e1 e) env)]
               [v2 (eval-under-env (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-number")))]
        
        [(int? e) e]
        [(aunit? e) e]
        [(fun? e) (closure env e)]
        [(closure? e) e]
        [(ifgreater? e)
         (let ([v1 (eval-under-env (ifgreater-e1 e) env)]
               [v2 (eval-under-env (ifgreater-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (if (> (int-num v1) (int-num v2))
                   (eval-under-env (ifgreater-e3 e) env)
                   (eval-under-env (ifgreater-e4 e) env))
               (error "MUPL conditional comparison applied to non-number :/")))]
        [(mlet? e)
         (let ([v (eval-under-env (mlet-e e) env)])
           (eval-under-env (mlet-body e) (append (list (cons (mlet-var e) v)) env)))]
        [(call? e)
         (let ([v1 (eval-under-env (call-funexp e) env)]
               [v2 (eval-under-env (call-actual e) env)])
           (if (closure? v1)
               (eval-under-env (fun-body (closure-fun v1))
                               (append (closure-env v1)
				       (list (cons (fun-formal (closure-fun v1)) v2)
                                             (if (fun-nameopt (closure-fun v1))
                                                 (cons (fun-nameopt (closure-fun v1)) v1)
                                                 '(v1)))))
               (error "First parameter in the function call did not evaluate to a closure +_+ ")))]
        [(apair? e)
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))]
        [(fst? e)
         (let ([v (eval-under-env (fst-e e) env)])
           (if (apair? v)
               (apair-e1 v)
               (error "Expression is not a pair; Cannot apply fst >.<")))]
        [(snd? e)
         (let ([v (eval-under-env (snd-e e) env)])
           (if (apair? v)
               (apair-e2 v)
               (error "Expression is not a pair; Cannot apply snd >.<")))]
        [(isaunit? e)
         (let ([v (eval-under-env (isaunit-e e) env)])
           (if (aunit? v)
               (int 1)
               (int 0)))]
        [#t (error (format "Bad MUPL expression: ~v" e))]))
               
               
               


(define (eval-exp e)
  (eval-under-env e null))
        

(define (ifaunit e1 e2 e3)
  (ifgreater (isaunit e1) (int 0) e2 e3))


(define (mlet* pairlst e2)
  (if (null? pairlst)
      e2
      (mlet (caar pairlst) (cdar pairlst) (mlet* (cdr pairlst) e2))))



(define (ifeq e1 e2 e3 e4)
  (mlet* (list (cons "_x" e1) (cons "_y" e2)) (ifgreater (var "_x") (var "_y")
                                                         e4
                                                         (ifgreater (var "_y") (var "_x")
                                                                    e4
                                                                    e3))))


(define mupl-map (fun "helper" "f"
                      (fun "map" "lst"
                           (ifaunit (var "lst")
                                    (aunit)
                                    (apair (call (var "f") (fst (var "lst")))
                                           (call (var "map") (snd (var "lst"))))))))



(define mupl-mapAddN 
  (mlet "map" mupl-map
	(fun "helper-1" "N"
	     (fun "helper-2" "lst"
		  (call (call (var "map") (fun #f "x" (add (var "x") (var "N"))))
			(var "lst"))))))


(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function


(define (compute-free-vars e)
        (define (get e) 
                (cond [(var? e) (cons (set (var-string e)) e)]
                      [(int? e) (cons (set) e)]
                      [(aunit? e) (cons (set) e)]
                      [(apair? e) (let ([p1 (get (apair-e1 e))]
                                        [p2 (get (apair-e2 e))])
                                       (cons (set-union (car p1) (car p2))
                                             (apair (cdr p1) (cdr p2))))]
                      [(add? e) (let ([p1 (get (add-e1 e))]
                                      [p2 (get (add-e2 e))])
                                     (cons (set-union (car p1) (car p2))
                                           (add (cdr p1) (cdr p2))))]
                      [(fst? e) (let ([p (get (fst-e e))])
                                     (cons (car p) (fst (cdr p))))]
                      [(snd? e) (let ([p (get (snd-e e))])
                                     (cons (car p) (snd (cdr p))))]
                      [(isaunit? e) (let ([p (get (isaunit-e e))])
                                         (cons (car p) (isaunit (cdr p))))]
                      [(ifgreater? e) (let ([p1 (get (ifgreater-e1 e))]
                                            [p2 (get (ifgreater-e2 e))]
                                            [p3 (get (ifgreater-e3 e))]
                                            [p4 (get (ifgreater-e4 e))])
                                           (cons (set-union (car p1) (car p2) (car p3) (car p4))
                                                 (ifgreater (cdr p1) (cdr p2) (cdr p3) (cdr p4))))]
                      [(mlet? e) (let ([p-e (get (mlet-e e))]
                                       [p-body (get (mlet-body e))])
                                      (cons (set-union (car p-e) (set-remove (car p-body) (mlet-var e)))
                                            (mlet (mlet-var e) (cdr p-e) (cdr p-body))))]
                      [(fun? e) (let* ([p (get (fun-body e))]
                                       [fv (set-remove (car p) (fun-formal e))] ; fix args
                                       [fv (if (fun-nameopt e)
                                               (set-remove fv (fun-nameopt e)) ; fix fun 
                                               fv)])
                                      (cons fv (fun-challenge (fun-nameopt e) (fun-formal e) (cdr p) fv)))]
                      [(call? e) (let ([p-cls (get (call-funexp e))]
                                       [p-arg (get (call-actual e))])
                                      (cons (set-union (car p-cls) (car p-arg))
                                            (call (cdr p-cls) (cdr p-arg))))]
                      [#t (error (format "bad MUPL expression: ~v" e))]))
        (cdr (get e)))


(define (eval-under-env-c e env)
        (cond [(var? e)
               (envlookup env (var-string e))]

              ;; self evaluate
              [(int? e) e]
              [(aunit? e) e]
              [(closure? e) e]

              ;; addition
              [(add? e) 
               (let ([v1 (eval-under-env-c (add-e1 e) env)]
                     [v2 (eval-under-env-c (add-e2 e) env)])
                    (if (and (int? v1)
                             (int? v2))
                        (int (+ (int-num v1) 
                                (int-num v2)))
                        (error "MUPL addition applied to non-number")))]

              ;; pair
              ;; evaluate pair exp
              [(apair? e)
               (apair (eval-under-env-c (apair-e1 e) env)
                      (eval-under-env-c (apair-e2 e) env))]
              ;; get first part of pair
              [(fst? e)
               (let ([pr (eval-under-env-c (fst-e e) env)]) ; evaluate pair exp
                    (if (apair? pr) ; type checking
                        (apair-e1 pr)
                        (error "MUPL fst applied to non-apair")))]
              ;; get first part of pair
              [(snd? e)
               (let ([pr (eval-under-env-c (snd-e e) env)]) ; evaluate pair exp
                    (if (apair? pr) ; type checking
                        (apair-e2 pr)
                        (error "MUPL snd applied to non-apair")))]

              ;; isaunit
              [(isaunit? e)
               (let ([v (eval-under-env-c (isaunit-e e) env)]) ; evaluate exp
                    (if (aunit? v)
                        (int 1)
                        (int 0)))]

              ;; ifgreater with type checking
              [(ifgreater? e)
               (let ([v1 (eval-under-env-c (ifgreater-e1 e) env)]
                     [v2 (eval-under-env-c (ifgreater-e2 e) env)])
                    (if (and (int? v1) (int? v2)) ; type checking
                        (if (> (int-num v1) (int-num v2))
                            (eval-under-env-c (ifgreater-e3 e) env)
                            (eval-under-env-c (ifgreater-e4 e) env))
                        (error "MUPL comparison applied to non-number")))]

              ;; mlet to extend env with new var and exp
              [(mlet? e)
               (let ([locenv (cons (cons (mlet-var e) (eval-under-env-c (mlet-e e) env)) env)]) ; put new var on the top of env 
                    (eval-under-env-c (mlet-body e) locenv))]

              ;; fun (lexically scoped)
              ;; function evaluates to a closure holding the function and the current environment
              [(fun-challenge? e)
               (closure (set-map (fun-challenge-freevars e) (lambda (s) (cons s (envlookup env s)))) ; only store free variables
                        e)]
              ;; call function with env
              [(call? e)
               (let ([cls (eval-under-env-c (call-funexp e) env)] ; closures
                     [arg (eval-under-env-c (call-actual e) env)]) ; argument
                    (if (closure? cls)
                        (let* ([clsenv (closure-env cls)] ; closure env
                               [func (closure-fun cls)] ; function
                               [bodyenv (cons (cons (fun-formal func) arg) clsenv)] ; put arguments
                               [bodyenv (if (fun-nameopt func) ; if not anonymous nonrecursive functions
                                            (cons (cons (fun-nameopt func) cls) bodyenv) ; add function itself into env (for recurison)
                                            bodyenv)])
                              (eval-under-env-c (fun-body func) bodyenv)) ; evaluate function body under bodyenv (cls + arg + func)
                        (error "MUPL call applied to non-closure")))]

              [#t (error (format "bad MUPL expression: ~v" e))]))

(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))