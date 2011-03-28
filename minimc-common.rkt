#lang racket

; I should probably only be exporting ctl-sat? but I don't want to change this for fear of breaking something.
(provide (all-defined-out))
(require mzlib/string)

#| For a model to interface with our sat-set function, it must have a function
defined that looks like the following:|#

#;(define (Model param)
  (match param
    ['atom-to-symbol atom-to-symbol]
    ['starting-state '(and x0 x1 (not x2))]
    ['delta delta]
    ['nsymbols 3]
    ['allvars '(x0 x1 x2)]
    )
  )

#| 
*atom-to-symbol: A function that converts from the variables entered
by the user to the combination ofvariables used internally by the model checker. Sometimes
these will be the same (in which case the function is the identity function).
Generally, though a model with 2^n states needs no more than n variables.

*starting-state: A boolean expression representing the model's start state(s).

*delta: A boolean expressions representing the model's transition function. 

*nsymbols: The number of symbols used internally to represent the model. Given that this is
just the length of allvars, its justification for existing is questionable.

*allvars: A list of all variables used internally to represent the model.


ctl-sat? expects a function of this sort, as do most other functions in this
module (basically any that have a parameter called model).|#



#| we append this character to symbols we want to "prime" when we're introducing
an exists clause. (The obvious choices of * or ' are problematic for various reasons.)|#
(define prime-char "Z")

#| If true, print out some information about what the model checker is doing. This
helps determine whether it's stuck, and where. |#
(define debug #f)

#| Return a first-order formula representing the satisfying set of the given 
CTL expression |#
(define (sat-set expr model)
  (let ([sat-setter (lambda (e) (sat-set e model))])
    (match expr
      ; We leave non-temporal operators alone and recursively evaluate their subparts
      [`(not ,<sub-expr>)
       `(not ,(sat-setter <sub-expr>))]
      [`(and ,<sub-expr1> ,<sub-expr2>)
       `(and ,(sat-setter <sub-expr1>) ,(sat-setter <sub-expr2>))]
      [`(or ,<sub-expr1> ,<sub-expr2>)
       `(or ,(sat-setter <sub-expr1>) ,(sat-setter <sub-expr2>))]
      #| For expressions with temporal operators we use home-baked algorithms,
         or reduce them to equivalent expressions using different operators |#
      [`(exists-until ,<sub1> ,<sub2>)
       (exists-until-sat (sat-setter <sub1>) (sat-setter <sub2>) model)]
      [`(forall-until ,<sub1> ,<sub2>)
       `(not (or ,(exists-until-sat (sat-setter `(not ,<sub2>)) (sat-setter `(not (or ,<sub1> ,<sub2>))) model) ,(exists-globally-sat (sat-setter `(not ,<sub2>)) model)))]
      [`(exists-next ,<sub>)
       (exists-next-sat (sat-setter <sub>) model)]
      [`(forall-next ,<sub>)
       `(not ,(exists-next-sat `(not ,(sat-setter <sub>)) model))]
      [`(exists-finally ,<sub>)
       (exists-until-sat 'true (sat-setter <sub>) model)]
      [`(forall-finally ,<sub>)
       (sat-setter `(forall-until true ,<sub>))]
      [`(exists-globally ,<sub>)
       (exists-globally-sat (sat-setter <sub>) model)]
      [`(forall-globally ,<sub>)
       `(not ,(exists-until-sat 'true `(not ,(sat-setter <sub>)) model))]
      ; We expect our recursion to bottom out here
      [atom ((model 'atom-to-symbol) atom)]
      )
    )
  )

; Given an expression using the model's outer representation, convert it to an
; expression that uses our internal symbols instead.
(define (symbolify expression model)
  (cond
    [(symbol? expression) ((model 'atom-to-symbol) expression)]
    [(list? expression) (cons (car expression) (map (lambda (e) (symbolify e model)) (cdr expression)))]
    [else expression]
    )
  )

; Return whether the given formula is true given the current model
(define (ctl-sat? formula model)
  (sat? `(and ,(model 'starting-state) ,(sat-set formula model)) model)
  )

; Return a formula representing: \exists x' <expr>[x replaced with x']
; Where x is the vector of all variables used in the model, and x' is those same
; variables "primed". 
(define (exists <expr> model [depth 1])
  `(exists ,(map (lambda (var) `(,(prime var depth) Bool)) (model 'allvars)) ,<expr>)
  )

; Return a formula representing: \forall x' <expr>[x replaced with x']
(define (forall <expr> model [depth 1])
  `(forall ,(map (lambda (var) `(,(prime var depth) Bool)) (model 'allvars)) ,<expr>)
  )

; TODO: Depth parameter is redundant now.
(define (prime form [depth 1])
  (match form
    [`(,<sub> ..1) (map prime <sub>)]
    ['true 'true]
    ['false 'false]
    ; Ugly ugly ugly hack to prime only variables. Assume that all variables start with x, and no non-variables do. Better not be using xor!
    [literal (if (and (symbol? literal) (equal? (string-ref (symbol->string literal) 0) #\x))
                 (string->symbol (string-append (symbol->string literal) (*s prime-char depth)))
                 literal)]
    
    )
  )

; Silly convenience function to multiply strings (not needed anymore?)
(define (*s str n)
  (if (zero? n) "" (string-append str (*s str (- n 1))))
  )

(define (exists-next-sat expr model)
  (exists `(and ,(model 'delta) ,(prime expr)) model)
  )

; Return a representation of the sat-set of (\exists init U final)
(define (exists-until-sat init final model)
  (letrec (
           [f_0 (simplify final model)]
           [fixed-point 
            (lambda (f_j [depth 1])
              (let ([f_k 
                     ; This is kludgy. Basically, z3 can only handle simplification on the first iteration,
                     ; but doing so significantly speeds up future iterations.
                     (if (< depth 2) (simplify `(or ,f_j (and ,(exists `(and ,(model 'delta) ,(prime f_j)) model) ,init)) model)
                         `(or ,f_j (and ,(exists `(and ,(model 'delta) ,(prime f_j)) model) ,init)) )
                     ]
                    )
				(if debug (begin
                (display depth) (display "\n")) (void))
                (if (equivalent? f_j f_k model) f_j 
                    (fixed-point f_k (+ depth 1)))
                
                )
              )
            ]
           )
    (fixed-point f_0)
    
    )
  )

(define (forall-until-sat init final model)
  (letrec (
           [f_0 (simplify final model)]
           [fixed-point 
            (lambda (f_j [depth 1])
              (let ([f_k 
                     (if (equal? depth 1) (simplify `(or ,f_j (and ,(forall `(and ,(model 'delta) ,(prime f_j)) model) ,init)) model)
                         `(or ,f_j (and ,(forall `(and ,(model 'delta) ,(prime f_j)) model) ,init)) )
                     ]
                    )
				(if debug (begin
                (display depth) (display "\n")) (void))
                (if (equivalent? f_j f_k model) f_j 
                    (fixed-point f_k (+ depth 1)))
                
                )
              )
            ]
           )
    (fixed-point f_0)
    
    )
  )

(define (exists-globally-sat expr model)
  (letrec (
           [f_0 (simplify expr model)]
           [fixed-point 
            (lambda (f_j [depth 1])
              (let ([f_k 
                     (if (equal? depth 1) (simplify `(and ,f_j ,(exists `(and ,(model 'delta) ,(prime f_j)) model)) model)
                         `(and ,f_j ,(exists `(and ,(model 'delta) ,(prime f_j)) model)) )
                     ]
                    )
                (if debug (begin (display depth) (display "\n")) (void))
                (if (equivalent? f_j f_k model) f_j 
                    (fixed-point f_k (+ depth 1)))
                
                )
              )
            ]
           )
    (fixed-point f_0)
    
    )
  )
; Return whether the two given prop formulas are equivalent.
(define (equivalent? f1 f2 model)
  ; same trick as at the end. We want to check whether this is a TAUTOLOGY, not just satisfiable.
  (not (sat? `(not (iff ,f1 ,f2)) model))
  )

; Return whether or not this first-order (not CTL) formula is satisfiable.
(define (sat? expr model)
  (let* ([s (open-output-string)]
         [input-start (string-append 
                       "(set-option set-param \"PULL_NESTED_QUANTIFIERS\" \"true\")"
                       (format "~s" `(declare-funs ,(map (lambda (var) `(,var Bool)) (model 'allvars)))) 
                       " (assert ")]
         [input-end ") (check-sat)"]
         [command "./z3 -smt2 -nw formula.z3"] ; -nw to disable warnings about quantifier stuff
         )
    
    (display-to-file (string-append input-start (format "~s" expr) input-end) "formula.z3" #:mode 'text #:exists 'replace)
	(if debug (display "determining satisfiability\n") (void))
    (parameterize ([current-output-port s])
      (system command)
      (let ([output (get-output-string s)])
        (cond
          [(equal? output "sat\n") #t]
          [(equal? output "unsat\n") #f]
          [else (error output)]
          )
        )
      )
    )
  )

; Return a simplified version of the given expression using z3's simplification routine
(define (simplify expr model)
  (let* ([s (open-output-string)]
         [input-start (string-append 
                       "(set-option set-param \"ELIM_QUANTIFIERS\" \"true\") (set-option set-param \"STRONG_CONTEXT_SIMPLIFIER\" \"true\")"
                       (format "~s" `(declare-funs ,(map (lambda (var) `(,var Bool)) (model 'allvars)))) " (simplify ")]
         [input-end ")"]
         [command "./z3 -smt2 -nw simplify.z3"]
         )
    
    (display-to-file (string-append input-start (format "~s" expr) input-end) "simplify.z3" #:mode 'text #:exists 'replace)
    (if debug (display "simplifying\n") (void))
    (parameterize ([current-output-port s])
      (system command)
      ; There's probably an easier way to do this. Unfortunately I don't understand ports at all.
      (read-from-string (get-output-string s))
      
      )
    )
  )
