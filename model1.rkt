#lang racket

(require "minimc-common.rkt")


; Turn the external prop variables into the internal representations.
(define (atom-to-symbol atom)
  (match atom
    ['a 'x0]
    ['b 'x1]
    ['c 'x2]
    ['a* (prime 'x0)]
    ['b* (prime 'x1)]
    ['c* (prime 'x2)]
    ['true 'true]
    ['false 'false]
    [other other]
    )
  )

; Formula representing the starting state(s?)
(define starting-state
  '(and x0 (not x1) x2)
  )

; hard-code this model's transition system
(define delta
  (symbolify
  '(or
    (and a (not b) c a* (not b*) (not c*))
    (and a (not b) c (not a*) (not b*) c*)
    
    (and a (not b) (not c) a* b* (not c*))
    (and a (not b) (not c) (not a*) (not b*) c)
    
    (and a b (not c) a* b* (not c*))
    (and a b (not c) a* b* c*)
    
    (and a b c (not a*) (not b*) c*)
    
    (and (not a) (not b) c (not a*) (not b*) c*)
    (and (not a) (not b) c a* b* (not c*))
    )
  (lambda (dummy) atom-to-symbol)) ;kludge kludge kludge
  )

(define (Model param)
  (match param
    ['atom-to-symbol atom-to-symbol]
    ['starting-state starting-state]
    ['delta delta]
    ['nsymbols 3]
    ['allvars '(x0 x1 x2)]
    [else (error "uh oh")]
    )
  )

; MAIN
(define (REPL)
  (let (
        [in (read)]
        )
    (if (equal? in 'q) (void)
        (begin (display (ctl-sat? in Model)) (display "\n") (REPL))
        )
    )
  )

(begin
(display "Enter CTL formula:\n")
(REPL)
)
