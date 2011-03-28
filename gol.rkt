#lang racket

; A model representing Conway's Game of Life.

(require "minimc-common.rkt")

; If you want to do anything interesting (such as exists-until), z3 will choke
; on a 5x5 grid, and probably on a 4x4 (I gave up after a couple minutes). It
; works on a 3x3 (to try with a 3x3 swap the non-commented versions of all_variables,
; sidelength, and Model with the commented versions). Unfortunately 3x3 GoL is pretty
; trivial.

(define all_variables
  '(
    x11 x12 x13 x14 x15
        x21 x22 x23 x24 x25
        x31 x32 x33 x34 x35
        x41 x42 x43 x44 x45
        x51 x52 x53 x54 x55)
  )

#;(define all_variables
  `(
    x11 x12 x13
        x21 x22 x23
        x31 x32 x33
        )
  )

(define sidelength 5)
;(define sidelength 3)

(define (range n)
  (if (zero? n) '()
      (cons (- n 1) (range (- n 1))))
  )

; Full disclosure: I copied this function from the internet somewhere after
; getting frustrated about not being able to import itertools.combinations
(define (combinations k nlst)
  (cond ((zero? k)
         '(()))
        ((null? nlst)
         '())
        (else
         (append (map (lambda (k-1)
                        (cons (car nlst) k-1))
                      (combinations (- k 1) (cdr nlst)))
                 (combinations k (cdr nlst))))))


; Expects to find a starting configuration at life_starting.txt
; each line of the file should be a pair of the form: (x, y)
; representing one live cell.
; Note that we start from (1, 1) in the top-left corner.
(define (starting-state [infile "life_starting.txt"])
  (let* ([in (open-input-file infile)]
         [live (live_cells in)])
       
    `(and ,@(map
             (lambda (var) 
               (if (member var live) var
                   `(not ,var)
                   )
               )
             all_variables))
    )
  )

(define (line->var line)
  (let ([indices (regexp-match #rx"\\( *([0-9]) *, *([0-9]) *\\)" line)])
    (fromindex (string->number (second indices)) (string->number (third indices)))
    )
  )

; Given a file with a starting configuration, return a list of live cells
(define (live_cells in [acc '()])
  (let ([line (read-line in)])
    (if (eof-object? line) acc
        (live_cells in (cons (line->var line) acc))
        )
    )
  )

; Return a an expression representing the "sum" of the given variables (that is,
; the number of true variables). I guess this makes our formulae not quite first-order,
; but z3 likes doing this arithmetic better than trying to deal with gigantic disjunctions of,
; e.g. all combinations with < 4 true variables.
(define (boolsum vars)
  (if (empty? vars) 0
      ;`(+ (if ,(car vars) 1 0) ,(boolsum (cdr vars)))
      `(+ ,@(map (lambda (var) `(if ,var 1 0)) vars))
      )
  )

; return the first or second index of the variable in the GoL array
(define (toindex var [pos 0])
  (string->number (substring (symbol->string var) (+ pos 1) (+ pos 2)))
  )

; stupid 1-indexing
(define (wraparound i)
  (cond
    [(zero? i) sidelength]
    [(equal? i (+ sidelength 1)) 1]
    [else i]
    )
  )

(define (fromindex i j)
  (string->symbol (string-append "x" (number->string (wraparound i)) (number->string (wraparound j))))
  )

(define (neighbours cell)
  (let (
        [i (toindex cell 0)]
        [j (toindex cell 1)]
        )
    `(
      ,(fromindex (+ i 1) j)
      ,(fromindex (+ i -1) j)
      ,(fromindex (+ i 1) (+ j 1))
      ,(fromindex (+ i 1) (+ j -1))
      ,(fromindex (+ i -1) (+ j 1))
      ,(fromindex (+ i -1) (+ j -1))
      ,(fromindex i (+ j 1))
      ,(fromindex i (+ j -1))
      )
    )
  )

; Return a formula expressing the necessity of cell having exactly n live neighbours
(define (live_neighbours_form cell n)
  (let* (
         [neighbs (neighbours cell)]
         [combos (combinations n neighbs)]
         [neighbours_clause 
          (lambda (combo)
            `(and ,@(map (lambda (n) (if (member n combo) n `(not ,n)) ) neighbs)))
          ]
         )
    `(or ,@(map neighbours_clause combos))
    )
  )


#;(define (transition cell)
    (let ([liveneighbs (boolsum (neighbours cell))]) 
      `(or
        (and ,cell (< ,liveneighbs 2) (not ,(prime cell)))
        (and ,cell (or (= ,liveneighbs 2) (= ,liveneighbs 3)) ,(prime cell))
        (and ,cell (> ,liveneighbs 3) (not ,(prime cell)))
        
        (and (not ,cell) (= ,liveneighbs 3) ,(prime cell))
        (and (not ,cell) (not (= ,liveneighbs 3)) (not ,(prime cell)))
        )
      
      )
    )

(define (transition cell)
  `(or
    (and ,cell (or ,(live_neighbours_form cell 0) ,(live_neighbours_form cell 1)) (not ,(prime cell)))
    (and ,cell (or ,(live_neighbours_form cell 2) ,(live_neighbours_form cell 3)) ,(prime cell))
    (and ,cell (not (or ,(live_neighbours_form cell 0) ,(live_neighbours_form cell 1) ,(live_neighbours_form cell 2) ,(live_neighbours_form cell 3))) (not ,(prime cell)))
    
    (and (not ,cell) ,(live_neighbours_form cell 3) ,(prime cell))
    (and (not ,cell) (not ,(live_neighbours_form cell 3)) (not ,(prime cell)))
    )
  
  )

; a formula representing the entire transition system
(define delta
  (simplify `(and ,@(map transition all_variables)) (lambda (dummy) (append all_variables (prime all_variables))))
  )

(define (Model param)
  (match param
    ['atom-to-symbol (lambda (x) x)]
    ['starting-state (starting-state)]
    ['delta delta]
    ['nsymbols 25]
    ['allvars all_variables]      
    [else (error "uh oh")]
    )
  )

#;(define (Model param)
  (match param
    ['atom-to-symbol (lambda (x) x)]
    ['starting-state (starting-state)]
    ['delta delta]
    ['nsymbols 9]
    ['allvars all_variables]      
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
