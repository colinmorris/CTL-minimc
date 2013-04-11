Intro
=====

    This was an assignment for a course in formal software verification. We had to write a [CTL](http://en.wikipedia.org/wiki/Computation_tree_logic) model checker, then encode Conway's Game of Life as a CTL model, and use our model checker (powered by the Z3 sat solver) to answer questions about the fates of Game of Life configurations. 

    This ended up being the hardest assignment of my university career. Everyone else in the class ended up writing a (much easier) 'explicit state model checker'. I toiled at doing it the 'right way' for probably 2 straight weeks. For my efforts, I got a ridiculously inefficient Game of Life simulator (it chokes on grids larger than 3x3 - Z3 was not as clever as our professor had hoped), but something like 110% on the assignment.

    Everything is written in Racket, which is really well-suited to the kind of recursive descent parsing I ended up doing.
    
Usage
=====

Run `gol.rkt`. By default, it uses a 5x5 GoL grid (probably too big) initialized with starting cells specified in `life_starting.txt`.

It will prompt for a formula, and tell you whether it's true or not. Formulas look something like...

    (exists-until x11 (not x22))

See sat-set in `minimc-common.rkt` for the full allowable syntax (also, see the above link on CTL for the semantics of these expressions).
