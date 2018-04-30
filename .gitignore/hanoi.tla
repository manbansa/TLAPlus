------------------------------- MODULE hanoi -------------------------------
EXTENDS TLC, Sequences, Integers
(* --algorithm hanoi
(***************************************************************************
Global variables
tower: Think of it as a 2D array where 
        tower[x] : represents xth tower (or rod), with disks in it
        tower[x] : represents value of yth disk in xth tower
 ***************************************************************************)
variables tower = << <<1,2,3>> , <<>>, <<>> >>,
begin
    while TRUE do
        (*******************************************************************
           Keep running this loop until following is true. 
           
           Question:- 1. Not sure if it is the way to put invariants in PlusCal??
                      2. Is there any other way as well??
         *******************************************************************)
        assert tower[3] /= <<1,2,3>>;
        
        (*******************************************************************
            'from' is the index of each tower, which satisfies
            the following condition(s)
                1. tower[from] is not empty, i.e. it has atleast one disk.  
         *******************************************************************)
        with from \in {x \in DOMAIN tower: tower[x] /= <<>> } do
        
            (***************************************************************
                'to' is the index of each tower, which satisfies 
                the following condition(s)
                1. to != from (note syntax is y\= from)
                   And (     tower[to] is not empty 
                         OR  top element of tower[from] < top element of tower[to])
                         
                Learnings:- 1. How to specify multiple conditions while
                               selecting an element
             ***************************************************************)
            with to \in { y \in DOMAIN tower: y /= from 
                                       /\ \/ tower[y] = <<>>
                                          \/ tower[from][1] < tower[y][1] } do
                                          
                (***********************************************************
                    1. Remove top element from tower[from]
                    2. And put it on top of tower[to]
                    
                    Learnings:- 1. || helps in writing multiple statements inside "with".
                                2. On replacing (||) with (;), you will face a parsing error
                                   mentioning 
                                   "Second assignment of same variable inside a 'with' statement
                 ***********************************************************)
                tower[from] := Tail(tower[from]) ||
                tower[to] := <<Head(tower[from])>> \o tower[to];
            end with;
        end with;
    end while;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLE tower

vars == << tower >>

Init == (* Global variables *)
        /\ tower = << <<1,2,3>> , <<>>, <<>> >>

Next == /\ Assert(tower[3] /= <<1,2,3>>, 
                  "Failure of assertion at line 19, column 9.")
        /\ \E from \in {x \in DOMAIN tower: tower[x] /= <<>> }:
             \E to \in { y \in DOMAIN tower: y /= from
                                      /\ \/ tower[y] = <<>>
                                         \/ tower[from][1] < tower[y][1] }:
               tower' = [tower EXCEPT ![from] = Tail(tower[from]),
                                      ![to] = <<Head(tower[from])>> \o tower[to]]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 29 16:57:05 PDT 2018 by maneetb
\* Created Sun Apr 29 13:42:22 PDT 2018 by maneetb
