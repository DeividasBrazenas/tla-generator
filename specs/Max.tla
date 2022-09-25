--------------------------------- MODULE Max ---------------------------------
EXTENDS Naturals, Sequences
CONSTANTS in_a, in_b
(*--algorithm Math

variables result_min, result_max

procedure generated_min(a, b)
begin
generated_min:
if a > b then
  result_min := b;
else
  result_min := a;
end if;
return;
end procedure;

procedure generated_max(a, b)
begin
generated_max:
if a < b then
  result_max := b;
else
  result_max := a;
end if;
return;
end procedure;


begin
min:
  if result_min = defaultInitValue then
    call generated_min(in_a, in_b)
  end if;
max:
  if result_max = defaultInitValue then
    call generated_max(in_a, in_b)
  end if;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d8789d49" /\ chksum(tla) = "ff8c56fa")
\* Label generated_min of procedure generated_min at line 11 col 1 changed to generated_min_
\* Label generated_max of procedure generated_max at line 22 col 1 changed to generated_max_
\* Parameter a of procedure generated_min at line 8 col 25 changed to a_
\* Parameter b of procedure generated_min at line 8 col 28 changed to b_
CONSTANT defaultInitValue
VARIABLES result_min, result_max, pc, stack, a_, b_, a, b

vars == << result_min, result_max, pc, stack, a_, b_, a, b >>

Init == (* Global variables *)
        /\ result_min = defaultInitValue
        /\ result_max = defaultInitValue
        (* Procedure generated_min *)
        /\ a_ = defaultInitValue
        /\ b_ = defaultInitValue
        (* Procedure generated_max *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        /\ stack = << >>
        /\ pc = "min"

generated_min_ == /\ pc = "generated_min_"
                  /\ IF a_ > b_
                        THEN /\ result_min' = b_
                        ELSE /\ result_min' = a_
                  /\ pc' = Head(stack).pc
                  /\ a_' = Head(stack).a_
                  /\ b_' = Head(stack).b_
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << result_max, a, b >>

generated_min == generated_min_

generated_max_ == /\ pc = "generated_max_"
                  /\ IF a < b
                        THEN /\ result_max' = b
                        ELSE /\ result_max' = a
                  /\ pc' = Head(stack).pc
                  /\ a' = Head(stack).a
                  /\ b' = Head(stack).b
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << result_min, a_, b_ >>

generated_max == generated_max_

min == /\ pc = "min"
       /\ IF result_min = defaultInitValue
             THEN /\ /\ a_' = in_a
                     /\ b_' = in_b
                     /\ stack' = << [ procedure |->  "generated_min",
                                      pc        |->  "max",
                                      a_        |->  a_,
                                      b_        |->  b_ ] >>
                                  \o stack
                  /\ pc' = "generated_min_"
             ELSE /\ pc' = "max"
                  /\ UNCHANGED << stack, a_, b_ >>
       /\ UNCHANGED << result_min, result_max, a, b >>

max == /\ pc = "max"
       /\ IF result_max = defaultInitValue
             THEN /\ /\ a' = in_a
                     /\ b' = in_b
                     /\ stack' = << [ procedure |->  "generated_max",
                                      pc        |->  "Done",
                                      a         |->  a,
                                      b         |->  b ] >>
                                  \o stack
                  /\ pc' = "generated_max_"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << stack, a, b >>
       /\ UNCHANGED << result_min, result_max, a_, b_ >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == generated_min \/ generated_max \/ min \/ max
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
===============================================================================
