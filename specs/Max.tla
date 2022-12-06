--------------------------------- MODULE Max ---------------------------------
EXTENDS Naturals, Sequences
CONSTANTS in_a, in_b
(*--algorithm Math

variables input_min_a, input_min_b, result_min, result_max

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

process min = "min"
begin
min:
if input_min_a > input_min_b then
  result_min := input_min_b;
else
  result_min := input_min_a;
end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "678e8bad" /\ chksum(tla) = "ed07eee1")
\* Label generated_min of procedure generated_min at line 11 col 1 changed to generated_min_
\* Label generated_max of procedure generated_max at line 22 col 1 changed to generated_max_
\* Label min of process min at line 33 col 1 changed to min_
\* Parameter a of procedure generated_min at line 8 col 25 changed to a_
\* Parameter b of procedure generated_min at line 8 col 28 changed to b_
CONSTANT defaultInitValue
VARIABLES input_min_a, input_min_b, result_min, result_max, pc, stack, a_, b_, 
          a, b

vars == << input_min_a, input_min_b, result_min, result_max, pc, stack, a_, 
           b_, a, b >>

ProcSet == {"min"}

Init == (* Global variables *)
        /\ input_min_a = defaultInitValue
        /\ input_min_b = defaultInitValue
        /\ result_min = defaultInitValue
        /\ result_max = defaultInitValue
        (* Procedure generated_min *)
        /\ a_ = [ self \in ProcSet |-> defaultInitValue]
        /\ b_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure generated_max *)
        /\ a = [ self \in ProcSet |-> defaultInitValue]
        /\ b = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "min_"]

generated_min_(self) == /\ pc[self] = "generated_min_"
                        /\ IF a_[self] > b_[self]
                              THEN /\ result_min' = b_[self]
                              ELSE /\ result_min' = a_[self]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ a_' = [a_ EXCEPT ![self] = Head(stack[self]).a_]
                        /\ b_' = [b_ EXCEPT ![self] = Head(stack[self]).b_]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << input_min_a, input_min_b, result_max, 
                                        a, b >>

generated_min(self) == generated_min_(self)

generated_max_(self) == /\ pc[self] = "generated_max_"
                        /\ IF a[self] < b[self]
                              THEN /\ result_max' = b[self]
                              ELSE /\ result_max' = a[self]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
                        /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << input_min_a, input_min_b, result_min, 
                                        a_, b_ >>

generated_max(self) == generated_max_(self)

min_ == /\ pc["min"] = "min_"
        /\ IF input_min_a > input_min_b
              THEN /\ result_min' = input_min_b
              ELSE /\ result_min' = input_min_a
        /\ pc' = [pc EXCEPT !["min"] = "Done"]
        /\ UNCHANGED << input_min_a, input_min_b, result_max, stack, a_, b_, a, 
                        b >>

min == min_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == min
           \/ (\E self \in ProcSet: generated_min(self) \/ generated_max(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
===============================================================================
