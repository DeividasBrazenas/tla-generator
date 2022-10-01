---------------------------- MODULE GeneratedMax ----------------------------
EXTENDS Naturals, Sequences
CONSTANTS in_a, in_b

(*--algorithm Max

variable result

procedure GeneratedMax(a, b)
begin
  GeneratedMax:
    if a > b then 
      result := a;
    else
      result := b;
    end if;
    return;
end procedure

begin
    Max:
        if result = defaultInitValue then
            call GeneratedMax(in_a, in_b)
        end if;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "b268d7d4" /\ chksum(tla) = "3d07c98c")
\* Label GeneratedMax of procedure GeneratedMax at line 12 col 5 changed to GeneratedMax_
CONSTANT defaultInitValue
VARIABLES result, pc, stack, a, b

vars == << result, pc, stack, a, b >>

Init == (* Global variables *)
        /\ result = defaultInitValue
        (* Procedure GeneratedMax *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        /\ stack = << >>
        /\ pc = "Max"

GeneratedMax_ == /\ pc = "GeneratedMax_"
                 /\ IF a > b
                       THEN /\ result' = a
                       ELSE /\ result' = b
                 /\ pc' = Head(stack).pc
                 /\ a' = Head(stack).a
                 /\ b' = Head(stack).b
                 /\ stack' = Tail(stack)

GeneratedMax == GeneratedMax_

Max == /\ pc = "Max"
       /\ IF result = defaultInitValue
             THEN /\ /\ a' = in_a
                     /\ b' = in_b
                     /\ stack' = << [ procedure |->  "GeneratedMax",
                                      pc        |->  "Done",
                                      a         |->  a,
                                      b         |->  b ] >>
                                  \o stack
                  /\ pc' = "GeneratedMax_"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << stack, a, b >>
       /\ UNCHANGED result

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == GeneratedMax \/ Max
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

===========================================
