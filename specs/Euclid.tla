-------------------- MODULE Euclid --------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS in_a, in_b

(*--algorithm Euclid
  variable result

procedure gcd(a, b)
begin
  gcd:
    if (a < b) then
      call gcd(a, b - a)
    elsif (a > b) then
      call gcd(a - b, b)
    else
      result := a;
      return;
    end if;
end procedure

begin
    gcd:
        if result = defaultInitValue then
            call gcd(in_a, in_b)
        end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "e1d79777" /\ chksum(tla) = "ce0b4c10")
\* Label gcd of procedure gcd at line 11 col 5 changed to gcd_
\* Label gcd at line 23 col 9 changed to gcd_1
CONSTANT defaultInitValue
VARIABLES result, pc, stack, a, b

vars == << result, pc, stack, a, b >>

Init == (* Global variables *)
        /\ result = defaultInitValue
        (* Procedure gcd *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        /\ stack = << >>
        /\ pc = "gcd_1"

gcd_ == /\ pc = "gcd_"
        /\ IF (a < b)
              THEN /\ /\ a' = a
                      /\ b' = b - a
                      /\ stack' = << [ procedure |->  "gcd",
                                       pc        |->  "Error",
                                       a         |->  a,
                                       b         |->  b ] >>
                                   \o stack
                   /\ pc' = "gcd_"
                   /\ UNCHANGED result
              ELSE /\ IF (a > b)
                         THEN /\ /\ a' = a - b
                                 /\ b' = b
                                 /\ stack' = << [ procedure |->  "gcd",
                                                  pc        |->  "Error",
                                                  a         |->  a,
                                                  b         |->  b ] >>
                                              \o stack
                              /\ pc' = "gcd_"
                              /\ UNCHANGED result
                         ELSE /\ result' = a
                              /\ pc' = Head(stack).pc
                              /\ a' = Head(stack).a
                              /\ b' = Head(stack).b
                              /\ stack' = Tail(stack)

gcd == gcd_

gcd_1 == /\ pc = "gcd_1"
         /\ IF result = defaultInitValue
               THEN /\ /\ a' = in_a
                       /\ b' = in_b
                       /\ stack' = << [ procedure |->  "gcd",
                                        pc        |->  "Done",
                                        a         |->  a,
                                        b         |->  b ] >>
                                    \o stack
                    /\ pc' = "gcd_"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << stack, a, b >>
         /\ UNCHANGED result

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == gcd \/ gcd_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=======================================================
