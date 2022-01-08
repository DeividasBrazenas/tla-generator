-------------------------------- MODULE Max --------------------------------
EXTENDS Naturals, TLAPS

(*
Assume this spec is writted by a user.
*)
Max(a, b) ==
  IF a > b THEN a ELSE b 

MaxProps(M(_, _)) == \A a, b \in Nat:
    /\ M(a, b) >= a
    /\ M(a, b) >= b
THEOREM MaxIsGEQ == MaxProps(Max)
  BY DEF MaxProps, Max
-----------------------------------------------------------------------------
(*
Assume these specs are generated from the code (different possible versions).
*)
OtherMax1(a, b) ==
  IF a > b THEN a ELSE b 
THEOREM \A a, b \in Nat : OtherMax1(a, b) = Max(a, b)
  BY DEF Max, OtherMax1
THEOREM MaxProps(OtherMax1)
  BY DEF MaxProps, OtherMax1

-----------------------------------------------------------------------------
OtherMax2(a, b) ==
  CHOOSE x \in {a, b} : x = IF a >= b THEN a ELSE b
THEOREM \A a, b \in Nat : OtherMax2(a, b) = Max(a, b)
  BY DEF Max, OtherMax2
THEOREM MaxProps(OtherMax2)
  BY DEF MaxProps, OtherMax2

-----------------------------------------------------------------------------
OtherMax3(a, b) ==
  CHOOSE x \in Nat :
    \/ (a >  b) /\ x = a
    \/ (a <= b) /\ x = b
THEOREM \A a, b \in Nat : OtherMax3(a, b) = Max(a, b)
  BY DEF Max, OtherMax3
THEOREM MaxProps(OtherMax3)
  BY DEF MaxProps, OtherMax3
  
-----------------------------------------------------------------------------
---------- MODULE OtherMax4 ---------------
EXTENDS Naturals
CONSTANTS a, b
ASSUME a \in Nat /\ b \in Nat
VARIABLES x
Null == CHOOSE n : n \notin Nat
Init == x = Null
Next ==
 /\ x = Null
 /\ \/ a >  b /\ x' = a
    \/ a =< b /\ x' = b
Live == WF_x(Next)
Spec == Init /\ [][Next]_x /\ Live 
===========================================
CONSTANTS otherMax4A, otherMax4B
VARIABLE otherMax4X
ASSUME otherMax4Assms == otherMax4A \in Nat /\ otherMax4B \in Nat
otherMax4 == INSTANCE OtherMax4 WITH
  a <- otherMax4A,
  b <- otherMax4B,
  x <- otherMax4X

otherMax4IsMax == otherMax4X = Max(otherMax4A, otherMax4B)

THEOREM otherMax4!Spec => [](otherMax4X # otherMax4!Null => otherMax4IsMax)
  <1>1. otherMax4!Init => (otherMax4X # otherMax4!Null => otherMax4IsMax)
        BY DEF otherMax4IsMax, otherMax4!Init
  <1>2. /\ (otherMax4X # otherMax4!Null => otherMax4IsMax)
        /\ [otherMax4!Next]_otherMax4X
        => (otherMax4X # otherMax4!Null => otherMax4IsMax)'
    <2> SUFFICES ASSUME (otherMax4X # otherMax4!Null => otherMax4IsMax),
                        otherMax4!Next
                 PROVE (otherMax4X # otherMax4!Null => otherMax4IsMax)'
        BY DEF otherMax4IsMax
    <2> SUFFICES ASSUME otherMax4X' # otherMax4!Null PROVE otherMax4IsMax'
        BY DEF otherMax4IsMax
    <2>1. CASE otherMax4X = otherMax4!Null
      <3>1. CASE otherMax4A > otherMax4B
            BY <2>1, <3>1, otherMax4Assms
            DEF otherMax4!Next, otherMax4IsMax, Max
      <3>2. CASE otherMax4A =< otherMax4B
            BY <2>1, <3>2, otherMax4Assms
            DEF otherMax4!Next, otherMax4IsMax, Max
      <3>q. QED BY <2>1, <3>1, <3>2, otherMax4Assms
    <2>2. CASE otherMax4X # otherMax4!Null
          BY <2>2 DEF otherMax4!Next
    <2>q. QED BY <2>1, <2>2

  <1> QED BY <1>1, <1>2, PTL DEF otherMax4!Spec

THEOREM otherMax4!Spec => <>[]otherMax4IsMax
  BY DEF otherMax4IsMax, otherMax4!Spec, otherMax4!Next, otherMax4!Init, Max
  
=============================================================================
