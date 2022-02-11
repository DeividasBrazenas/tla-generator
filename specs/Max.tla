-------------------------------- MODULE Max --------------------------------
EXTENDS Naturals, TlaPS

(*
Assume this spec is writted by a user.
*)
Max(a, b) ==
  IF a > b THEN a ELSE b 

MaxProps(M(_, _)) == \A a, b \in Nat:
                       /\ M(a, b) >= a
                       /\ M(a, b) >= b
                       /\ M(a, b) \in Nat
                       /\ M(a, b) \in {a, b}
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
ASSUME Assms == a \in Nat /\ b \in Nat
VARIABLES x
Null == CHOOSE n : n \notin Nat
Init == x = Null
Next ==
 /\ x = Null
 /\ \/ a >  b /\ x' = a
    \/ a =< b /\ x' = b
Live == WF_x(Next)
Spec == Init /\ [][Next]_x /\ Live
TypeOK == x \in Nat \cup {Null}
===========================================
CONSTANTS otherMax4A, otherMax4B
VARIABLE otherMax4X
ASSUME otherMax4Assms == otherMax4A \in Nat /\ otherMax4B \in Nat
otherMax4 == INSTANCE OtherMax4 WITH
  a <- otherMax4A,
  b <- otherMax4B,
  x <- otherMax4X

otherMax4IsMax == otherMax4X = Max(otherMax4A, otherMax4B)

(*
In this case we prove that OtherMax4 refines (implements) the Max function
as a conditional invariant, that depends on some termination flag. In this
case the termination flag is otherMax4X # otherMax4!Null.
*)
THEOREM otherMax4SpecIsMaxAsInv == otherMax4!Spec => [](otherMax4X # otherMax4!Null => otherMax4IsMax)
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
  <1>q. QED BY <1>1, <1>2, PTL DEF otherMax4!Spec

(*
Type correctness.
*)
LEMMA otherMax4SpecTypeOK == otherMax4!Spec => []otherMax4!TypeOK
  <1>1. otherMax4!Init => otherMax4!TypeOK
        BY DEF otherMax4!Init, otherMax4!TypeOK
  <1>2. otherMax4!TypeOK /\ [otherMax4!Next]_otherMax4X => otherMax4!TypeOK'
        BY otherMax4!Assms DEF otherMax4!TypeOK, otherMax4!Next
  <1>q. QED BY <1>1, <1>2, PTL DEF otherMax4!Spec

(*
Invariant: otherMax4IsMax is stable.
*)
LEMMA otherMax4SpecStableMax == otherMax4!Spec => [](otherMax4IsMax => []otherMax4IsMax)
  <1>1. otherMax4!Init /\ otherMax4IsMax => otherMax4IsMax
        OBVIOUS
  <1>2. otherMax4IsMax /\ [otherMax4!Next]_otherMax4X => otherMax4IsMax'
        BY otherMax4!Assms DEF Max, otherMax4IsMax, otherMax4!Next
  <1>q. QED BY <1>1, <1>2, PTL DEF otherMax4!Spec

(*
Invariant: Either X = Null XOR X = Max(A, B)
*)
otherMax4XInv ==
  /\ (otherMax4X = otherMax4!Null) # otherMax4IsMax
  /\ (otherMax4X = otherMax4!Null) \in BOOLEAN
  /\ otherMax4IsMax \in BOOLEAN
LEMMA otherMax4SpecXInv == otherMax4!Spec => []otherMax4XInv
  <1>0. (otherMax4X # otherMax4!Null) \in BOOLEAN OBVIOUS
  <1>x. otherMax4IsMax \in BOOLEAN BY DEF otherMax4IsMax
  <1>1. otherMax4!Init => otherMax4XInv
        <2>0. SUFFICES ASSUME otherMax4!Init PROVE otherMax4XInv OBVIOUS
        <2>1. otherMax4X = otherMax4!Null BY <2>0 DEF otherMax4!Init
        <2>2. ~otherMax4IsMax
              BY <2>1, otherMax4!Assms, NoSetContainsEverything, MaxIsGEQ
              DEF otherMax4IsMax, MaxProps, otherMax4!Null  
        <2>q. QED BY <2>1, <2>2, <1>0, <1>x DEF otherMax4XInv
  <1>2. otherMax4XInv /\ [otherMax4!Next]_otherMax4X => otherMax4XInv'
        <2>1. SUFFICES ASSUME otherMax4XInv, otherMax4!Next PROVE otherMax4XInv'
              BY DEF otherMax4!Next, otherMax4XInv, otherMax4IsMax, Max
        <2>2. CASE otherMax4X = otherMax4!Null /\ ~otherMax4IsMax 
              BY <2>1, <2>2, otherMax4!Assms
              DEF otherMax4IsMax, Max, otherMax4!Next, otherMax4XInv
        <2>3. CASE otherMax4X # otherMax4!Null /\ otherMax4IsMax
              BY <2>1, <2>3, otherMax4!Assms
              DEF otherMax4IsMax, Max, otherMax4!Next, otherMax4XInv
        <2>4. QED BY <2>1, <2>2, <2>3, <1>0, <1>x, otherMax4!Assms DEF otherMax4XInv
  <1>q. QED BY <1>1, <1>2, PTL DEF otherMax4!Spec

(*
Prove the Max function refinement using a temporal (eventual) formulation.
In such case we would be not required to rely on some "DONE" flags.

NOTE: This proof might require TLAPS from the updated_enabled_cdot branch (if not merged yet).
      That's because we use ExpandENABLED proof rule.
*)
LEMMA otherMax4SpecEventuallyMax == otherMax4!Spec => <>otherMax4IsMax
  <1>1. otherMax4!Spec => [](<>otherMax4IsMax \/ <><<otherMax4!Next>>_otherMax4X)
        <2> DEFINE P == otherMax4IsMax \/ ENABLED <<otherMax4!Next>>_otherMax4X
        <2> HIDE DEF P
        <2>1. otherMax4!Spec => []P
              <3>1. otherMax4!Init => P
                    <4>1. SUFFICES ASSUME otherMax4!Init PROVE P OBVIOUS
                    <4>2. SUFFICES ASSUME ~otherMax4IsMax PROVE ENABLED <<otherMax4!Next>>_otherMax4X
                          BY DEF P
                    <4>3. otherMax4X = otherMax4!Null BY <4>1 DEF otherMax4!Init
                    <4>4. otherMax4A \in Nat /\ otherMax4B \in Nat /\ otherMax4!Null \notin Nat
                          BY otherMax4!Assms, NoSetContainsEverything DEF otherMax4!Null
                    <4>5. SUFFICES ASSUME TRUE PROVE \E otherMax4X_1 : (
                            /\ otherMax4X = otherMax4!Null
                            /\ \/ otherMax4A >  otherMax4B /\ otherMax4X_1 = otherMax4A
                               \/ otherMax4A =< otherMax4B /\ otherMax4X_1 = otherMax4B
                          ) /\ ~otherMax4X_1 = otherMax4X
                          BY ExpandENABLED DEF otherMax4!Next
                    <4>6. CASE otherMax4A > otherMax4B
                          <5>1. WITNESS otherMax4A
                          <5>2. QED BY <5>1, <4>3, <4>4, <4>6
                    <4>7. CASE otherMax4A <= otherMax4B
                          <5>1. WITNESS otherMax4B
                          <5>2. QED BY <5>1, <4>3, <4>4, <4>7
                    <4>8. QED BY <4>6, <4>7, otherMax4!Assms
              <3>2. otherMax4!TypeOK /\ otherMax4XInv /\ P /\ [otherMax4!Next]_otherMax4X /\ otherMax4XInv' => P'
                    <4>1. SUFFICES ASSUME otherMax4!TypeOK,
                                          otherMax4XInv,
                                          P,
                                          otherMax4X = otherMax4X' \/ otherMax4!Next,
                                          otherMax4XInv'
                                   PROVE P'
                          OBVIOUS
                    <4>2. CASE otherMax4X = otherMax4!Null
                          <5>2. CASE otherMax4X = otherMax4X'
                                <6>0. otherMax4X' = otherMax4!Null BY <4>2, <5>2
                                <6>1. SUFFICES ASSUME TRUE PROVE (ENABLED <<otherMax4!Next>>_otherMax4X)'
                                      BY DEF P
                                <6>2. SUFFICES ASSUME TRUE PROVE \E otherMax4X_1 : (
                                        /\ otherMax4X' = otherMax4!Null
                                        /\ \/ otherMax4A > otherMax4B /\ otherMax4X_1 = otherMax4A
                                           \/ otherMax4A =< otherMax4B /\ otherMax4X_1 = otherMax4B
                                        ) /\ ~otherMax4X_1 = otherMax4X'
                                      BY <6>2, ExpandENABLED DEF otherMax4!Next
                                <6>3. otherMax4A' \in Nat /\ otherMax4B \in Nat /\ otherMax4!Null \notin Nat
                                      BY otherMax4!Assms, NoSetContainsEverything DEF otherMax4!Null
                                <6>a. CASE otherMax4A > otherMax4B
                                      <7>1. WITNESS otherMax4A
                                      <7>2. QED BY <7>1, <6>0, <6>a, <6>3
                                <6>b. CASE otherMax4A <= otherMax4B
                                      <7>1. WITNESS otherMax4B
                                      <7>2. QED BY <7>1, <6>0, <6>b, <6>3
                                <6>q. QED  BY <6>a, <6>b, otherMax4!Assms
                          <5>3. CASE otherMax4X # otherMax4X'
                                <6>1. otherMax4X' # otherMax4!Null BY <4>2, <5>3
                                <6>2. QED BY <6>1, <4>1, <4>2 DEF P, otherMax4IsMax, otherMax4XInv
                          <5>q. QED BY <5>2, <5>3
                    <4>3. CASE otherMax4IsMax
                          <5>1. otherMax4X # otherMax4!Null BY <4>1, <4>3 DEF otherMax4XInv
                          <5>2. ~otherMax4!Next BY <5>1 DEF otherMax4!Next 
                          <5>3. otherMax4X = otherMax4X' BY <5>2, <4>1
                          <5>4. otherMax4IsMax' BY <5>3, <4>3 DEF otherMax4IsMax 
                          <5>q. QED BY <5>4 DEF P
                    <4>q. QED BY <4>1, <4>2, <4>3 DEF otherMax4XInv
              <3>q. QED BY <3>1, <3>2, PTL, otherMax4SpecXInv, otherMax4SpecTypeOK DEF otherMax4!Spec
        <2>2. otherMax4!Spec => [](WF_otherMax4X(otherMax4!Next) => (<>otherMax4IsMax \/ <><<otherMax4!Next>>_otherMax4X))
              BY <2>1, PTL, otherMax4SpecTypeOK DEF P, otherMax4!Spec, otherMax4!Live
        <2>3. QED BY <2>1, <2>2, PTL DEF otherMax4!Spec, otherMax4!Live
  <1>2. ASSUME otherMax4!TypeOK, ~otherMax4IsMax, <<otherMax4!Next>>_otherMax4X PROVE otherMax4IsMax'
        BY <1>2, otherMax4!Assms
        DEF  otherMax4IsMax, Max, otherMax4!Next, otherMax4!TypeOK, otherMax4!Null
  <1>3. QED BY <1>1, <1>2, PTL, otherMax4SpecTypeOK

THEOREM otherMax4SpecIsMaxAsProp == otherMax4!Spec => <>[]otherMax4IsMax
  BY otherMax4SpecEventuallyMax, otherMax4SpecStableMax, PTL
  
=============================================================================
