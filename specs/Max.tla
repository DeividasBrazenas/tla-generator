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
Invariant otherMax4IsMax is stable.
*)
LEMMA otherMax4SpecStableMax == otherMax4!Spec => [](otherMax4IsMax => []otherMax4IsMax)
  <1>1. otherMax4!Init /\ otherMax4IsMax => otherMax4IsMax
        OBVIOUS
  <1>2. otherMax4IsMax /\ [otherMax4!Next]_otherMax4X => otherMax4IsMax'
        BY otherMax4!Assms DEF Max, otherMax4IsMax, otherMax4!Next
  <1>q. QED BY <1>1, <1>2, PTL DEF otherMax4!Spec

(*
Prove the Max function refinement using a temporal (eventual) formulation.
In such case we would be not required to rely on some "DONE" flags.
*)
LEMMA otherMax4SpecEventuallyMax == otherMax4!Spec => <>otherMax4IsMax
  <1>1. SUFFICES ASSUME TRUE
                 PROVE (otherMax4!Spec /\ <>(otherMax4X = otherMax4!Null)) => <>otherMax4IsMax
        BY PTL DEF otherMax4!Spec, otherMax4!Init

  <1>x. ASSUME otherMax4!TypeOK, otherMax4!Spec
        PROVE ENABLED <<otherMax4!Next>>_otherMax4X
        <2> \E otherMax4X_1 : (/\ otherMax4X = otherMax4!Null
                               /\ \/ otherMax4A > otherMax4B /\ otherMax4X_1 = otherMax4A
                                  \/ otherMax4A =< otherMax4B /\ otherMax4X_1 = otherMax4B)
                               /\ ~otherMax4X_1 = otherMax4X
            <3>x. otherMax4X = otherMax4!Null
                  BY <1>x DEF otherMax4!Spec, otherMax4!Init
            <3>a. otherMax4A # otherMax4X
                  BY <3>x, NoSetContainsEverything, otherMax4!Assms DEF otherMax4!Null
            <3>b. otherMax4B # otherMax4X
                  BY <3>x, NoSetContainsEverything, otherMax4!Assms DEF otherMax4!Null
            <3>1. CASE otherMax4A > otherMax4B
                  <4> WITNESS otherMax4A
                  <4> QED BY <3>x, <3>a, <3>1, <1>x
            <3>2. CASE otherMax4A <= otherMax4B
                  <4> WITNESS otherMax4B
                  <4> QED BY <3>x, <3>b, <3>2, <1>x
            <3> QED BY <3>1, <3>2, otherMax4!Assms
        <2>q. QED BY ExpandENABLED DEF otherMax4!Next
  <1>y. ASSUME otherMax4!TypeOK, otherMax4!Spec
        PROVE <><<otherMax4!Next>>_otherMax4X
        <2>1. ENABLED <<otherMax4!Next>>_otherMax4X
              BY <1>x, <1>y
        <2>2. WF_otherMax4X(otherMax4!Next)
              BY <1>y DEF otherMax4!Spec, otherMax4!Live
        <2>3. WF_otherMax4X(otherMax4!Next) =>
                \/ []<>(~ENABLED <<otherMax4!Next>>_otherMax4X)
                \/ []<><<otherMax4!Next>>_otherMax4X
              BY PTL
        <2>4. WF_otherMax4X(otherMax4!Next) => []([](ENABLED <<otherMax4!Next>>_otherMax4X) => <><<otherMax4!Next>>_otherMax4X)
              BY PTL
        <2>q. QED BY <1>y, <2>1, <2>2, <2>3, PTL

  <1>2. otherMax4!Spec => [] \/ [](otherMax4X = otherMax4!Null)
                             \/ <>(otherMax4IsMax)
        OMITTED
    (*
    <2> DEFINE P == \/ [](otherMax4X = otherMax4!Null)
                    \/ <>(otherMax4IsMax)
    <2> HIDE DEF P
    <2>1. otherMax4!Init => P
    <2>2. P /\ [otherMax4!Next]_otherMax4X => P'
    <2>q. QED BY <2>1, <2>2, PTL DEF otherMax4!Spec
    *)
        (*
        <3>0. ASSUME otherMax4!TypeOK /\ [otherMax4!Next]_otherMax4X
              PROVE \/ (otherMax4X = otherMax4!Null)'
                    \/ otherMax4IsMax'
              <4> SUFFICES ASSUME otherMax4!TypeOK /\ otherMax4!Next
                           PROVE \/ otherMax4X' = otherMax4!Null
                                 \/ otherMax4IsMax'
                  BY <3>0 DEF otherMax4!Next
              <4>1. CASE otherMax4X = otherMax4!Null
                     BY <3>0, <4>1 DEF otherMax4!Next, otherMax4!TypeOK, otherMax4IsMax, Max
              <4>2. CASE otherMax4X # otherMax4!Null
                     BY <3>0, <4>2 DEF otherMax4!Next, otherMax4!TypeOK, otherMax4IsMax, Max
              <4>3. QED BY <4>1, <4>2
        *)
        (* 
        <3>1. SUFFICES ASSUME otherMax4!TypeOK /\ [otherMax4!Next]_otherMax4X
                       PROVE otherMax4X' = otherMax4!Null \/ (otherMax4IsMax')
              BY <3>1, otherMax4SpecTypeOK, PTL
              DEF otherMax4!Spec, otherMax4!Init, otherMax4!Next, otherMax4IsMax,
                  otherMax4!TypeOK
        *)
        (*
        <3>q. QED BY otherMax4SpecTypeOK, <3>0, PTL DEF otherMax4!Spec*)
        (*BY DEF otherMax4!Spec, otherMax4!Init, otherMax4!Next, otherMax4IsMax, Max*)
  <1>3. otherMax4!Spec => <><<otherMax4!Next>>_otherMax4X
        BY DEF otherMax4!Spec, otherMax4!Live, otherMax4!Init, otherMax4!Next
  <1>4. ASSUME otherMax4!TypeOK /\ (otherMax4X = otherMax4!Null) /\ <<otherMax4!Next>>_otherMax4X
        PROVE ~(otherMax4X = otherMax4!Null)'
        BY <1>4 DEF otherMax4!TypeOK, otherMax4!Next
  <1>q. QED BY otherMax4SpecTypeOK, <1>1, <1>2, <1>3, <1>4, PTL

THEOREM otherMax4SpecIsMaxAsProp == otherMax4!Spec => <>[]otherMax4IsMax
  BY otherMax4SpecEventuallyMax, otherMax4SpecStableMax, PTL


  
=============================================================================
