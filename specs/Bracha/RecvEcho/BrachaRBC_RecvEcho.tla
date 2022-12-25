---------------------------- MODULE BrachaRBC_RecvEcho ----------------------------
EXTENDS FiniteSets, Naturals, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

VARIABLE bcNode     \* The broadcaster node.
VARIABLE bcValue    \* Value broadcasted by a correct BC node.
VARIABLE msgs       \* Messages that were sent.
VARIABLE echosExist
vars == <<bcNode, bcValue, msgs, echosExist>>

AN  == CN \cup FN       \* All nodes.
N   == Cardinality(AN)  \* Number of nodes in the system.
F   == Cardinality(FN)  \* Number of faulty nodes.
QXF == {q \in SUBSET AN : Cardinality(q) = ((N+F) \div 2) + 1}  \* Intersection is F+1.

HaveEchoMsg   (n, vs) == \E em \in msgs : em.t = "ECHO"    /\ em.src = n /\ em.v \in vs
HaveReadyMsg  (n, vs) == \E rm \in msgs : rm.t = "READY"   /\ rm.src = n /\ rm.v \in vs
Msg == [t: {"PROPOSE", "ECHO", "READY"}, src: AN, v: Value \cup {NotValue}]

TypeOK ==
    /\ \/ msgs \subseteq Msg
       \/ msgs = {}
    /\ bcNode \in AN
    /\ \/ bcNode \in CN /\ bcValue \in Value
       \/ bcNode \in FN /\ bcValue = NotValue

------------------------------------------------------------------------------------
(*
Actions.
*)

(*
>    9: upon receiving 2𝑡 + 1 ⟨ECHO, 𝑀⟩ messages and not having sent a READY message do
>   10:     send ⟨READY, 𝑀⟩ to all
*)
RecvEcho(eq) ==
    \E n \in CN, v \in Value :
        /\ eq \in QXF
        /\ \A qn \in eq : HaveEchoMsg(qn, {v})
        /\ ~HaveReadyMsg(n, Value)
        /\ msgs' = msgs \cup {[t |-> "READY", src |-> n, v |-> v]}
        /\ UNCHANGED <<bcNode, bcValue, echosExist>>
------------------------------------------------------------------------------------
(*
The specification.
*)
Init ==
    /\ bcNode \in AN
    /\ \/ bcNode \in CN /\ bcValue \in Value
       \/ bcNode \in FN /\ bcValue = NotValue
    /\ echosExist \in BOOLEAN
    /\ \/ echosExist /\ msgs = [t: {"PROPOSE", "ECHO"}, src: CN, v: {bcValue}]
       \/ ~echosExist /\ msgs = [t: {"PROPOSE"}, src: CN, v: {bcValue}]

Next ==
    \/ \E eq \in QXF  : RecvEcho(eq)

Fairness ==
    /\ WF_vars(\E eq \in QXF  : eq \subseteq CN /\ RecvEcho(eq))

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------------

Termination ==
    \/ <>(\A n \in CN : {[t |-> "READY", src |-> n, v |-> bcValue]} \subseteq msgs) 
    \/ ~echosExist 
    \/ {bcNode} \subseteq FN

THEOREM SpecWorks ==
    Spec => /\ []TypeOK
            /\ Termination
PROOF OMITTED \* Checked using TLC.
===================================================================================