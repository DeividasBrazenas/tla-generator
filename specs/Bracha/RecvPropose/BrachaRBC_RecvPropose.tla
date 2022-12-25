---------------------------- MODULE BrachaRBC_RecvPropose ----------------------------
EXTENDS FiniteSets, Naturals, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

VARIABLE bcNode     \* The broadcaster node.
VARIABLE bcValue    \* Value broadcasted by a correct BC node.
VARIABLE predicate  \* Predicates received by the nodes.
VARIABLE msgs       \* Messages that were sent.
vars == <<bcNode, bcValue, predicate, msgs>>

AN  == CN \cup FN       \* All nodes.

HaveProposeMsg(n, vs) == \E pm \in msgs : pm.t = "PROPOSE" /\ pm.src = n /\ pm.v \in vs
HaveEchoMsg   (n, vs) == \E em \in msgs : em.t = "ECHO"    /\ em.src = n /\ em.v \in vs
Msg == [t: {"PROPOSE", "ECHO", "READY"}, src: AN, v: Value \cup {NotValue}]

TypeOK ==
    /\ \/ msgs \subseteq Msg
       \/ msgs = {}
    /\ bcNode \in AN
    /\ \/ bcNode \in CN /\ bcValue \in Value
       \/ bcNode \in FN /\ bcValue = NotValue
    /\ predicate \in [CN -> BOOLEAN]

------------------------------------------------------------------------------------
(*
Actions.
*)

(*
>    6: upon receiving ⟨PROPOSE, 𝑀⟩ from the broadcaster do
>    7:     if 𝑃(𝑀) then
>    8:         send ⟨ECHO, 𝑀⟩ to all
*)
RecvPropose(pm) ==
    \E n \in CN:
        /\ predicate[n]
        /\ HaveProposeMsg(bcNode, {pm.v})
        /\ ~HaveEchoMsg(n, Value)
        /\ msgs' = msgs \cup {[t |-> "ECHO", src |-> n, v |-> pm.v]}
        /\ UNCHANGED <<bcNode, bcValue, predicate>>

------------------------------------------------------------------------------------
(*
The specification.
*)
Init ==
    /\ bcNode \in AN
    /\ \/ bcNode \in CN /\ bcValue \in Value
       \/ bcNode \in FN /\ bcValue = NotValue
    /\ predicate \in [CN -> {TRUE}]
    /\ msgs = [t: {"PROPOSE", "ECHO", "READY"}, src: AN, v: {bcValue}]

Next ==
    \/ \E pm \in msgs : RecvPropose(pm)

Fairness ==
    /\ WF_vars(\E pm \in msgs : pm.src \in CN  /\ RecvPropose(pm))

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------------

Termination ==
    <>(\A n \in CN : {[t |-> "ECHO", src |-> n, v |-> bcValue]} \subseteq msgs)

THEOREM SpecWorks ==
    Spec => /\ []TypeOK
            /\ Termination
PROOF OMITTED \* Checked using TLC.
===================================================================================