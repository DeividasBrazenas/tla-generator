---------------------------- MODULE BrachaRBC_Broadcast ----------------------------
EXTENDS FiniteSets, Naturals, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

VARIABLE bcNode     \* The broadcaster node.
VARIABLE bcValue    \* Value broadcasted by a correct BC node.
VARIABLE msgs       \* Messages that were sent.
vars == <<bcNode, bcValue, msgs>>

AN  == CN \cup FN       \* All nodes.

HaveProposeMsg(n, vs) == \E pm \in msgs : pm.t = "PROPOSE" /\ pm.src = n /\ pm.v \in vs
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
>    1: // only broadcaster node
>    2: input 𝑀
>    3: send ⟨PROPOSE, 𝑀⟩ to all
*)
Broadcast ==
    /\ bcNode \in CN \* We only care on the behaviour of the correct nodes.
    /\ ~HaveProposeMsg(bcNode, Value)
    /\ msgs' = msgs \cup {[t |-> "PROPOSE", src |-> bcNode, v |-> bcValue]}
    /\ UNCHANGED <<bcNode, bcValue>>

------------------------------------------------------------------------------------
(*
The specification.
*)
Init ==
    /\ bcNode \in AN
    /\ \/ bcNode \in CN /\ bcValue \in Value
       \/ bcNode \in FN /\ bcValue = NotValue
    /\ msgs = [t: {"PROPOSE", "ECHO", "READY"}, src: FN, v: Value \cup {NotValue}]

Next ==
    \/ Broadcast

Fairness ==
    /\ WF_vars(Broadcast)

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------------

Termination ==
    <>(\E m \in msgs : m.t = "PROPOSE" /\ m.src = bcNode /\ m.v = bcValue)

THEOREM SpecWorks ==
    Spec => /\ []TypeOK
            /\ Termination
PROOF OMITTED \* Checked using TLC.
===================================================================================