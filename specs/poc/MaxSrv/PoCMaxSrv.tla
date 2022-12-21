------------------------------ MODULE PoCMaxSrv --------------------------------
(*
This spec represents the abstract algorithm. We want to show, that the program
actually implements this spec (program refines this spec).
*)
EXTENDS Naturals
VARIABLE params
VARIABLE output
VARIABLE msgs
vars == <<params, output, msgs>>

Value == Nat
Null == CHOOSE nv : nv \notin Value
Msg == UNION {
    [t: {"req"}, items: SUBSET Value],
    [t: {"res"}, max: Value]
}

TypeOK ==
    /\ params \subseteq Value
    /\ output \in Value \cup {Null}

--------------------------------------------------------------------------------
Req ==
    /\ ~\E m \in msgs : m.t = "req"
    /\ msgs' = msgs \cup {[t |-> "req", items |-> params]}
    /\ UNCHANGED <<params, output>>

Srv ==
    /\ ~\E m \in msgs: m.t = "res"
    /\ \E m \in msgs:
        /\ m.t = "req"
        /\ msgs' = msgs \cup {[t |-> "res", max |-> CHOOSE max \in m.items: \A i \in m.items: max >= i]}
    /\ UNCHANGED <<params, output>>

Res ==
    \E m \in msgs :
        /\ m.t = "res"
        /\ output = Null
        /\ output' = m.max
        /\ UNCHANGED <<params, msgs>>

--------------------------------------------------------------------------------
Init ==
    /\ params \in SUBSET Value /\ \E x \in params : TRUE \* Non-empty.
    /\ output = Null
    /\ msgs = {}
Next ==
    \/ Req
    \/ Srv
    \/ Res
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------------------------------------------------------------
IsMax(val) == val \in params /\ \A p \in params: val >= p

MaxReturned ==
    <>[](output # Null /\ IsMax(output))

(*
Both probably OK, the V2 looks simpler.
*)
SrvTerminationV1 ==
    /\ <>ENABLED Srv
    /\ ENABLED Srv ~> \E m \in msgs : m.t = "res" /\ IsMax(m.max)
SrvTerminationV2 ==
    <>(\E m \in msgs : m.t = "res" /\ IsMax(m.max))
SrvTermination == SrvTerminationV1 /\ SrvTerminationV2

THEOREM SpecMaxReturned ==
    Spec => /\ []TypeOK
            /\ MaxReturned
            /\ SrvTermination
PROOF OMITTED \* Checked using TLC.
================================================================================
