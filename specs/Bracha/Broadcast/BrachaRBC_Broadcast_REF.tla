---------------------- MODULE BrachaRBC_Broadcast_REF ----------------------
EXTENDS BrachaRBC_Broadcast_PCal

org_spec == INSTANCE BrachaRBC_Broadcast WITH
    bcNode <- bcNode,
    bcValue <- input,
    msgs <- IF \A n \in AN: msgs[n] = {[t |-> "PROPOSE", src |-> bcNode, v |-> input]}
                THEN {[t |-> "PROPOSE", src |-> bcNode, v |-> input]}
                ELSE {}

AbsStepNext == org_spec!Broadcast
AbsStepSpec == [][AbsStepNext]_<<>>

EventuallyStep == org_spec!Termination

TypeOK == org_spec!TypeOK

THEOREM Spec => /\ AbsStepSpec \* Safety
                /\ EventuallyStep \* Liveness

PROOF OMITTED \* Checked using TLC.
============================================================================
