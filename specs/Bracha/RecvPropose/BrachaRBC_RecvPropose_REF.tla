---------------------- MODULE BrachaRBC_RecvPropose_REF ----------------------
EXTENDS BrachaRBC_RecvPropose_PCal

org_spec == INSTANCE BrachaRBC_RecvPropose WITH
    bcNode <- from,
    bcValue <- value,
    predicate <- [n \in CN |-> TRUE],
    msgs <- IF \A peer_node \in AN, correct_node \in CN: 
                {<<"ECHO", correct_node, value>>} \subseteq msgs[peer_node]
                THEN [t: {"ECHO"}, src: CN, v: {value}]
                ELSE {}


AbsStepNext == org_spec!RecvPropose([t |-> "PROPOSE", src |-> from, v |-> value])
AbsStepSpec == [][AbsStepNext]_<<>>

EventuallyStep == org_spec!Termination

TypeOK == org_spec!TypeOK

THEOREM Spec => /\ AbsStepSpec \* Safety
                /\ EventuallyStep \* Liveness

PROOF OMITTED \* Checked using TLC.
============================================================================
