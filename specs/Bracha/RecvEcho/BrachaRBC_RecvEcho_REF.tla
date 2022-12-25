---------------------- MODULE BrachaRBC_RecvEcho_REF ----------------------
EXTENDS BrachaRBC_RecvEcho_PCal

org_spec == INSTANCE BrachaRBC_RecvEcho WITH
    bcNode <- from,
    bcValue <- value,
    echosExist <- \* TODO
    msgs <- IF \A peer_node \in AN, correct_node \in CN: 
                {<<"READY", correct_node, value>>} \subseteq msgs[peer_node]
                THEN [t: {"READY"}, src: CN, v: {value}]
                ELSE {}
                    
N   == Cardinality(AN)  \* Number of nodes in the system.
F   == Cardinality(FN)  \* Number of faulty nodes.

FQX == {q \in SUBSET AN : Cardinality(q) = ((N+F) \div 2) + 1}  \* Intersection is F+1.

AbsStepNext ==  \E x \in FQX: org_spec!RecvEcho(x)
AbsStepSpec == [][AbsStepNext]_<<>>

EventuallyStep == org_spec!Termination

TypeOK == org_spec!TypeOK

THEOREM Spec => /\ AbsStepSpec \* Safety
                /\ EventuallyStep \* Liveness

PROOF OMITTED \* Checked using TLC.
============================================================================
