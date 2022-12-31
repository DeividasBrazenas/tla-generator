---------------------- MODULE handle_input_REF ----------------------
EXTENDS handle_input

(*
    1. Result should exist for the broadcaster node.
    2. propose_sent should be set to TRUE in the broadcaster node.
    3. propose message should be sent to all peers from the broadcaster node.
*)
IsProposeSent(res, node) ==   
    /\ res[node] /= NULL
    /\ res[node][2].propose_sent = TRUE
    /\ \A peer \in AN: {<<"PROPOSE", node, input>>} \subseteq res[node][3][peer]

org_spec == INSTANCE BrachaRBC WITH
    bcNode <- bcNode,
    bcValue <- input,
    predicate <- [p \in CN |-> TRUE],
    output <- [o \in CN |-> NotValue],
    msgs <- IF IsProposeSent(result, bcNode)
                THEN {[t |-> "PROPOSE", src |-> bcNode, v |-> input]}
                ELSE {}

AbsStepNext == org_spec!Broadcast
AbsStepSpec == [][AbsStepNext]_<<>>

(*
    1. The propose should be sent from the broadcaster node.
*)
Liveness ==
    \/ <>IsProposeSent(result, bcNode)

TypeOK == org_spec!TypeOK

============================================================================
