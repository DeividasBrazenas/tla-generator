---------------------- MODULE handle_propose_message_REF ----------------------
EXTENDS handle_propose_message

(*
    1. Result should exist for the node.
    2. echo_sent should be set to TRUE for the node.
    3.1. If echo message was sent earlier, then there should be no messages in result.
    3.2. If echo message was not sent earlier, then echo message should exist
         for every peer in the result.
*)
IsEchoSent(res, node) ==
    /\ res[node] /= NULL
    /\ res[node][2].echo_sent = TRUE
    /\ \/ /\ echoSent
          /\ res[node][3] = [node_id \in AN |-> {}]
       \/ /\ ~echoSent 
          /\ \A peer \in AN : {<<"ECHO", node, bcValue>>} \subseteq res[node][3][peer]

org_spec == INSTANCE BrachaRBC WITH
    bcNode <- bcNode,
    bcValue <- bcValue,
    predicate <- [p \in CN |-> TRUE],
    output <- [o \in CN |-> NotValue],
    msgs <- IF \A n \in CN : IsEchoSent(result, n)
                THEN [t: {"ECHO"}, src: CN, v: {bcValue}]
                ELSE {}

AbsStepNext == org_spec!RecvPropose([t |-> _msg[1], src |-> _msg[2], v |-> _msg[3]])
AbsStepSpec == [][AbsStepNext]_<<>>

(*
    For every correct node:
    1. The echo messsage should be sent.
*)
Liveness == <>(\A n \in CN : 
                IsEchoSent(result, n))

TypeOK == org_spec!TypeOK

THEOREM Spec =>
    /\ []TypeOK
    /\ AbsStepSpec
    /\ Liveness
PROOF OMITTED \* Checked by the TLC.

============================================================================
