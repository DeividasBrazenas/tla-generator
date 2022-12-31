---------------------- MODULE handle_echo_message_REF ----------------------
EXTENDS handle_echo_message

(*
    1. Result should exist for the node.
    2. ready_sent should be set to TRUE for the node.
    3.1. If ready message was sent earlier, then there should be no messages in result.
    3.2. If ready message was not sent earlier, then ready message should exist
         for every peer in the result.
*)
IsReadySent(res, node) ==
    /\ res[node] /= NULL
    /\ res[node][2].ready_sent = TRUE
    /\ \/ /\ readySent  
          /\ res[node][3] = [node_id \in AN |-> {}] 
       \/ /\ ~readySent
          /\ \A peer \in AN : {<<"READY", node, value>>} \subseteq res[node][3][peer] 

EnoughEchoMsgs(cn) == EchosCount(rbcs[cn].echo_recv) >= ((N + F) \div 2)

org_spec == INSTANCE BrachaRBC WITH
    bcNode <- bcNode,
    bcValue <- value,
    predicate <- [p \in CN |-> TRUE],
    output <- [o \in CN |-> NotValue],
    msgs <- IF \A cn \in CN : IsReadySent(result, cn)
                THEN [t: {"READY"}, src: CN, v: {value}]
                ELSE {}

QXF == {q \in SUBSET AN : Cardinality(q) = ((N + F) \div 2) + 1}  \* Intersection is F+1.

AbsStepNext == \E eq \in QXF : org_spec!RecvEcho(eq)
AbsStepSpec == [][AbsStepNext]_<<>> 

(*
    For every correct node:
    1.1. If there are enough echo messages received, the ready message should be sent.
    1.2. If there are not enough echo messages received, the ready message should not be sent.
*)
Liveness ==
    <>(\A cn \in CN :
        \/ /\ EnoughEchoMsgs(cn)
           /\ IsReadySent(result, cn)
        \/ /\ ~EnoughEchoMsgs(cn)
           /\ ~IsReadySent(result, cn))

TypeOK == org_spec!TypeOK

============================================================================
