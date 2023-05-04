---------------------- MODULE handle_ready_message_REF ----------------------
EXTENDS handle_ready_message

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
          /\ \A peer \in AN : {<<"READY", node, bcValue>>} \subseteq res[node][3][peer] 

IsOutputSet(res, node) ==
    \* result should exist for node
    /\ res[node] /= NULL
    \* output should be set to value
    /\ res[node][4] = bcValue

EnoughReadyMsgs(cn) == ReadyCount(rbcs[cn].ready_recv) >= F
EnoughReadyMsgsForOutput(cn) == ReadyCount(rbcs[cn].ready_recv) >= 3 * F

org_spec == INSTANCE BrachaRBC WITH
    bcNode <- bcNode,
    bcValue <- bcValue,
    predicate <- [cn \in CN |-> TRUE],
    output <- IF \A cn \in CN : IsOutputSet(result, cn)
                THEN [node \in CN |-> bcValue]
                ELSE [node \in CN |-> NotValue],
    msgs <- IF \A cn \in CN : IsReadySent(result, cn)
                THEN [t: {"READY"}, src: CN, v: {bcValue}]
                ELSE {}

Q1F == {q \in SUBSET AN : Cardinality(q) = F+1}     \* Contains >= 1 correct node.
Q2F == {q \in SUBSET AN : Cardinality(q) = 2*F+1}   \* Contains >= F+1 correct nodes.

AbsStepNext ==     
    \/ \E rq \in Q1F  : org_spec!RecvReadySupport(rq)
    \/ \E rq \in Q2F  : org_spec!RecvReadyOutput(rq)
AbsStepSpec == [][AbsStepNext]_<<>>

(*
    For every correct node:
    1.1. If there are enough ready messages received, the ready message should be sent.
    1.2. If there are not enough ready messages received, the ready message should not be sent.
    2.1. If there are enough ready messages received, the output should be set.
    2.2. If there are not enough ready messages received, the output should not be set.
*)
Liveness ==
    <>(\A cn \in CN :
        /\  \/  /\ EnoughReadyMsgs(cn)
                /\ IsReadySent(result, cn)
            \/  /\ ~EnoughReadyMsgs(cn)
                /\ ~IsReadySent(result, cn)
        /\  \/  /\ EnoughReadyMsgsForOutput(cn)
                /\ IsOutputSet(result, cn)
            \/  /\ ~EnoughReadyMsgsForOutput(cn)
                /\ ~IsOutputSet(result, cn))

TypeOK == org_spec!TypeOK

THEOREM Spec =>
    /\ []TypeOK
    /\ AbsStepSpec
    /\ Liveness
PROOF OMITTED \* Checked by the TLC.
============================================================================
