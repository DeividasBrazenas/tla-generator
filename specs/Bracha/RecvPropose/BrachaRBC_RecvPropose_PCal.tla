--------------------- MODULE BrachaRBC_RecvPropose_PCal ---------------------
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC 

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

(*--algorithm BrachaRBC
variables
    from \in AN, 
    value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue}),
    rbcs = [node_id \in AN |-> [n |-> Cardinality(AN), 
           f |-> Cardinality(FN), 
           me |-> node_id, 
           peers |-> SetToSeq(AN), 
           broadcaster |-> from, 
           predicate |-> TRUE, 
           max_msg_size |-> 1000, 
           propose_sent |-> FALSE,
           echo_sent |-> FALSE,
           msg_recv |-> {}, 
           output |-> NotValue]], 
    msgs = [node_id \in AN |-> {}],
    msg = <<"PROPOSE", from, value>>
define
    AN  == CN \cup FN       \* All nodes.
    byte_size(x) == 0       \* Implement?
end define;

fair process handle_message \in CN
variables
    rbc = rbcs[self],
    me = rbcs[self].me,
    broadcaster = rbcs[self].broadcaster,
    peers = rbcs[self].peers,
    predicate = rbcs[self].predicate,
    output = rbcs[self].output,
    echo_sent = rbcs[self].echo_sent,
    max_msg_size = rbcs[self].max_msg_size,
    msg_recv = rbcs[self].msg_recv,
    peer_id,
    index = 1
begin
    handle_message:
        if msg[1] = "PROPOSE" /\ ~echo_sent /\ predicate then
            rbcs[self].echo_sent := TRUE || rbcs[self].msg_recv := rbcs[self].msg_recv \cup {<<from, "PROPOSE">>};
            iterate:
                while index <= Len(peers) do
                    peer_id := peers[index];
                    msgs[peer_id] := msgs[peer_id] \union {<<"ECHO", me, value>>};
                    index := index + 1;
                end while;
                output := output;
        end if;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cc0d70e1" /\ chksum(tla) = "b181dac3")
\* Label handle_message of process handle_message at line 46 col 9 changed to handle_message_
CONSTANT defaultInitValue
VARIABLES from, value, rbcs, msgs, msg, pc

(* define statement *)
AN  == CN \cup FN
byte_size(x) == 0

VARIABLES rbc, me, broadcaster, peers, predicate, output, echo_sent, 
          max_msg_size, msg_recv, peer_id, index

vars == << from, value, rbcs, msgs, msg, pc, rbc, me, broadcaster, peers, 
           predicate, output, echo_sent, max_msg_size, msg_recv, peer_id, 
           index >>

ProcSet == (CN)

Init == (* Global variables *)
        /\ from \in AN
        /\ value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue})
        /\ rbcs = [node_id \in AN |-> [n |-> Cardinality(AN),
                  f |-> Cardinality(FN),
                  me |-> node_id,
                  peers |-> SetToSeq(AN),
                  broadcaster |-> from,
                  predicate |-> TRUE,
                  max_msg_size |-> 1000,
                  propose_sent |-> FALSE,
                  echo_sent |-> FALSE,
                  msg_recv |-> {},
                  output |-> NotValue]]
        /\ msgs = [node_id \in AN |-> {}]
        /\ msg = <<"PROPOSE", from, value>>
        (* Process handle_message *)
        /\ rbc = [self \in CN |-> rbcs[self]]
        /\ me = [self \in CN |-> rbcs[self].me]
        /\ broadcaster = [self \in CN |-> rbcs[self].broadcaster]
        /\ peers = [self \in CN |-> rbcs[self].peers]
        /\ predicate = [self \in CN |-> rbcs[self].predicate]
        /\ output = [self \in CN |-> rbcs[self].output]
        /\ echo_sent = [self \in CN |-> rbcs[self].echo_sent]
        /\ max_msg_size = [self \in CN |-> rbcs[self].max_msg_size]
        /\ msg_recv = [self \in CN |-> rbcs[self].msg_recv]
        /\ peer_id = [self \in CN |-> defaultInitValue]
        /\ index = [self \in CN |-> 1]
        /\ pc = [self \in ProcSet |-> "handle_message_"]

handle_message_(self) == /\ pc[self] = "handle_message_"
                         /\ IF msg[1] = "PROPOSE" /\ ~echo_sent[self] /\ predicate[self]
                               THEN /\ rbcs' = [rbcs EXCEPT ![self].echo_sent = TRUE,
                                                            ![self].msg_recv = rbcs[self].msg_recv \cup {<<from, "PROPOSE">>}]
                                    /\ pc' = [pc EXCEPT ![self] = "iterate"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ rbcs' = rbcs
                         /\ UNCHANGED << from, value, msgs, msg, rbc, me, 
                                         broadcaster, peers, predicate, output, 
                                         echo_sent, max_msg_size, msg_recv, 
                                         peer_id, index >>

iterate(self) == /\ pc[self] = "iterate"
                 /\ IF index[self] <= Len(peers[self])
                       THEN /\ peer_id' = [peer_id EXCEPT ![self] = peers[self][index[self]]]
                            /\ msgs' = [msgs EXCEPT ![peer_id'[self]] = msgs[peer_id'[self]] \union {<<"ECHO", me[self], value>>}]
                            /\ index' = [index EXCEPT ![self] = index[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "iterate"]
                            /\ UNCHANGED output
                       ELSE /\ output' = [output EXCEPT ![self] = output[self]]
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << msgs, peer_id, index >>
                 /\ UNCHANGED << from, value, rbcs, msg, rbc, me, broadcaster, 
                                 peers, predicate, echo_sent, max_msg_size, 
                                 msg_recv >>

handle_message(self) == handle_message_(self) \/ iterate(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in CN: handle_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CN : WF_vars(handle_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
