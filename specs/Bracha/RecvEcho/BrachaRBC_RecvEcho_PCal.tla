--------------------- MODULE BrachaRBC_RecvEcho_PCal ---------------------
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC 

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue
CONSTANT NULL

(*--algorithm BrachaRBC
variables
    from \in AN, 
    value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue}),
    echo_recv_value \in BOOLEAN \cup {NULL},
    rbcs = [node_id \in AN |-> [
        n |-> Cardinality(AN), 
        f |-> Cardinality(FN), 
        me |-> node_id, 
        peers |-> SetToSeq(AN), 
        broadcaster |-> from, 
        predicate |-> TRUE, 
        max_msg_size |-> 1000, 
        propose_sent |-> FALSE,
        echo_sent |-> FALSE,
        ready_sent |-> FALSE,
        msg_recv |-> {},
        echo_recv |-> [v \in AllValues |-> [x \in CN |-> echo_recv_value]],
        output |-> NotValue]], 
    msgs = [node_id \in AN |-> {}],
    msg = <<"ECHO", from, value>>

define
    AN  == CN \cup FN       \* All nodes.
    AllValues == Value \cup {NotValue}
    map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL}) 
end define;

fair process handle_message \in CN
variables
    me = rbcs[self].me,
    n = rbcs[self].n,
    f = rbcs[self].f,
    peers = rbcs[self].peers,
    msg_recv = rbcs[self].msg_recv,
    echo_recv = rbcs[self].echo_recv,
    ready_sent = rbcs[self].ready_sent,
    output = rbcs[self].output,
    existing_recv,
    new_recv,
    peer_id,
    index = 1
begin
    handle_message:
        if msg[1] = "ECHO" then
            existing_recv := echo_recv[value];
            double_assignment:
                existing_recv[from] := TRUE;
                new_recv := existing_recv;
            
                echo_recv[value] := new_recv;

                rbcs[self].echo_recv := echo_recv;

                if ~ready_sent /\ map_size(echo_recv[value]) > (n + f) \div 2 then
                    ooo:
                    rbcs[self].ready_sent := TRUE || rbcs[self].msg_recv := rbcs[self].msg_recv \cup {<<from, "ECHO">>};
                    iterate:
                        while index <= Len(peers) do
                            peer_id := peers[index];
                            msgs[peer_id] := msgs[peer_id] \union {<<"READY", me, value>>};
                            index := index + 1;
                        end while;
                        output := output;
                 end if;

        end if;
    
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "36691a30" /\ chksum(tla) = "54c294b1")
\* Label handle_message of process handle_message at line 54 col 9 changed to handle_message_
CONSTANT defaultInitValue
VARIABLES from, value, echo_recv_value, rbcs, msgs, msg, pc

(* define statement *)
AN  == CN \cup FN
AllValues == Value \cup {NotValue}
map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})

VARIABLES me, n, f, peers, msg_recv, echo_recv, ready_sent, output, 
          existing_recv, new_recv, peer_id, index

vars == << from, value, echo_recv_value, rbcs, msgs, msg, pc, me, n, f, peers, 
           msg_recv, echo_recv, ready_sent, output, existing_recv, new_recv, 
           peer_id, index >>

ProcSet == (CN)

Init == (* Global variables *)
        /\ from \in AN
        /\ value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue})
        /\ echo_recv_value \in (BOOLEAN \cup {NULL})
        /\ rbcs =    [node_id \in AN |-> [
                  n |-> Cardinality(AN),
                  f |-> Cardinality(FN),
                  me |-> node_id,
                  peers |-> SetToSeq(AN),
                  broadcaster |-> from,
                  predicate |-> TRUE,
                  max_msg_size |-> 1000,
                  propose_sent |-> FALSE,
                  echo_sent |-> FALSE,
                  ready_sent |-> FALSE,
                  msg_recv |-> {},
                  echo_recv |-> [v \in AllValues |-> [x \in CN |-> echo_recv_value]],
                  output |-> NotValue]]
        /\ msgs = [node_id \in AN |-> {}]
        /\ msg = <<"ECHO", from, value>>
        (* Process handle_message *)
        /\ me = [self \in CN |-> rbcs[self].me]
        /\ n = [self \in CN |-> rbcs[self].n]
        /\ f = [self \in CN |-> rbcs[self].f]
        /\ peers = [self \in CN |-> rbcs[self].peers]
        /\ msg_recv = [self \in CN |-> rbcs[self].msg_recv]
        /\ echo_recv = [self \in CN |-> rbcs[self].echo_recv]
        /\ ready_sent = [self \in CN |-> rbcs[self].ready_sent]
        /\ output = [self \in CN |-> rbcs[self].output]
        /\ existing_recv = [self \in CN |-> defaultInitValue]
        /\ new_recv = [self \in CN |-> defaultInitValue]
        /\ peer_id = [self \in CN |-> defaultInitValue]
        /\ index = [self \in CN |-> 1]
        /\ pc = [self \in ProcSet |-> "handle_message_"]

handle_message_(self) == /\ pc[self] = "handle_message_"
                         /\ IF msg[1] = "ECHO"
                               THEN /\ existing_recv' = [existing_recv EXCEPT ![self] = echo_recv[self][value]]
                                    /\ pc' = [pc EXCEPT ![self] = "double_assignment"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED existing_recv
                         /\ UNCHANGED << from, value, echo_recv_value, rbcs, 
                                         msgs, msg, me, n, f, peers, msg_recv, 
                                         echo_recv, ready_sent, output, 
                                         new_recv, peer_id, index >>

double_assignment(self) == /\ pc[self] = "double_assignment"
                           /\ existing_recv' = [existing_recv EXCEPT ![self][from] = TRUE]
                           /\ new_recv' = [new_recv EXCEPT ![self] = existing_recv'[self]]
                           /\ echo_recv' = [echo_recv EXCEPT ![self][value] = new_recv'[self]]
                           /\ rbcs' = [rbcs EXCEPT ![self].echo_recv = echo_recv'[self]]
                           /\ IF ~ready_sent[self] /\ map_size(echo_recv'[self][value]) > (n[self] + f[self]) \div 2
                                 THEN /\ pc' = [pc EXCEPT ![self] = "ooo"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << from, value, echo_recv_value, msgs, 
                                           msg, me, n, f, peers, msg_recv, 
                                           ready_sent, output, peer_id, index >>

ooo(self) == /\ pc[self] = "ooo"
             /\ rbcs' = [rbcs EXCEPT ![self].ready_sent = TRUE,
                                     ![self].msg_recv = rbcs[self].msg_recv \cup {<<from, "ECHO">>}]
             /\ pc' = [pc EXCEPT ![self] = "iterate"]
             /\ UNCHANGED << from, value, echo_recv_value, msgs, msg, me, n, f, 
                             peers, msg_recv, echo_recv, ready_sent, output, 
                             existing_recv, new_recv, peer_id, index >>

iterate(self) == /\ pc[self] = "iterate"
                 /\ IF index[self] <= Len(peers[self])
                       THEN /\ peer_id' = [peer_id EXCEPT ![self] = peers[self][index[self]]]
                            /\ msgs' = [msgs EXCEPT ![peer_id'[self]] = msgs[peer_id'[self]] \union {<<"READY", me[self], value>>}]
                            /\ index' = [index EXCEPT ![self] = index[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "iterate"]
                            /\ UNCHANGED output
                       ELSE /\ output' = [output EXCEPT ![self] = output[self]]
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << msgs, peer_id, index >>
                 /\ UNCHANGED << from, value, echo_recv_value, rbcs, msg, me, 
                                 n, f, peers, msg_recv, echo_recv, ready_sent, 
                                 existing_recv, new_recv >>

handle_message(self) == handle_message_(self) \/ double_assignment(self)
                           \/ ooo(self) \/ iterate(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in CN: handle_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CN : WF_vars(handle_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
==========================================================================
