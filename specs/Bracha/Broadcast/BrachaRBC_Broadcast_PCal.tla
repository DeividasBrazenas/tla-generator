----------------------- MODULE BrachaRBC_Broadcast_PCal -----------------------
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC 

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

(*--algorithm BrachaRBC
variables
    bcNode \in AN, 
    rbc = [n |-> Cardinality(AN), f |-> Cardinality(FN), me |-> bcNode, peers |-> SetToSeq(AN), broadcaster |-> bcNode, predicate |-> TRUE, max_msg_size |-> 1000, propose_sent |-> FALSE, output |-> NotValue], 
    input \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue}),
    msgs = [node_id \in AN |-> {}]
define
    AN  == CN \cup FN       \* All nodes.
end define;

fair process handle_input = "handle_input"
variables
    me = rbc.me, 
    broadcaster = rbc.broadcaster, 
    propose_sent = rbc.propose_sent, 
    peers = rbc.peers, 
    output = rbc.output,
    peer_id,
    index = 1
begin
    handle_input:
    if broadcaster = me /\ propose_sent = FALSE then
        rbc.propose_sent := TRUE;
        iterate:
            while index <= Len(peers) do
                peer_id := peers[index];
                msgs[peer_id] := msgs[peer_id] \union {<<"PROPOSE", me, input>>};
                index := index + 1;
            end while;
            output := output;
    end if;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "94ed0f00" /\ chksum(tla) = "56b3f946")
\* Label handle_input of process handle_input at line 30 col 5 changed to handle_input_
CONSTANT defaultInitValue
VARIABLES bcNode, rbc, input, msgs, pc

(* define statement *)
AN  == CN \cup FN

VARIABLES me, broadcaster, propose_sent, peers, output, peer_id, index

vars == << bcNode, rbc, input, msgs, pc, me, broadcaster, propose_sent, peers, 
           output, peer_id, index >>

ProcSet == {"handle_input"}

Init == (* Global variables *)
        /\ bcNode \in AN
        /\ rbc = [n |-> Cardinality(AN), f |-> Cardinality(FN), me |-> bcNode, peers |-> SetToSeq(AN), broadcaster |-> bcNode, predicate |-> TRUE, max_msg_size |-> 1000, propose_sent |-> FALSE, output |-> NotValue]
        /\ input \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue})
        /\ msgs = [node_id \in AN |-> {}]
        (* Process handle_input *)
        /\ me = rbc.me
        /\ broadcaster = rbc.broadcaster
        /\ propose_sent = rbc.propose_sent
        /\ peers = rbc.peers
        /\ output = rbc.output
        /\ peer_id = defaultInitValue
        /\ index = 1
        /\ pc = [self \in ProcSet |-> "handle_input_"]

handle_input_ == /\ pc["handle_input"] = "handle_input_"
                 /\ IF broadcaster = me /\ propose_sent = FALSE
                       THEN /\ rbc' = [rbc EXCEPT !.propose_sent = TRUE]
                            /\ pc' = [pc EXCEPT !["handle_input"] = "iterate"]
                       ELSE /\ pc' = [pc EXCEPT !["handle_input"] = "Done"]
                            /\ rbc' = rbc
                 /\ UNCHANGED << bcNode, input, msgs, me, broadcaster, 
                                 propose_sent, peers, output, peer_id, index >>

iterate == /\ pc["handle_input"] = "iterate"
           /\ IF index <= Len(peers)
                 THEN /\ peer_id' = peers[index]
                      /\ msgs' = [msgs EXCEPT ![peer_id'] = msgs[peer_id'] \union {<<"PROPOSE", me, input>>}]
                      /\ index' = index + 1
                      /\ pc' = [pc EXCEPT !["handle_input"] = "iterate"]
                      /\ UNCHANGED output
                 ELSE /\ output' = output
                      /\ pc' = [pc EXCEPT !["handle_input"] = "Done"]
                      /\ UNCHANGED << msgs, peer_id, index >>
           /\ UNCHANGED << bcNode, rbc, input, me, broadcaster, propose_sent, 
                           peers >>

handle_input == handle_input_ \/ iterate

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == handle_input
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(handle_input)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


===============================================================================
