------------------------------- MODULE BrachaRBCPlusCal -------------------------------
\* https://github.com/tlaplus/CommunityModules
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC 

CONSTANT CN         \* Correct nodes
CONSTANT FN         \* Faulty nodes
CONSTANT Value
CONSTANT NotValue   \* Should be in "define" clause
  
(*--algorithm BrachaRBC
variables
    bcNode \in AN,
    bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue}),
    rbcs = [node_id \in AN |-> [n |-> Cardinality(AN), f |-> Cardinality(FN), me |-> node_id, peers |-> SetToSeq(AN), broadcaster |-> bcNode, predicate |-> TRUE, max_msg_size |-> 1000, propose_sent |-> FALSE, echo_sent |-> FALSE, output |-> NotValue]],
    msgs = [node_id \in AN |-> {}]

    
define
    AN  == CN \cup FN       \* All nodes.
end define;

(*
>    1: // only broadcaster node
>    2: input 𝑀
>    3: send ⟨PROPOSE, 𝑀⟩ to all
*)
process handle_input \in AN  \* "\in AN kadangi broadcasteris gali but betkuris node"
variables me = rbcs[self].me, 
          broadcaster = rbcs[self].broadcaster, 
          propose_sent = rbcs[self].propose_sent, 
          peers = rbcs[self].peers, 
          output = rbcs[self].output,
          input = bcValue,
          peer_id,
          index = 1
begin
    handle_input:
        if broadcaster = me /\ propose_sent = FALSE then \* Sitas if'as turi buti vykdomas tik viena karta - atejus broadcasterio node eilei ir jei jeis dar neissiunte msg
            rbcs[self].propose_sent := TRUE;             \* Pazymim, kad broadcasteris issiunte msg

        with m = [t |-> "PROPOSE", src |-> me, v |-> input] do
            msgs := [p \in peers |-> @ \cup {m}];
        end with;
        \* msgs := [peer_id \in peers |-> msgs[peer_id] \cup {[t |-> "PROPOSE", src |-> me, v |-> input]}];
        \* \* Visiem peeram pridedam po pranesima 
        \* iterate:
            \* while index <= Len(peers) do
            \*     peer_id := peers[index];
            \*     msgs[peer_id] := msgs[peer_id] \union {[t |-> "PROPOSE", src |-> me, v |-> input]};
            \*     index := index + 1;
            \* end while;
        print msgs;
        end if;

        
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e8ec6631" /\ chksum(tla) = "49b0332a")
\* Label handle_input of process handle_input at line 38 col 9 changed to handle_input_
CONSTANT defaultInitValue
VARIABLES bcNode, bcValue, rbcs, msgs, pc

(* define statement *)
AN  == CN \cup FN

VARIABLES me, broadcaster, propose_sent, peers, output, input, peer_id, index

vars == << bcNode, bcValue, rbcs, msgs, pc, me, broadcaster, propose_sent, 
           peers, output, input, peer_id, index >>

ProcSet == (AN)

Init == (* Global variables *)
        /\ bcNode \in AN
        /\ bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue})
        /\ rbcs = [node_id \in AN |-> [n |-> Cardinality(AN), f |-> Cardinality(FN), me |-> node_id, peers |-> SetToSeq(AN), broadcaster |-> bcNode, predicate |-> TRUE, max_msg_size |-> 1000, propose_sent |-> FALSE, echo_sent |-> FALSE, output |-> NotValue]]
        /\ msgs = [node_id \in AN |-> {}]
        (* Process handle_input *)
        /\ me = [self \in AN |-> rbcs[self].me]
        /\ broadcaster = [self \in AN |-> rbcs[self].broadcaster]
        /\ propose_sent = [self \in AN |-> rbcs[self].propose_sent]
        /\ peers = [self \in AN |-> rbcs[self].peers]
        /\ output = [self \in AN |-> rbcs[self].output]
        /\ input = [self \in AN |-> bcValue]
        /\ peer_id = [self \in AN |-> defaultInitValue]
        /\ index = [self \in AN |-> 1]
        /\ pc = [self \in ProcSet |-> "handle_input_"]

handle_input_(self) == /\ pc[self] = "handle_input_"
                       /\ IF broadcaster[self] = me[self] /\ propose_sent[self] = FALSE
                             THEN /\ rbcs' = [rbcs EXCEPT ![self].propose_sent = TRUE]
                                  /\ LET m == [t |-> "PROPOSE", src |-> me[self], v |-> input[self]] IN
                                       msgs' = [p \in peers[self] |-> @ \cup {m}]
                                  /\ PrintT(msgs')
                             ELSE /\ TRUE
                                  /\ UNCHANGED << rbcs, msgs >>
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << bcNode, bcValue, me, broadcaster, 
                                       propose_sent, peers, output, input, 
                                       peer_id, index >>

handle_input(self) == handle_input_(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in AN: handle_input(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=======================================================================================
