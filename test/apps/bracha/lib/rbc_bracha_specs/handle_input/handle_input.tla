-------------------- MODULE handle_input --------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue
CONSTANT NULL

(*--algorithm handle_input
variables
  bcNode \in AN,
  bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue}),
  rbcs = [node_id \in AN |->
       [n |-> N,
       f |-> F,
       me |-> node_id,
       peers |-> AN,
       broadcaster |-> bcNode,
       predicate |-> [v \in AllValues |-> TRUE],
       max_msg_size |-> 1000,
       propose_sent |-> FALSE,
       msg_recv |-> [msg_from_node_id \in AN |-> [msg_type \in MsgTypes |-> FALSE]],
       echo_sent |-> FALSE,
       echo_recv |-> [echo_value \in AllValues |-> [x \in AN |-> FALSE]],
       ready_sent |-> FALSE,
       ready_recv |-> [ready_value \in AllValues |-> [x \in AN |-> FALSE]],
       output |-> NULL]],
  node_input = [node_id \in AN |-> bcValue],

define
  AN  == CN \cup FN
  N == Cardinality(AN)
  F == Cardinality(FN)
  AllValues == Value \cup {NotValue}
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
end define;

fair process handle_input \in AN
variables
  rbc = rbcs[self],
  input = node_input[self],
  msgs = [node_id \in AN |-> {}],
  broadcaster = NULL,
  me = NULL,
  output = NULL,
  peers = NULL,
  propose_sent = NULL,
  result = NULL,
begin
handle_input:
  broadcaster := rbc.broadcaster;
  me := rbc.me;
  output := rbc.output;
  peers := rbc.peers;
  propose_sent := rbc.propose_sent;

  if (broadcaster /= me) then
    goto Done;
  end if;
  after_pin_0:

  if (propose_sent /= FALSE) then
    goto Done;
  end if;
  after_pin_1:

  rbc.propose_sent := TRUE;

  msgs := [peer_id \in peers |-> msgs[peer_id] \cup {<<"PROPOSE", me, input>>}];

  result := <<"ok", rbc, msgs, output>>;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "222a76a" /\ chksum(tla) = "fd38e5df")
\* Label handle_input of process handle_input at line 52 col 3 changed to handle_input_
VARIABLES bcNode, bcValue, rbcs, node_input, pc

(* define statement *)
AN  == CN \cup FN
N == Cardinality(AN)
F == Cardinality(FN)
AllValues == Value \cup {NotValue}
MsgTypes == {"PROPOSE", "ECHO", "READY"}

VARIABLES rbc, input, msgs, broadcaster, me, output, peers, propose_sent, 
          result

vars == << bcNode, bcValue, rbcs, node_input, pc, rbc, input, msgs, 
           broadcaster, me, output, peers, propose_sent, result >>

ProcSet == (AN)

Init == (* Global variables *)
        /\ bcNode \in AN
        /\ bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue})
        /\ rbcs =   [node_id \in AN |->
                  [n |-> N,
                  f |-> F,
                  me |-> node_id,
                  peers |-> AN,
                  broadcaster |-> bcNode,
                  predicate |-> [v \in AllValues |-> TRUE],
                  max_msg_size |-> 1000,
                  propose_sent |-> FALSE,
                  msg_recv |-> [msg_from_node_id \in AN |-> [msg_type \in MsgTypes |-> FALSE]],
                  echo_sent |-> FALSE,
                  echo_recv |-> [echo_value \in AllValues |-> [x \in AN |-> FALSE]],
                  ready_sent |-> FALSE,
                  ready_recv |-> [ready_value \in AllValues |-> [x \in AN |-> FALSE]],
                  output |-> NULL]]
        /\ node_input = [node_id \in AN |-> bcValue]
        (* Process handle_input *)
        /\ rbc = [self \in AN |-> rbcs[self]]
        /\ input = [self \in AN |-> node_input[self]]
        /\ msgs = [self \in AN |-> [node_id \in AN |-> {}]]
        /\ broadcaster = [self \in AN |-> NULL]
        /\ me = [self \in AN |-> NULL]
        /\ output = [self \in AN |-> NULL]
        /\ peers = [self \in AN |-> NULL]
        /\ propose_sent = [self \in AN |-> NULL]
        /\ result = [self \in AN |-> NULL]
        /\ pc = [self \in ProcSet |-> "handle_input_"]

handle_input_(self) == /\ pc[self] = "handle_input_"
                       /\ broadcaster' = [broadcaster EXCEPT ![self] = rbc[self].broadcaster]
                       /\ me' = [me EXCEPT ![self] = rbc[self].me]
                       /\ output' = [output EXCEPT ![self] = rbc[self].output]
                       /\ peers' = [peers EXCEPT ![self] = rbc[self].peers]
                       /\ propose_sent' = [propose_sent EXCEPT ![self] = rbc[self].propose_sent]
                       /\ IF (broadcaster'[self] /= me'[self])
                             THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "after_pin_0"]
                       /\ UNCHANGED << bcNode, bcValue, rbcs, node_input, rbc, 
                                       input, msgs, result >>

after_pin_0(self) == /\ pc[self] = "after_pin_0"
                     /\ IF (propose_sent[self] /= FALSE)
                           THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "after_pin_1"]
                     /\ UNCHANGED << bcNode, bcValue, rbcs, node_input, rbc, 
                                     input, msgs, broadcaster, me, output, 
                                     peers, propose_sent, result >>

after_pin_1(self) == /\ pc[self] = "after_pin_1"
                     /\ rbc' = [rbc EXCEPT ![self].propose_sent = TRUE]
                     /\ msgs' = [msgs EXCEPT ![self] = [peer_id \in peers[self] |-> msgs[self][peer_id] \cup {<<"PROPOSE", me[self], input[self]>>}]]
                     /\ result' = [result EXCEPT ![self] = <<"ok", rbc'[self], msgs'[self], output[self]>>]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << bcNode, bcValue, rbcs, node_input, input, 
                                     broadcaster, me, output, peers, 
                                     propose_sent >>

handle_input(self) == handle_input_(self) \/ after_pin_0(self)
                         \/ after_pin_1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in AN: handle_input(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in AN : WF_vars(handle_input(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================
