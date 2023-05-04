-------------------- MODULE BrachaRBC_handle_propose_message --------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue
CONSTANT NULL

(*--algorithm handle_propose_message
variables
  bcNode \in AN,
  bcFrom = bcNode,
  bcValue \in (CASE bcFrom \in CN -> Value [] bcFrom \in FN -> {NotValue}),
  echoSent \in BOOLEAN,
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
       echo_sent |-> echoSent,
       echo_recv |-> [echo_value \in AllValues |-> [x \in AN |-> FALSE]],
       ready_sent |-> FALSE,
       ready_recv |-> [ready_value \in AllValues |-> [x \in AN |-> FALSE]],
       output |-> NULL]],
  node_msgs = [node_id \in AN |-> <<"PROPOSE", bcFrom, bcValue>>],

define
  AN  == CN \cup FN
  N == Cardinality(AN)
  F == Cardinality(FN)
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
  AllValues == Value \cup {NotValue}
  predicate_fn(val) == TRUE
end define;

fair process handle_propose_message \in AN
variables
  rbc = rbcs[self],
  _msg = node_msgs[self],
  from = _msg[2],
  value = _msg[3],
  msgs = [node_id \in AN |-> {}],
  broadcaster = NULL,
  echo_sent = NULL,
  me = NULL,
  msg_recv = NULL,
  output = NULL,
  peers = NULL,
  predicate = NULL,
  result = NULL,
begin
handle_propose_message:
  if (_msg[1] /= "PROPOSE") then
    goto Done;
  end if;
  after_condition:

  broadcaster := rbc.broadcaster;
  echo_sent := rbc.echo_sent;
  me := rbc.me;
  msg_recv := rbc.msg_recv;
  output := rbc.output;
  peers := rbc.peers;
  predicate := rbc.predicate;

  if (broadcaster /= from) then
    goto Done;
  end if;
  after_pin_0:

  if (~echo_sent /\ predicate_fn(value)) then
    if_0:
      msg_recv[from]["PROPOSE"] := TRUE;

      rbc.echo_sent := TRUE
      || rbc.msg_recv := msg_recv;

      msgs := [peer_id \in peers |-> msgs[peer_id] \cup {<<"ECHO", me, value>>}];

      result := <<"ok", rbc, msgs, output>>;

  else
    else_0:
      msgs := msgs;

      result := <<"ok", rbc, msgs, output>>;

  end if;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "34154b29" /\ chksum(tla) = "508139b4")
\* Label handle_propose_message of process handle_propose_message at line 59 col 3 changed to handle_propose_message_
VARIABLES bcNode, bcFrom, bcValue, echoSent, rbcs, node_msgs, pc

(* define statement *)
AN  == CN \cup FN
N == Cardinality(AN)
F == Cardinality(FN)
MsgTypes == {"PROPOSE", "ECHO", "READY"}
AllValues == Value \cup {NotValue}
predicate_fn(val) == TRUE

VARIABLES rbc, _msg, from, value, msgs, broadcaster, echo_sent, me, msg_recv, 
          output, peers, predicate, result

vars == << bcNode, bcFrom, bcValue, echoSent, rbcs, node_msgs, pc, rbc, _msg, 
           from, value, msgs, broadcaster, echo_sent, me, msg_recv, output, 
           peers, predicate, result >>

ProcSet == (AN)

Init == (* Global variables *)
        /\ bcNode \in AN
        /\ bcFrom = bcNode
        /\ bcValue \in (CASE bcFrom \in CN -> Value [] bcFrom \in FN -> {NotValue})
        /\ echoSent \in BOOLEAN
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
                  echo_sent |-> echoSent,
                  echo_recv |-> [echo_value \in AllValues |-> [x \in AN |-> FALSE]],
                  ready_sent |-> FALSE,
                  ready_recv |-> [ready_value \in AllValues |-> [x \in AN |-> FALSE]],
                  output |-> NULL]]
        /\ node_msgs = [node_id \in AN |-> <<"PROPOSE", bcFrom, bcValue>>]
        (* Process handle_propose_message *)
        /\ rbc = [self \in AN |-> rbcs[self]]
        /\ _msg = [self \in AN |-> node_msgs[self]]
        /\ from = [self \in AN |-> _msg[self][2]]
        /\ value = [self \in AN |-> _msg[self][3]]
        /\ msgs = [self \in AN |-> [node_id \in AN |-> {}]]
        /\ broadcaster = [self \in AN |-> NULL]
        /\ echo_sent = [self \in AN |-> NULL]
        /\ me = [self \in AN |-> NULL]
        /\ msg_recv = [self \in AN |-> NULL]
        /\ output = [self \in AN |-> NULL]
        /\ peers = [self \in AN |-> NULL]
        /\ predicate = [self \in AN |-> NULL]
        /\ result = [self \in AN |-> NULL]
        /\ pc = [self \in ProcSet |-> "handle_propose_message_"]

handle_propose_message_(self) == /\ pc[self] = "handle_propose_message_"
                                 /\ IF (_msg[self][1] /= "PROPOSE")
                                       THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "after_condition"]
                                 /\ UNCHANGED << bcNode, bcFrom, bcValue, 
                                                 echoSent, rbcs, node_msgs, 
                                                 rbc, _msg, from, value, msgs, 
                                                 broadcaster, echo_sent, me, 
                                                 msg_recv, output, peers, 
                                                 predicate, result >>

after_condition(self) == /\ pc[self] = "after_condition"
                         /\ broadcaster' = [broadcaster EXCEPT ![self] = rbc[self].broadcaster]
                         /\ echo_sent' = [echo_sent EXCEPT ![self] = rbc[self].echo_sent]
                         /\ me' = [me EXCEPT ![self] = rbc[self].me]
                         /\ msg_recv' = [msg_recv EXCEPT ![self] = rbc[self].msg_recv]
                         /\ output' = [output EXCEPT ![self] = rbc[self].output]
                         /\ peers' = [peers EXCEPT ![self] = rbc[self].peers]
                         /\ predicate' = [predicate EXCEPT ![self] = rbc[self].predicate]
                         /\ IF (broadcaster'[self] /= from[self])
                               THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "after_pin_0"]
                         /\ UNCHANGED << bcNode, bcFrom, bcValue, echoSent, 
                                         rbcs, node_msgs, rbc, _msg, from, 
                                         value, msgs, result >>

after_pin_0(self) == /\ pc[self] = "after_pin_0"
                     /\ IF (~echo_sent[self] /\ predicate_fn(value[self]))
                           THEN /\ pc' = [pc EXCEPT ![self] = "if_0"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "else_0"]
                     /\ UNCHANGED << bcNode, bcFrom, bcValue, echoSent, rbcs, 
                                     node_msgs, rbc, _msg, from, value, msgs, 
                                     broadcaster, echo_sent, me, msg_recv, 
                                     output, peers, predicate, result >>

if_0(self) == /\ pc[self] = "if_0"
              /\ msg_recv' = [msg_recv EXCEPT ![self][from[self]]["PROPOSE"] = TRUE]
              /\ rbc' = [rbc EXCEPT ![self].echo_sent = TRUE,
                                    ![self].msg_recv = msg_recv'[self]]
              /\ msgs' = [msgs EXCEPT ![self] = [peer_id \in peers[self] |-> msgs[self][peer_id] \cup {<<"ECHO", me[self], value[self]>>}]]
              /\ result' = [result EXCEPT ![self] = <<"ok", rbc'[self], msgs'[self], output[self]>>]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << bcNode, bcFrom, bcValue, echoSent, rbcs, 
                              node_msgs, _msg, from, value, broadcaster, 
                              echo_sent, me, output, peers, predicate >>

else_0(self) == /\ pc[self] = "else_0"
                /\ msgs' = [msgs EXCEPT ![self] = msgs[self]]
                /\ result' = [result EXCEPT ![self] = <<"ok", rbc[self], msgs'[self], output[self]>>]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << bcNode, bcFrom, bcValue, echoSent, rbcs, 
                                node_msgs, rbc, _msg, from, value, broadcaster, 
                                echo_sent, me, msg_recv, output, peers, 
                                predicate >>

handle_propose_message(self) == handle_propose_message_(self)
                                   \/ after_condition(self)
                                   \/ after_pin_0(self) \/ if_0(self)
                                   \/ else_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in AN: handle_propose_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in AN : WF_vars(handle_propose_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=======================================================================
