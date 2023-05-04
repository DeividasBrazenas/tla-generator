-------------------- MODULE BrachaRBC_handle_echo_message --------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue
CONSTANT NULL

(*--algorithm handle_echo_message
variables
  bcNode \in AN,
  bcFrom \in CN,
  bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue}),
  echoRecvValue \in BOOLEAN \cup {NULL},
  echoRecv = [echo_value \in AllValues |-> [x \in AN |-> echoRecvValue]],
  readySent = ReadySent(echoRecv),
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
       echo_recv |-> echoRecv,
       ready_sent |-> readySent,
       ready_recv |-> [ready_value \in AllValues |-> [x \in AN |-> FALSE]],
       output |-> NULL]],
  node_msgs = [node_id \in AN |-> <<"ECHO", bcFrom, bcValue>>],

define
  AN  == CN \cup FN
  N == Cardinality(AN)
  F == Cardinality(FN)
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
  AllValues == Value \cup {NotValue}
  EchosCount(echo_recv) == Cardinality({an \in AN : echo_recv[bcValue][an] = TRUE})
  ReadySent(echo_recv) == EchosCount(echo_recv) > ((N + F) \div 2)
  map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})
end define;

fair process handle_echo_message \in AN
variables
  rbc = rbcs[self],
  _msg = node_msgs[self],
  from = _msg[2],
  value = _msg[3],
  msgs = [node_id \in AN |-> {}],
  echo_recv = NULL,
  f = NULL,
  me = NULL,
  msg_recv = NULL,
  n = NULL,
  output = NULL,
  peers = NULL,
  ready_sent = NULL,
  existing_recv = NULL,
  value_recv = NULL,
  count = NULL,
  result = NULL,
begin
handle_echo_message:
  if (_msg[1] /= "ECHO") then
    goto Done;
  end if;
  after_condition:

  echo_recv := rbc.echo_recv;
  f := rbc.f;
  me := rbc.me;
  msg_recv := rbc.msg_recv;
  n := rbc.n;
  output := rbc.output;
  peers := rbc.peers;
  ready_sent := rbc.ready_sent;

  existing_recv := echo_recv[value];

  value_recv := existing_recv;
  map_put_0:
  value_recv[from] := TRUE;

  echo_recv[value] := value_recv;

  rbc.echo_recv := echo_recv;

  count := map_size(value_recv);

  if (~ready_sent /\ (count > ((n + f) \div 2))) then
    if_0:
      msg_recv[from]["ECHO"] := TRUE;

      rbc.msg_recv := msg_recv
      || rbc.ready_sent := TRUE;

      msgs := [peer_id \in peers |-> msgs[peer_id] \cup {<<"READY", me, value>>}];

      result := <<"ok", rbc, msgs, output>>;

  else
    else_0:
      msgs := msgs;
      
      result := <<"ok", rbc, msgs, output>>;

  end if;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7fec544d" /\ chksum(tla) = "3faabb4")
\* Label handle_echo_message of process handle_echo_message at line 67 col 3 changed to handle_echo_message_
VARIABLES bcNode, bcFrom, bcValue, echoRecvValue, echoRecv, readySent, rbcs, 
          node_msgs, pc

(* define statement *)
AN  == CN \cup FN
N == Cardinality(AN)
F == Cardinality(FN)
MsgTypes == {"PROPOSE", "ECHO", "READY"}
AllValues == Value \cup {NotValue}
EchosCount(echo_recv) == Cardinality({an \in AN : echo_recv[bcValue][an] = TRUE})
ReadySent(echo_recv) == EchosCount(echo_recv) > ((N + F) \div 2)
map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})

VARIABLES rbc, _msg, from, value, msgs, echo_recv, f, me, msg_recv, n, output, 
          peers, ready_sent, existing_recv, value_recv, count, result

vars == << bcNode, bcFrom, bcValue, echoRecvValue, echoRecv, readySent, rbcs, 
           node_msgs, pc, rbc, _msg, from, value, msgs, echo_recv, f, me, 
           msg_recv, n, output, peers, ready_sent, existing_recv, value_recv, 
           count, result >>

ProcSet == (AN)

Init == (* Global variables *)
        /\ bcNode \in AN
        /\ bcFrom \in CN
        /\ bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue})
        /\ echoRecvValue \in (BOOLEAN \cup {NULL})
        /\ echoRecv = [echo_value \in AllValues |-> [x \in AN |-> echoRecvValue]]
        /\ readySent = ReadySent(echoRecv)
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
                  echo_recv |-> echoRecv,
                  ready_sent |-> readySent,
                  ready_recv |-> [ready_value \in AllValues |-> [x \in AN |-> FALSE]],
                  output |-> NULL]]
        /\ node_msgs = [node_id \in AN |-> <<"ECHO", bcFrom, bcValue>>]
        (* Process handle_echo_message *)
        /\ rbc = [self \in AN |-> rbcs[self]]
        /\ _msg = [self \in AN |-> node_msgs[self]]
        /\ from = [self \in AN |-> _msg[self][2]]
        /\ value = [self \in AN |-> _msg[self][3]]
        /\ msgs = [self \in AN |-> [node_id \in AN |-> {}]]
        /\ echo_recv = [self \in AN |-> NULL]
        /\ f = [self \in AN |-> NULL]
        /\ me = [self \in AN |-> NULL]
        /\ msg_recv = [self \in AN |-> NULL]
        /\ n = [self \in AN |-> NULL]
        /\ output = [self \in AN |-> NULL]
        /\ peers = [self \in AN |-> NULL]
        /\ ready_sent = [self \in AN |-> NULL]
        /\ existing_recv = [self \in AN |-> NULL]
        /\ value_recv = [self \in AN |-> NULL]
        /\ count = [self \in AN |-> NULL]
        /\ result = [self \in AN |-> NULL]
        /\ pc = [self \in ProcSet |-> "handle_echo_message_"]

handle_echo_message_(self) == /\ pc[self] = "handle_echo_message_"
                              /\ IF (_msg[self][1] /= "ECHO")
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "after_condition"]
                              /\ UNCHANGED << bcNode, bcFrom, bcValue, 
                                              echoRecvValue, echoRecv, 
                                              readySent, rbcs, node_msgs, rbc, 
                                              _msg, from, value, msgs, 
                                              echo_recv, f, me, msg_recv, n, 
                                              output, peers, ready_sent, 
                                              existing_recv, value_recv, count, 
                                              result >>

after_condition(self) == /\ pc[self] = "after_condition"
                         /\ echo_recv' = [echo_recv EXCEPT ![self] = rbc[self].echo_recv]
                         /\ f' = [f EXCEPT ![self] = rbc[self].f]
                         /\ me' = [me EXCEPT ![self] = rbc[self].me]
                         /\ msg_recv' = [msg_recv EXCEPT ![self] = rbc[self].msg_recv]
                         /\ n' = [n EXCEPT ![self] = rbc[self].n]
                         /\ output' = [output EXCEPT ![self] = rbc[self].output]
                         /\ peers' = [peers EXCEPT ![self] = rbc[self].peers]
                         /\ ready_sent' = [ready_sent EXCEPT ![self] = rbc[self].ready_sent]
                         /\ existing_recv' = [existing_recv EXCEPT ![self] = echo_recv'[self][value[self]]]
                         /\ value_recv' = [value_recv EXCEPT ![self] = existing_recv'[self]]
                         /\ pc' = [pc EXCEPT ![self] = "map_put_0"]
                         /\ UNCHANGED << bcNode, bcFrom, bcValue, 
                                         echoRecvValue, echoRecv, readySent, 
                                         rbcs, node_msgs, rbc, _msg, from, 
                                         value, msgs, count, result >>

map_put_0(self) == /\ pc[self] = "map_put_0"
                   /\ value_recv' = [value_recv EXCEPT ![self][from[self]] = TRUE]
                   /\ echo_recv' = [echo_recv EXCEPT ![self][value[self]] = value_recv'[self]]
                   /\ rbc' = [rbc EXCEPT ![self].echo_recv = echo_recv'[self]]
                   /\ count' = [count EXCEPT ![self] = map_size(value_recv'[self])]
                   /\ IF (~ready_sent[self] /\ (count'[self] > ((n[self] + f[self]) \div 2)))
                         THEN /\ pc' = [pc EXCEPT ![self] = "if_0"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "else_0"]
                   /\ UNCHANGED << bcNode, bcFrom, bcValue, echoRecvValue, 
                                   echoRecv, readySent, rbcs, node_msgs, _msg, 
                                   from, value, msgs, f, me, msg_recv, n, 
                                   output, peers, ready_sent, existing_recv, 
                                   result >>

if_0(self) == /\ pc[self] = "if_0"
              /\ msg_recv' = [msg_recv EXCEPT ![self][from[self]]["ECHO"] = TRUE]
              /\ rbc' = [rbc EXCEPT ![self].msg_recv = msg_recv'[self],
                                    ![self].ready_sent = TRUE]
              /\ msgs' = [msgs EXCEPT ![self] = [peer_id \in peers[self] |-> msgs[self][peer_id] \cup {<<"READY", me[self], value[self]>>}]]
              /\ result' = [result EXCEPT ![self] = <<"ok", rbc'[self], msgs'[self], output[self]>>]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << bcNode, bcFrom, bcValue, echoRecvValue, echoRecv, 
                              readySent, rbcs, node_msgs, _msg, from, value, 
                              echo_recv, f, me, n, output, peers, ready_sent, 
                              existing_recv, value_recv, count >>

else_0(self) == /\ pc[self] = "else_0"
                /\ msgs' = [msgs EXCEPT ![self] = msgs[self]]
                /\ result' = [result EXCEPT ![self] = <<"ok", rbc[self], msgs'[self], output[self]>>]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << bcNode, bcFrom, bcValue, echoRecvValue, 
                                echoRecv, readySent, rbcs, node_msgs, rbc, 
                                _msg, from, value, echo_recv, f, me, msg_recv, 
                                n, output, peers, ready_sent, existing_recv, 
                                value_recv, count >>

handle_echo_message(self) == handle_echo_message_(self)
                                \/ after_condition(self) \/ map_put_0(self)
                                \/ if_0(self) \/ else_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in AN: handle_echo_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in AN : WF_vars(handle_echo_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====================================================================
