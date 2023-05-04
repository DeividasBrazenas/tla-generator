-------------------- MODULE handle_ready_message --------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue
CONSTANT NULL

(*--algorithm handle_ready_message
variables
  bcNode \in AN,
  bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue}),
  readyRecvValue \in BOOLEAN \cup {NULL},
  readyRecv = [v \in AllValues |-> [x \in AN |-> readyRecvValue]],
  readySent = ReadySent(readyRecv),
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
       ready_sent |-> readySent,
       ready_recv |-> readyRecv,
       output |-> NULL]],
  node_msgs = [node_id \in AN |-> <<"READY", bcNode, bcValue>>],

define
  AN  == CN \cup FN
  N == Cardinality(AN)
  F == Cardinality(FN)
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
  AllValues == Value \cup {NotValue}
  ReadyCount(ready_recv) == Cardinality({an \in AN : ready_recv[bcValue][an] = TRUE})
  ReadySent(ready_recv) == ReadyCount(ready_recv) > (F * 3)
  map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})
end define;

fair process handle_ready_message \in AN
variables
  rbc = rbcs[self],
  _msg = node_msgs[self],
  msgs = [node_id \in AN |-> {}],
  from = _msg[2],
  value = _msg[3],
  f = NULL,
  me = NULL,
  msg_recv = NULL,
  output = NULL,
  peers = NULL,
  ready_recv = NULL,
  ready_sent = NULL,
  existing_recv = NULL,
  value_recv = NULL,
  count = NULL,
  result = NULL,
begin
handle_ready_message:
  if (_msg[1] /= "READY") then
    goto Done;
  end if;
  after_condition:

  f := rbc.f;
  me := rbc.me;
  msg_recv := rbc.msg_recv;
  output := rbc.output;
  peers := rbc.peers;
  ready_recv := rbc.ready_recv;
  ready_sent := rbc.ready_sent;

  existing_recv := ready_recv[value];

  value_recv := existing_recv;
  map_put_0:
  value_recv[from] := TRUE;

  ready_recv[value] := value_recv;

  rbc.ready_recv := ready_recv;

  count := map_size(value_recv);

  output := CASE
      ((count > (3 * f)) /\ (output = NULL)) -> value
      [] OTHER -> output;

   if ready_sent then print <<"true">>; else print <<"false">>; end if;

  if (~ready_sent /\ (count > f)) then if_0:
      msg_recv[from]["READY"] := TRUE;

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
\* BEGIN TRANSLATION (chksum(pcal) = "d98552f0" /\ chksum(tla) = "8c976278")
\* Label handle_ready_message of process handle_ready_message at line 65 col 3 changed to handle_ready_message_
VARIABLES bcNode, bcValue, readyRecvValue, readyRecv, readySent, rbcs, 
          node_msgs, pc

(* define statement *)
AN  == CN \cup FN
N == Cardinality(AN)
F == Cardinality(FN)
MsgTypes == {"PROPOSE", "ECHO", "READY"}
AllValues == Value \cup {NotValue}
ReadyCount(ready_recv) == Cardinality({an \in AN : ready_recv[bcValue][an] = TRUE})
ReadySent(ready_recv) == ReadyCount(ready_recv) > (F * 3)
map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})

VARIABLES rbc, _msg, msgs, from, value, f, me, msg_recv, output, peers, 
          ready_recv, ready_sent, existing_recv, value_recv, count, result

vars == << bcNode, bcValue, readyRecvValue, readyRecv, readySent, rbcs, 
           node_msgs, pc, rbc, _msg, msgs, from, value, f, me, msg_recv, 
           output, peers, ready_recv, ready_sent, existing_recv, value_recv, 
           count, result >>

ProcSet == (AN)

Init == (* Global variables *)
        /\ bcNode \in AN
        /\ bcValue \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue})
        /\ readyRecvValue \in (BOOLEAN \cup {NULL})
        /\ readyRecv = [v \in AllValues |-> [x \in AN |-> readyRecvValue]]
        /\ readySent = ReadySent(readyRecv)
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
                  ready_sent |-> readySent,
                  ready_recv |-> readyRecv,
                  output |-> NULL]]
        /\ node_msgs = [node_id \in AN |-> <<"READY", bcNode, bcValue>>]
        (* Process handle_ready_message *)
        /\ rbc = [self \in AN |-> rbcs[self]]
        /\ _msg = [self \in AN |-> node_msgs[self]]
        /\ msgs = [self \in AN |-> [node_id \in AN |-> {}]]
        /\ from = [self \in AN |-> _msg[self][2]]
        /\ value = [self \in AN |-> _msg[self][3]]
        /\ f = [self \in AN |-> NULL]
        /\ me = [self \in AN |-> NULL]
        /\ msg_recv = [self \in AN |-> NULL]
        /\ output = [self \in AN |-> NULL]
        /\ peers = [self \in AN |-> NULL]
        /\ ready_recv = [self \in AN |-> NULL]
        /\ ready_sent = [self \in AN |-> NULL]
        /\ existing_recv = [self \in AN |-> NULL]
        /\ value_recv = [self \in AN |-> NULL]
        /\ count = [self \in AN |-> NULL]
        /\ result = [self \in AN |-> NULL]
        /\ pc = [self \in ProcSet |-> "handle_ready_message_"]

handle_ready_message_(self) == /\ pc[self] = "handle_ready_message_"
                               /\ IF (_msg[self][1] /= "READY")
                                     THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "after_condition"]
                               /\ UNCHANGED << bcNode, bcValue, readyRecvValue, 
                                               readyRecv, readySent, rbcs, 
                                               node_msgs, rbc, _msg, msgs, 
                                               from, value, f, me, msg_recv, 
                                               output, peers, ready_recv, 
                                               ready_sent, existing_recv, 
                                               value_recv, count, result >>

after_condition(self) == /\ pc[self] = "after_condition"
                         /\ f' = [f EXCEPT ![self] = rbc[self].f]
                         /\ me' = [me EXCEPT ![self] = rbc[self].me]
                         /\ msg_recv' = [msg_recv EXCEPT ![self] = rbc[self].msg_recv]
                         /\ output' = [output EXCEPT ![self] = rbc[self].output]
                         /\ peers' = [peers EXCEPT ![self] = rbc[self].peers]
                         /\ ready_recv' = [ready_recv EXCEPT ![self] = rbc[self].ready_recv]
                         /\ ready_sent' = [ready_sent EXCEPT ![self] = rbc[self].ready_sent]
                         /\ existing_recv' = [existing_recv EXCEPT ![self] = ready_recv'[self][value[self]]]
                         /\ value_recv' = [value_recv EXCEPT ![self] = existing_recv'[self]]
                         /\ pc' = [pc EXCEPT ![self] = "map_put_0"]
                         /\ UNCHANGED << bcNode, bcValue, readyRecvValue, 
                                         readyRecv, readySent, rbcs, node_msgs, 
                                         rbc, _msg, msgs, from, value, count, 
                                         result >>

map_put_0(self) == /\ pc[self] = "map_put_0"
                   /\ value_recv' = [value_recv EXCEPT ![self][from[self]] = TRUE]
                   /\ ready_recv' = [ready_recv EXCEPT ![self][value[self]] = value_recv'[self]]
                   /\ rbc' = [rbc EXCEPT ![self].ready_recv = ready_recv'[self]]
                   /\ count' = [count EXCEPT ![self] = map_size(value_recv'[self])]
                   /\ output' = [output EXCEPT ![self] =       CASE
                                                         ((count'[self] > (3 * f[self])) /\ (output[self] = NULL)) -> value[self]
                                                         [] OTHER -> output[self]]
                   /\ IF ready_sent[self]
                         THEN /\ PrintT(<<"true">>)
                         ELSE /\ PrintT(<<"false">>)
                   /\ IF (~ready_sent[self] /\ (count'[self] > f[self]))
                         THEN /\ pc' = [pc EXCEPT ![self] = "if_0"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "else_0"]
                   /\ UNCHANGED << bcNode, bcValue, readyRecvValue, readyRecv, 
                                   readySent, rbcs, node_msgs, _msg, msgs, 
                                   from, value, f, me, msg_recv, peers, 
                                   ready_sent, existing_recv, result >>

if_0(self) == /\ pc[self] = "if_0"
              /\ msg_recv' = [msg_recv EXCEPT ![self][from[self]]["READY"] = TRUE]
              /\ rbc' = [rbc EXCEPT ![self].msg_recv = msg_recv'[self],
                                    ![self].ready_sent = TRUE]
              /\ msgs' = [msgs EXCEPT ![self] = [peer_id \in peers[self] |-> msgs[self][peer_id] \cup {<<"READY", me[self], value[self]>>}]]
              /\ result' = [result EXCEPT ![self] = <<"ok", rbc'[self], msgs'[self], output[self]>>]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << bcNode, bcValue, readyRecvValue, readyRecv, 
                              readySent, rbcs, node_msgs, _msg, from, value, f, 
                              me, output, peers, ready_recv, ready_sent, 
                              existing_recv, value_recv, count >>

else_0(self) == /\ pc[self] = "else_0"
                /\ msgs' = [msgs EXCEPT ![self] = msgs[self]]
                /\ result' = [result EXCEPT ![self] = <<"ok", rbc[self], msgs'[self], output[self]>>]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << bcNode, bcValue, readyRecvValue, readyRecv, 
                                readySent, rbcs, node_msgs, rbc, _msg, from, 
                                value, f, me, msg_recv, output, peers, 
                                ready_recv, ready_sent, existing_recv, 
                                value_recv, count >>

handle_ready_message(self) == handle_ready_message_(self)
                                 \/ after_condition(self)
                                 \/ map_put_0(self) \/ if_0(self)
                                 \/ else_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in AN: handle_ready_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in AN : WF_vars(handle_ready_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=====================================================================
