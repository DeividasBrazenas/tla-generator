-------------------- MODULE BrachaRBC_handle_ready_message --------------------
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

(*--algorithm BrachaRBC_handle_ready_message
variables
  from \in AN,
  value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue}),
  ready_recv_value \in BOOLEAN \cup {NULL},
  rbcs = [node_id \in AN |-> [
       n |-> Cardinality(AN),
       f |-> Cardinality(FN),
       me |-> node_id,
       peers |-> SetToSeq(AN),
       broadcaster |-> from,
       predicate |-> [v \in AllValues |-> TRUE],
       max_msg_size |-> 1000,
       propose_sent |-> FALSE,
       echo_sent |-> FALSE,
       ready_sent |-> FALSE,
       msg_recv |-> [from_node_id \in AN |-> [msg_type \in MsgTypes |-> FALSE]],
       ready_recv |-> [v \in AllValues |-> [x \in CN |-> ready_recv_value]],
       output |-> NotValue]],
  msgs = [node_id \in AN |-> {}],
  msg = <<"READY", from, value>>,

define
  AN  == CN \cup FN
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
  AllValues == Value \cup {NotValue}
  map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})
end define;

fair process handle_ready_message \in CN
variables
  rbc = rbcs[self],
  f,
  me,
  msg_recv,
  output,
  peers,
  ready_recv,
  ready_sent,
  existing_recv,
  value_recv,
  count,
  enum_into_0_idx = 1,
  peer_id,
  result,
begin
handle_ready_message:
  if msg[1] /= "READY" then
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

  if (~ready_sent /\ (count > f)) then
  if_0:
    msg_recv[from]["READY"] := TRUE;

    rbc.msg_recv := msg_recv
    || rbc.ready_sent := TRUE;

    enum_into_0:
      while enum_into_0_idx <= Len(peers) do
        peer_id := peers[enum_into_0_idx];
        msgs[peer_id] := msgs[peer_id] \cup {<<"READY", me, value>>};
        enum_into_0_idx := enum_into_0_idx + 1;
      end while;

    result := <<"ok", rbc, msgs, output>>;

  else
    result := <<"ok", rbc, {}, output>>;

  end if;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "76d4c9b5" /\ chksum(tla) = "d2706be9")
\* Label handle_ready_message of process handle_ready_message at line 56 col 3 changed to handle_ready_message_
CONSTANT defaultInitValue
VARIABLES from, value, ready_recv_value, rbcs, msgs, msg, pc

(* define statement *)
AN  == CN \cup FN
MsgTypes == {"PROPOSE", "ECHO", "READY"}
AllValues == Value \cup {NotValue}
map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})

VARIABLES rbc, f, me, msg_recv, output, peers, ready_recv, ready_sent, 
          existing_recv, value_recv, count, enum_into_0_idx, peer_id, result

vars == << from, value, ready_recv_value, rbcs, msgs, msg, pc, rbc, f, me, 
           msg_recv, output, peers, ready_recv, ready_sent, existing_recv, 
           value_recv, count, enum_into_0_idx, peer_id, result >>

ProcSet == (CN)

Init == (* Global variables *)
        /\ from \in AN
        /\ value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue})
        /\ ready_recv_value \in (BOOLEAN \cup {NULL})
        /\ rbcs =   [node_id \in AN |-> [
                  n |-> Cardinality(AN),
                  f |-> Cardinality(FN),
                  me |-> node_id,
                  peers |-> SetToSeq(AN),
                  broadcaster |-> from,
                  predicate |-> [v \in AllValues |-> TRUE],
                  max_msg_size |-> 1000,
                  propose_sent |-> FALSE,
                  echo_sent |-> FALSE,
                  ready_sent |-> FALSE,
                  msg_recv |-> [from_node_id \in AN |-> [msg_type \in MsgTypes |-> FALSE]],
                  ready_recv |-> [v \in AllValues |-> [x \in CN |-> ready_recv_value]],
                  output |-> NotValue]]
        /\ msgs = [node_id \in AN |-> {}]
        /\ msg = <<"READY", from, value>>
        (* Process handle_ready_message *)
        /\ rbc = [self \in CN |-> rbcs[self]]
        /\ f = [self \in CN |-> defaultInitValue]
        /\ me = [self \in CN |-> defaultInitValue]
        /\ msg_recv = [self \in CN |-> defaultInitValue]
        /\ output = [self \in CN |-> defaultInitValue]
        /\ peers = [self \in CN |-> defaultInitValue]
        /\ ready_recv = [self \in CN |-> defaultInitValue]
        /\ ready_sent = [self \in CN |-> defaultInitValue]
        /\ existing_recv = [self \in CN |-> defaultInitValue]
        /\ value_recv = [self \in CN |-> defaultInitValue]
        /\ count = [self \in CN |-> defaultInitValue]
        /\ enum_into_0_idx = [self \in CN |-> 1]
        /\ peer_id = [self \in CN |-> defaultInitValue]
        /\ result = [self \in CN |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "handle_ready_message_"]

handle_ready_message_(self) == /\ pc[self] = "handle_ready_message_"
                               /\ IF msg[1] /= "READY"
                                     THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "after_condition"]
                               /\ UNCHANGED << from, value, ready_recv_value, 
                                               rbcs, msgs, msg, rbc, f, me, 
                                               msg_recv, output, peers, 
                                               ready_recv, ready_sent, 
                                               existing_recv, value_recv, 
                                               count, enum_into_0_idx, peer_id, 
                                               result >>

after_condition(self) == /\ pc[self] = "after_condition"
                         /\ f' = [f EXCEPT ![self] = rbc[self].f]
                         /\ me' = [me EXCEPT ![self] = rbc[self].me]
                         /\ msg_recv' = [msg_recv EXCEPT ![self] = rbc[self].msg_recv]
                         /\ output' = [output EXCEPT ![self] = rbc[self].output]
                         /\ peers' = [peers EXCEPT ![self] = rbc[self].peers]
                         /\ ready_recv' = [ready_recv EXCEPT ![self] = rbc[self].ready_recv]
                         /\ ready_sent' = [ready_sent EXCEPT ![self] = rbc[self].ready_sent]
                         /\ existing_recv' = [existing_recv EXCEPT ![self] = ready_recv'[self][value]]
                         /\ value_recv' = [value_recv EXCEPT ![self] = existing_recv'[self]]
                         /\ pc' = [pc EXCEPT ![self] = "map_put_0"]
                         /\ UNCHANGED << from, value, ready_recv_value, rbcs, 
                                         msgs, msg, rbc, count, 
                                         enum_into_0_idx, peer_id, result >>

map_put_0(self) == /\ pc[self] = "map_put_0"
                   /\ value_recv' = [value_recv EXCEPT ![self][from] = TRUE]
                   /\ ready_recv' = [ready_recv EXCEPT ![self][value] = value_recv'[self]]
                   /\ rbc' = [rbc EXCEPT ![self].ready_recv = ready_recv'[self]]
                   /\ count' = [count EXCEPT ![self] = map_size(value_recv'[self])]
                   /\ output' = [output EXCEPT ![self] =       CASE
                                                         ((count'[self] > (3 * f[self])) /\ (output[self] = NULL)) -> value
                                                         [] OTHER -> output[self]]
                   /\ IF (~ready_sent[self] /\ (count'[self] > f[self]))
                         THEN /\ pc' = [pc EXCEPT ![self] = "if_0"]
                              /\ UNCHANGED result
                         ELSE /\ result' = [result EXCEPT ![self] = <<"ok", rbc'[self], {}, output'[self]>>]
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << from, value, ready_recv_value, rbcs, msgs, 
                                   msg, f, me, msg_recv, peers, ready_sent, 
                                   existing_recv, enum_into_0_idx, peer_id >>

if_0(self) == /\ pc[self] = "if_0"
              /\ msg_recv' = [msg_recv EXCEPT ![self][from]["READY"] = TRUE]
              /\ rbc' = [rbc EXCEPT ![self].msg_recv = msg_recv'[self],
                                    ![self].ready_sent = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "enum_into_0"]
              /\ UNCHANGED << from, value, ready_recv_value, rbcs, msgs, msg, 
                              f, me, output, peers, ready_recv, ready_sent, 
                              existing_recv, value_recv, count, 
                              enum_into_0_idx, peer_id, result >>

enum_into_0(self) == /\ pc[self] = "enum_into_0"
                     /\ IF enum_into_0_idx[self] <= Len(peers[self])
                           THEN /\ peer_id' = [peer_id EXCEPT ![self] = peers[self][enum_into_0_idx[self]]]
                                /\ msgs' = [msgs EXCEPT ![peer_id'[self]] = msgs[peer_id'[self]] \cup {<<"READY", me[self], value>>}]
                                /\ enum_into_0_idx' = [enum_into_0_idx EXCEPT ![self] = enum_into_0_idx[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "enum_into_0"]
                                /\ UNCHANGED result
                           ELSE /\ result' = [result EXCEPT ![self] = <<"ok", rbc[self], msgs, output[self]>>]
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << msgs, enum_into_0_idx, peer_id >>
                     /\ UNCHANGED << from, value, ready_recv_value, rbcs, msg, 
                                     rbc, f, me, msg_recv, output, peers, 
                                     ready_recv, ready_sent, existing_recv, 
                                     value_recv, count >>

handle_ready_message(self) == handle_ready_message_(self)
                                 \/ after_condition(self)
                                 \/ map_put_0(self) \/ if_0(self)
                                 \/ enum_into_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in CN: handle_ready_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CN : WF_vars(handle_ready_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

===============================================================================
