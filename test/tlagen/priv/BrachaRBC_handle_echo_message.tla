-------------------- MODULE BrachaRBC_handle_echo_message --------------------
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue

(*--algorithm BrachaRBC_handle_echo_message
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
       predicate |-> [v \in AllValues |-> TRUE],
       max_msg_size |-> 1000,
       propose_sent |-> FALSE,
       echo_sent |-> FALSE,
       ready_sent |-> FALSE,
       msg_recv |-> [from_node_id \in AN |-> [msg_type \in MsgTypes |-> FALSE]],
       echo_recv |-> [v \in AllValues |-> [x \in CN |-> echo_recv_value]],
       output |-> NotValue]],
  msgs = [node_id \in AN |-> {}],
  msg = <<"ECHO", from, value>>,

define
  AN  == CN \cup FN
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
  AllValues == Value \cup {NotValue}
  map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})
end define;

fair process handle_echo_message \in CN
variables
  rbc = rbcs[self],
  echo_recv,
  f,
  me,
  msg_recv,
  n,
  output,
  peers,
  ready_sent,
  existing_recv,
  value_recv,
  count,
  enum_into_0_idx = 1,
  peer_id,
  result,
begin
handle_echo_message:
  if msg[1] /= "ECHO" then
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
\* BEGIN TRANSLATION (chksum(pcal) = "8f11784e" /\ chksum(tla) = "140fceb4")
\* Label handle_echo_message of process handle_echo_message at line 57 col 3 changed to handle_echo_message_
CONSTANT defaultInitValue
VARIABLES from, value, echo_recv_value, rbcs, msgs, msg, pc

(* define statement *)
AN  == CN \cup FN
MsgTypes == {"PROPOSE", "ECHO", "READY"}
AllValues == Value \cup {NotValue}
map_size(structure) == Cardinality({k \in (DOMAIN structure) : structure[k] /= NULL})

VARIABLES rbc, echo_recv, f, me, msg_recv, n, output, peers, ready_sent, 
          existing_recv, value_recv, count, enum_into_0_idx, peer_id, result

vars == << from, value, echo_recv_value, rbcs, msgs, msg, pc, rbc, echo_recv, 
           f, me, msg_recv, n, output, peers, ready_sent, existing_recv, 
           value_recv, count, enum_into_0_idx, peer_id, result >>

ProcSet == (CN)

Init == (* Global variables *)
        /\ from \in AN
        /\ value \in (CASE from \in CN -> Value [] from \in FN -> {NotValue})
        /\ echo_recv_value \in (BOOLEAN \cup {NULL})
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
                  echo_recv |-> [v \in AllValues |-> [x \in CN |-> echo_recv_value]],
                  output |-> NotValue]]
        /\ msgs = [node_id \in AN |-> {}]
        /\ msg = <<"ECHO", from, value>>
        (* Process handle_echo_message *)
        /\ rbc = [self \in CN |-> rbcs[self]]
        /\ echo_recv = [self \in CN |-> defaultInitValue]
        /\ f = [self \in CN |-> defaultInitValue]
        /\ me = [self \in CN |-> defaultInitValue]
        /\ msg_recv = [self \in CN |-> defaultInitValue]
        /\ n = [self \in CN |-> defaultInitValue]
        /\ output = [self \in CN |-> defaultInitValue]
        /\ peers = [self \in CN |-> defaultInitValue]
        /\ ready_sent = [self \in CN |-> defaultInitValue]
        /\ existing_recv = [self \in CN |-> defaultInitValue]
        /\ value_recv = [self \in CN |-> defaultInitValue]
        /\ count = [self \in CN |-> defaultInitValue]
        /\ enum_into_0_idx = [self \in CN |-> 1]
        /\ peer_id = [self \in CN |-> defaultInitValue]
        /\ result = [self \in CN |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "handle_echo_message_"]

handle_echo_message_(self) == /\ pc[self] = "handle_echo_message_"
                              /\ IF msg[1] /= "ECHO"
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "after_condition"]
                              /\ UNCHANGED << from, value, echo_recv_value, 
                                              rbcs, msgs, msg, rbc, echo_recv, 
                                              f, me, msg_recv, n, output, 
                                              peers, ready_sent, existing_recv, 
                                              value_recv, count, 
                                              enum_into_0_idx, peer_id, result >>

after_condition(self) == /\ pc[self] = "after_condition"
                         /\ echo_recv' = [echo_recv EXCEPT ![self] = rbc[self].echo_recv]
                         /\ f' = [f EXCEPT ![self] = rbc[self].f]
                         /\ me' = [me EXCEPT ![self] = rbc[self].me]
                         /\ msg_recv' = [msg_recv EXCEPT ![self] = rbc[self].msg_recv]
                         /\ n' = [n EXCEPT ![self] = rbc[self].n]
                         /\ output' = [output EXCEPT ![self] = rbc[self].output]
                         /\ peers' = [peers EXCEPT ![self] = rbc[self].peers]
                         /\ ready_sent' = [ready_sent EXCEPT ![self] = rbc[self].ready_sent]
                         /\ existing_recv' = [existing_recv EXCEPT ![self] = echo_recv'[self][value]]
                         /\ value_recv' = [value_recv EXCEPT ![self] = existing_recv'[self]]
                         /\ pc' = [pc EXCEPT ![self] = "map_put_0"]
                         /\ UNCHANGED << from, value, echo_recv_value, rbcs, 
                                         msgs, msg, rbc, count, 
                                         enum_into_0_idx, peer_id, result >>

map_put_0(self) == /\ pc[self] = "map_put_0"
                   /\ value_recv' = [value_recv EXCEPT ![self][from] = TRUE]
                   /\ echo_recv' = [echo_recv EXCEPT ![self][value] = value_recv'[self]]
                   /\ rbc' = [rbc EXCEPT ![self].echo_recv = echo_recv'[self]]
                   /\ count' = [count EXCEPT ![self] = map_size(value_recv'[self])]
                   /\ IF (~ready_sent[self] /\ (count'[self] > ((n[self] + f[self]) \div 2)))
                         THEN /\ pc' = [pc EXCEPT ![self] = "if_0"]
                              /\ UNCHANGED result
                         ELSE /\ result' = [result EXCEPT ![self] = <<"ok", rbc'[self], {}, output[self]>>]
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << from, value, echo_recv_value, rbcs, msgs, 
                                   msg, f, me, msg_recv, n, output, peers, 
                                   ready_sent, existing_recv, enum_into_0_idx, 
                                   peer_id >>

if_0(self) == /\ pc[self] = "if_0"
              /\ msg_recv' = [msg_recv EXCEPT ![self][from]["ECHO"] = TRUE]
              /\ rbc' = [rbc EXCEPT ![self].msg_recv = msg_recv'[self],
                                    ![self].ready_sent = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "enum_into_0"]
              /\ UNCHANGED << from, value, echo_recv_value, rbcs, msgs, msg, 
                              echo_recv, f, me, n, output, peers, ready_sent, 
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
                     /\ UNCHANGED << from, value, echo_recv_value, rbcs, msg, 
                                     rbc, echo_recv, f, me, msg_recv, n, 
                                     output, peers, ready_sent, existing_recv, 
                                     value_recv, count >>

handle_echo_message(self) == handle_echo_message_(self)
                                \/ after_condition(self) \/ map_put_0(self)
                                \/ if_0(self) \/ enum_into_0(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in CN: handle_echo_message(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in CN : WF_vars(handle_echo_message(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

==============================================================================
