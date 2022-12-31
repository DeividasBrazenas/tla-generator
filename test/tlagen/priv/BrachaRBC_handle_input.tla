-------------------- MODULE BrachaRBC_handle_input --------------------
EXTENDS Naturals, FiniteSets, Sequences, SequencesExt, TLC

CONSTANT CN
CONSTANT FN
CONSTANT Value
CONSTANT NotValue
CONSTANT NULL

(*--algorithm BrachaRBC_handle_input
variables
  bcNode \in AN,
  rbcs = [node_id \in AN |->
       [n |-> Cardinality(AN),
       f |-> Cardinality(FN),
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
       output |-> NotValue]],
  input \in (CASE bcNode \in CN -> Value [] bcNode \in FN -> {NotValue}),
  msgs = [node_id \in AN |-> {}],

define
  AN  == CN \cup FN
  AllValues == Value \cup {NotValue}
  MsgTypes == {"PROPOSE", "ECHO", "READY"}
end define;

fair process handle_input \in AN
variables
  rbc = rbcs[self],
  broadcaster = NULL,
  me = NULL,
  output = NULL,
  peers = NULL,
  propose_sent = NULL,
  msgs = NULL,
  result = NULL,
begin
handle_input:
  broadcaster := rbc.broadcaster;
  me := rbc.me;
  output := rbc.output;
  peers := rbc.peers;
  propose_sent := rbc.propose_sent;

  if broadcaster /= me then
    goto Done;
  end if;
  after_pin_0:

  if propose_sent /= FALSE then
    goto Done;
  end if;
  after_pin_1:

  rbc.propose_sent := TRUE;

  msgs := [peer_id \in peers |-> msgs[peer_id]] \cup <<"PROPOSE", me, input>>

not implemented

  result := <<"ok", rbc, msgs, output>>;

end process;
end algorithm; *)

=======================================================================