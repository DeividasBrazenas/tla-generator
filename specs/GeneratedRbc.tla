------------------------------ MODULE GeneratedRbc ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS in_handle_new_arg_1, in_handle_new_arg_0, in_rbc, in_input, in_broadcast_val_arg_1, in_broadcast_val_arg_0, in_rs_encode_arg_1, in_rs_encode_arg_0, in_hash_arg_1, in_hash_arg_0, NULL

(*--algorithm Rbc
  variables result_handle_new, result_handle_input, result_broadcast_val, result_rs_encode, result_hash, handle_input_rbc, handle_input_input

  procedure rs_encode(rs_encode_arg_1, data)
  begin
  end procedure;

  procedure hash(data)
  begin
  end procedure;

  procedure broadcast_val(broadcast_val_arg_1, root_hash, shards)
  begin
  end procedure;

  process handle_new = "handle_new"
  begin
  handle_new:
    result_handle_new := <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>;
  end process;

  process handle_input = "handle_input"
  variables rbc = handle_input_rbc, input = handle_input_input, shards, root_hash, msgs
  begin
    handle_input:
      if rbc["n"] = 1 then
        rbc["decoded"] := input
        || rbc["output"] := TRUE;

        result_handle_input := <<"ok", rbc, {}, input>>;

      else
        await rs_encode(rbc, input);
        shards := result_rs_encode;

        await hash(input);
        root_hash := result_hash;

        await broadcast_val(rbc, root_hash, shards);
        msgs := result_broadcast_val;
          
        result_handle_input := <<"ok", rbc, msgs, NULL>>;
      end if;
  end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "738d0ab4" /\ chksum(tla) = "d3fdd5bf")
\* Label handle_new of process handle_new at line 23 col 5 changed to handle_new_
\* Label handle_input of process handle_input at line 30 col 7 changed to handle_input_
\* Process variable shards of process handle_input at line 27 col 65 changed to shards_
\* Process variable root_hash of process handle_input at line 27 col 73 changed to root_hash_
\* Parameter data of procedure rs_encode at line 8 col 40 changed to data_
CONSTANT defaultInitValue
VARIABLES result_handle_new, result_handle_input, result_broadcast_val, 
          result_rs_encode, result_hash, handle_input_rbc, handle_input_input, 
          pc, stack, rs_encode_arg_1, data_, data, broadcast_val_arg_1, 
          root_hash, shards, rbc, input, shards_, root_hash_, msgs

vars == << result_handle_new, result_handle_input, result_broadcast_val, 
           result_rs_encode, result_hash, handle_input_rbc, 
           handle_input_input, pc, stack, rs_encode_arg_1, data_, data, 
           broadcast_val_arg_1, root_hash, shards, rbc, input, shards_, 
           root_hash_, msgs >>

ProcSet == {"handle_new"} \cup {"handle_input"}

Init == (* Global variables *)
        /\ result_handle_new = defaultInitValue
        /\ result_handle_input = defaultInitValue
        /\ result_broadcast_val = defaultInitValue
        /\ result_rs_encode = defaultInitValue
        /\ result_hash = defaultInitValue
        /\ handle_input_rbc = defaultInitValue
        /\ handle_input_input = defaultInitValue
        (* Procedure rs_encode *)
        /\ rs_encode_arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ data_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure hash *)
        /\ data = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure broadcast_val *)
        /\ broadcast_val_arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ root_hash = [ self \in ProcSet |-> defaultInitValue]
        /\ shards = [ self \in ProcSet |-> defaultInitValue]
        (* Process handle_input *)
        /\ rbc = handle_input_rbc
        /\ input = handle_input_input
        /\ shards_ = defaultInitValue
        /\ root_hash_ = defaultInitValue
        /\ msgs = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "handle_new" -> "handle_new_"
                                        [] self = "handle_input" -> "handle_input_"]

rs_encode(self) == 

hash(self) == 

broadcast_val(self) == 

handle_new_ == /\ pc["handle_new"] = "handle_new_"
               /\ result_handle_new' = <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>
               /\ pc' = [pc EXCEPT !["handle_new"] = "Done"]
               /\ UNCHANGED << result_handle_input, result_broadcast_val, 
                               result_rs_encode, result_hash, handle_input_rbc, 
                               handle_input_input, stack, rs_encode_arg_1, 
                               data_, data, broadcast_val_arg_1, root_hash, 
                               shards, rbc, input, shards_, root_hash_, msgs >>

handle_new == handle_new_

handle_input_ == /\ pc["handle_input"] = "handle_input_"
                 /\ IF rbc["n"] = 1
                       THEN /\ rbc' = [rbc EXCEPT !["decoded"] = input,
                                                  !["output"] = TRUE]
                            /\ result_handle_input' = <<"ok", rbc', {}, input>>
                            /\ UNCHANGED << shards_, root_hash_, msgs >>
                       ELSE /\ rs_encode(rbc, input)
                            /\ shards_' = result_rs_encode
                            /\ hash(input)
                            /\ root_hash_' = result_hash
                            /\ broadcast_val(rbc, root_hash_', shards_')
                            /\ msgs' = result_broadcast_val
                            /\ result_handle_input' = <<"ok", rbc, msgs', NULL>>
                            /\ rbc' = rbc
                 /\ pc' = [pc EXCEPT !["handle_input"] = "Done"]
                 /\ UNCHANGED << result_handle_new, result_broadcast_val, 
                                 result_rs_encode, result_hash, 
                                 handle_input_rbc, handle_input_input, stack, 
                                 rs_encode_arg_1, data_, data, 
                                 broadcast_val_arg_1, root_hash, shards, input >>

handle_input == handle_input_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == handle_new \/ handle_input
           \/ (\E self \in ProcSet:  \/ rs_encode(self) \/ hash(self)
                                     \/ broadcast_val(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
========================================================================
