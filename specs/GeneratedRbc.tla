------------------------------ MODULE GeneratedRbc ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS handle_new_arg_1, handle_new_arg_1, rbc, input, broadcast_val_arg_1, shards, rs_encode_arg_1, data, data, data, NULL

(*--algorithm Rbc
  variables result_handle_new, result_handle_input, result_broadcast_val, result_rs_encode, result_hash

  procedure broadcast_val(broadcast_val_arg_1, shards)
  variables shard;
  begin
    broadcast_val:
      result_broadcast_val := "result_broadcast_val";
  end procedure;

  procedure rs_encode(rs_encode_arg_1, data)
  begin
    rs_encode:
      result_rs_encode := "result_rs_encode";
  end procedure;

  procedure hash(data)
  begin
    hash:
      result_hash := "result_hash";
  end procedure;


  process handle_new = "handle_new"
  variables handle_new_arg_1 = input_handle_new_handle_new_arg_1;
  begin
    handle_new:
      result_handle_new := <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>;
  end process;

  process handle_input = "handle_input"
  variables rbc = input_handle_input_rbc, input = input_handle_input_input, shards, root_hash, msgs;
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
\* BEGIN TRANSLATION (chksum(pcal) = "1df2cbe1" /\ chksum(tla) = "46417d0")
\* Label broadcast_val of procedure broadcast_val at line 12 col 7 changed to broadcast_val_
\* Label rs_encode of procedure rs_encode at line 18 col 7 changed to rs_encode_
\* Label hash of procedure hash at line 24 col 7 changed to hash_
\* Label handle_new of process handle_new at line 32 col 7 changed to handle_new_
\* Label handle_input of process handle_input at line 39 col 7 changed to handle_input_
\* Process variable shards of process handle_input at line 36 col 77 changed to shards_
\* Parameter data of procedure rs_encode at line 15 col 40 changed to data_
CONSTANT defaultInitValue
VARIABLES result_handle_new, result_handle_input, result_broadcast_val, 
          result_rs_encode, result_hash, pc, stack, broadcast_val_arg_1, 
          shards, shard, rs_encode_arg_1, data_, data, handle_new_arg_1, rbc, 
          input, shards_, root_hash, msgs

vars == << result_handle_new, result_handle_input, result_broadcast_val, 
           result_rs_encode, result_hash, pc, stack, broadcast_val_arg_1, 
           shards, shard, rs_encode_arg_1, data_, data, handle_new_arg_1, rbc, 
           input, shards_, root_hash, msgs >>

ProcSet == {"handle_new"} \cup {"handle_input"}

Init == (* Global variables *)
        /\ result_handle_new = defaultInitValue
        /\ result_handle_input = defaultInitValue
        /\ result_broadcast_val = defaultInitValue
        /\ result_rs_encode = defaultInitValue
        /\ result_hash = defaultInitValue
        (* Procedure broadcast_val *)
        /\ broadcast_val_arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ shards = [ self \in ProcSet |-> defaultInitValue]
        /\ shard = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure rs_encode *)
        /\ rs_encode_arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ data_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure hash *)
        /\ data = [ self \in ProcSet |-> defaultInitValue]
        (* Process handle_new *)
        /\ handle_new_arg_1 = input_handle_new_handle_new_arg_1
        (* Process handle_input *)
        /\ rbc = input_handle_input_rbc
        /\ input = input_handle_input_input
        /\ shards_ = defaultInitValue
        /\ root_hash = defaultInitValue
        /\ msgs = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "handle_new" -> "handle_new_"
                                        [] self = "handle_input" -> "handle_input_"]

broadcast_val_(self) == /\ pc[self] = "broadcast_val_"
                        /\ result_broadcast_val' = "result_broadcast_val"
                        /\ pc' = [pc EXCEPT ![self] = "Error"]
                        /\ UNCHANGED << result_handle_new, result_handle_input, 
                                        result_rs_encode, result_hash, stack, 
                                        broadcast_val_arg_1, shards, shard, 
                                        rs_encode_arg_1, data_, data, 
                                        handle_new_arg_1, rbc, input, shards_, 
                                        root_hash, msgs >>

broadcast_val(self) == broadcast_val_(self)

rs_encode_(self) == /\ pc[self] = "rs_encode_"
                    /\ result_rs_encode' = "result_rs_encode"
                    /\ pc' = [pc EXCEPT ![self] = "Error"]
                    /\ UNCHANGED << result_handle_new, result_handle_input, 
                                    result_broadcast_val, result_hash, stack, 
                                    broadcast_val_arg_1, shards, shard, 
                                    rs_encode_arg_1, data_, data, 
                                    handle_new_arg_1, rbc, input, shards_, 
                                    root_hash, msgs >>

rs_encode(self) == rs_encode_(self)

hash_(self) == /\ pc[self] = "hash_"
               /\ result_hash' = "result_hash"
               /\ pc' = [pc EXCEPT ![self] = "Error"]
               /\ UNCHANGED << result_handle_new, result_handle_input, 
                               result_broadcast_val, result_rs_encode, stack, 
                               broadcast_val_arg_1, shards, shard, 
                               rs_encode_arg_1, data_, data, handle_new_arg_1, 
                               rbc, input, shards_, root_hash, msgs >>

hash(self) == hash_(self)

handle_new_ == /\ pc["handle_new"] = "handle_new_"
               /\ result_handle_new' = <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>
               /\ pc' = [pc EXCEPT !["handle_new"] = "Done"]
               /\ UNCHANGED << result_handle_input, result_broadcast_val, 
                               result_rs_encode, result_hash, stack, 
                               broadcast_val_arg_1, shards, shard, 
                               rs_encode_arg_1, data_, data, handle_new_arg_1, 
                               rbc, input, shards_, root_hash, msgs >>

handle_new == handle_new_

handle_input_ == /\ pc["handle_input"] = "handle_input_"
                 /\ IF rbc["n"] = 1
                       THEN /\ rbc' = [rbc EXCEPT !["decoded"] = input,
                                                  !["output"] = TRUE]
                            /\ result_handle_input' = <<"ok", rbc', {}, input>>
                            /\ UNCHANGED << shards_, root_hash, msgs >>
                       ELSE /\ rs_encode(rbc, input)
                            /\ shards_' = result_rs_encode
                            /\ hash(input)
                            /\ root_hash' = result_hash
                            /\ broadcast_val(rbc, root_hash', shards_')
                            /\ msgs' = result_broadcast_val
                            /\ result_handle_input' = <<"ok", rbc, msgs', NULL>>
                            /\ rbc' = rbc
                 /\ pc' = [pc EXCEPT !["handle_input"] = "Done"]
                 /\ UNCHANGED << result_handle_new, result_broadcast_val, 
                                 result_rs_encode, result_hash, stack, 
                                 broadcast_val_arg_1, shards, shard, 
                                 rs_encode_arg_1, data_, data, 
                                 handle_new_arg_1, input >>

handle_input == handle_input_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == handle_new \/ handle_input
           \/ (\E self \in ProcSet:  \/ broadcast_val(self) \/ rs_encode(self)
                                     \/ hash(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
========================================================================
