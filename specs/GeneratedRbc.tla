------------------------------ MODULE GeneratedRbc ------------------------------
EXTENDS Sequences, Naturals, TLC
CONSTANTS NULL, handle_new_arg_1, handle_input_rbc, handle_input_input

(*--algorithm GeneratedRbc
  variables result_handle_new, 
            result_handle_input, 
            result_rs_encode = [self \in ProcSet |-> defaultInitValue],
            result_hash = [self \in ProcSet |-> defaultInitValue],
            result_broadcast_val = [self \in ProcSet |-> defaultInitValue]

  procedure rs_encode(rs_encode_arg_1, data)
  begin
    rs_encode:
      result_rs_encode[self] := data;
      return;
  end procedure;
  
  procedure hash(data)
  begin
    hash:
      result_hash[self] := data;
      return;
  end procedure;
  
  procedure broadcast_val(broadcast_val_arg_1, root_hash, shards)
  variables loop_result = <<>>, shard
  begin
    broadcast_val:
      while shards /= <<>> do
        shard := Head(shards);
        shards := Tail(shards);

        call hash(shard[3]);
        label:
        loop_result := Append(loop_result, <<shard[1], <<<<"VAL", root_hash, result_hash[self], shard>>>>>>);
      end while;
      result_broadcast_val[self] := loop_result;
      return;
  end procedure;


  process handle_new \in {"handle_new"}
  variables i = handle_new_arg_1[1], n = handle_new_arg_1[2], f = handle_new_arg_1[3]
  begin
    handle_new:
      result_handle_new := <<"ok", [i |-> i, n |-> n, f |-> f], {}, NULL>>;
  end process;
  
  process handle_input \in {"handle_input"}
  variables rbc = handle_input_rbc, input = handle_input_input, shards, root_hash, msgs
  begin
    handle_input:
      if rbc["n"] = 1 then
        rbc["decoded"] := input
        || rbc["output"] := TRUE;

        result_handle_input := <<"ok", rbc, {}, input>>;
      else
        call rs_encode(rbc, input);
        result_rs_encode:
        shards := result_rs_encode[self];
        print <<"shards: ", shards>>;
        
        call hash(input);
        result_hash:
        root_hash := result_hash[self];
        print <<"hash: ", root_hash>>;
        
        call broadcast_val(rbc, root_hash, shards);
        result_broadcast_val:
        msgs := result_broadcast_val[self];
        print <<"broadcast val: ", msgs>>;
          
        result_handle_input := <<"ok", rbc, msgs, NULL>>;
      end if;
  end process;
  
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "48588598" /\ chksum(tla) = "2e9be114")
\* Label rs_encode of procedure rs_encode at line 15 col 7 changed to rs_encode_
\* Label hash of procedure hash at line 22 col 7 changed to hash_
\* Label broadcast_val of procedure broadcast_val at line 30 col 7 changed to broadcast_val_
\* Label handle_new of process handle_new at line 47 col 7 changed to handle_new_
\* Label handle_input of process handle_input at line 54 col 7 changed to handle_input_
\* Label result_rs_encode of process handle_input at line 62 col 9 changed to result_rs_encode_
\* Label result_hash of process handle_input at line 67 col 9 changed to result_hash_
\* Label result_broadcast_val of process handle_input at line 72 col 9 changed to result_broadcast_val_
\* Process variable shards of process handle_input at line 51 col 65 changed to shards_
\* Process variable root_hash of process handle_input at line 51 col 73 changed to root_hash_
\* Parameter data of procedure rs_encode at line 12 col 40 changed to data_
CONSTANT defaultInitValue
VARIABLES result_handle_new, result_handle_input, result_rs_encode, 
          result_hash, result_broadcast_val, pc, stack, rs_encode_arg_1, 
          data_, data, broadcast_val_arg_1, root_hash, shards, loop_result, 
          shard, i, n, f, rbc, input, shards_, root_hash_, msgs

vars == << result_handle_new, result_handle_input, result_rs_encode, 
           result_hash, result_broadcast_val, pc, stack, rs_encode_arg_1, 
           data_, data, broadcast_val_arg_1, root_hash, shards, loop_result, 
           shard, i, n, f, rbc, input, shards_, root_hash_, msgs >>

ProcSet == ({"handle_new"}) \cup ({"handle_input"})

Init == (* Global variables *)
        /\ result_handle_new = defaultInitValue
        /\ result_handle_input = defaultInitValue
        /\ result_rs_encode = [self \in ProcSet |-> defaultInitValue]
        /\ result_hash = [self \in ProcSet |-> defaultInitValue]
        /\ result_broadcast_val = [self \in ProcSet |-> defaultInitValue]
        (* Procedure rs_encode *)
        /\ rs_encode_arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ data_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure hash *)
        /\ data = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure broadcast_val *)
        /\ broadcast_val_arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ root_hash = [ self \in ProcSet |-> defaultInitValue]
        /\ shards = [ self \in ProcSet |-> defaultInitValue]
        /\ loop_result = [ self \in ProcSet |-> <<>>]
        /\ shard = [ self \in ProcSet |-> defaultInitValue]
        (* Process handle_new *)
        /\ i = [self \in {"handle_new"} |-> handle_new_arg_1[1]]
        /\ n = [self \in {"handle_new"} |-> handle_new_arg_1[2]]
        /\ f = [self \in {"handle_new"} |-> handle_new_arg_1[3]]
        (* Process handle_input *)
        /\ rbc = [self \in {"handle_input"} |-> handle_input_rbc]
        /\ input = [self \in {"handle_input"} |-> handle_input_input]
        /\ shards_ = [self \in {"handle_input"} |-> defaultInitValue]
        /\ root_hash_ = [self \in {"handle_input"} |-> defaultInitValue]
        /\ msgs = [self \in {"handle_input"} |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {"handle_new"} -> "handle_new_"
                                        [] self \in {"handle_input"} -> "handle_input_"]

rs_encode_(self) == /\ pc[self] = "rs_encode_"
                    /\ result_rs_encode' = [result_rs_encode EXCEPT ![self] = data_[self]]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ rs_encode_arg_1' = [rs_encode_arg_1 EXCEPT ![self] = Head(stack[self]).rs_encode_arg_1]
                    /\ data_' = [data_ EXCEPT ![self] = Head(stack[self]).data_]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << result_handle_new, result_handle_input, 
                                    result_hash, result_broadcast_val, data, 
                                    broadcast_val_arg_1, root_hash, shards, 
                                    loop_result, shard, i, n, f, rbc, input, 
                                    shards_, root_hash_, msgs >>

rs_encode(self) == rs_encode_(self)

hash_(self) == /\ pc[self] = "hash_"
               /\ result_hash' = [result_hash EXCEPT ![self] = data[self]]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ data' = [data EXCEPT ![self] = Head(stack[self]).data]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << result_handle_new, result_handle_input, 
                               result_rs_encode, result_broadcast_val, 
                               rs_encode_arg_1, data_, broadcast_val_arg_1, 
                               root_hash, shards, loop_result, shard, i, n, f, 
                               rbc, input, shards_, root_hash_, msgs >>

hash(self) == hash_(self)

broadcast_val_(self) == /\ pc[self] = "broadcast_val_"
                        /\ IF shards[self] /= <<>>
                              THEN /\ shard' = [shard EXCEPT ![self] = Head(shards[self])]
                                   /\ shards' = [shards EXCEPT ![self] = Tail(shards[self])]
                                   /\ /\ data' = [data EXCEPT ![self] = shard'[self][3]]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "hash",
                                                                               pc        |->  "label",
                                                                               data      |->  data[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "hash_"]
                                   /\ UNCHANGED << result_broadcast_val, 
                                                   broadcast_val_arg_1, 
                                                   root_hash, loop_result >>
                              ELSE /\ result_broadcast_val' = [result_broadcast_val EXCEPT ![self] = loop_result[self]]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ loop_result' = [loop_result EXCEPT ![self] = Head(stack[self]).loop_result]
                                   /\ shard' = [shard EXCEPT ![self] = Head(stack[self]).shard]
                                   /\ broadcast_val_arg_1' = [broadcast_val_arg_1 EXCEPT ![self] = Head(stack[self]).broadcast_val_arg_1]
                                   /\ root_hash' = [root_hash EXCEPT ![self] = Head(stack[self]).root_hash]
                                   /\ shards' = [shards EXCEPT ![self] = Head(stack[self]).shards]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ data' = data
                        /\ UNCHANGED << result_handle_new, result_handle_input, 
                                        result_rs_encode, result_hash, 
                                        rs_encode_arg_1, data_, i, n, f, rbc, 
                                        input, shards_, root_hash_, msgs >>

label(self) == /\ pc[self] = "label"
               /\ loop_result' = [loop_result EXCEPT ![self] = Append(loop_result[self], <<shard[self][1], <<<<"VAL", root_hash[self], result_hash[self], shard[self]>>>>>>)]
               /\ pc' = [pc EXCEPT ![self] = "broadcast_val_"]
               /\ UNCHANGED << result_handle_new, result_handle_input, 
                               result_rs_encode, result_hash, 
                               result_broadcast_val, stack, rs_encode_arg_1, 
                               data_, data, broadcast_val_arg_1, root_hash, 
                               shards, shard, i, n, f, rbc, input, shards_, 
                               root_hash_, msgs >>

broadcast_val(self) == broadcast_val_(self) \/ label(self)

handle_new_(self) == /\ pc[self] = "handle_new_"
                     /\ result_handle_new' = <<"ok", [i |-> i[self], n |-> n[self], f |-> f[self]], {}, NULL>>
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << result_handle_input, result_rs_encode, 
                                     result_hash, result_broadcast_val, stack, 
                                     rs_encode_arg_1, data_, data, 
                                     broadcast_val_arg_1, root_hash, shards, 
                                     loop_result, shard, i, n, f, rbc, input, 
                                     shards_, root_hash_, msgs >>

handle_new(self) == handle_new_(self)

handle_input_(self) == /\ pc[self] = "handle_input_"
                       /\ IF rbc[self]["n"] = 1
                             THEN /\ rbc' = [rbc EXCEPT ![self]["decoded"] = input[self],
                                                        ![self]["output"] = TRUE]
                                  /\ result_handle_input' = <<"ok", rbc'[self], {}, input[self]>>
                                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << stack, rs_encode_arg_1, 
                                                  data_ >>
                             ELSE /\ /\ data_' = [data_ EXCEPT ![self] = input[self]]
                                     /\ rs_encode_arg_1' = [rs_encode_arg_1 EXCEPT ![self] = rbc[self]]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "rs_encode",
                                                                              pc        |->  "result_rs_encode_",
                                                                              rs_encode_arg_1 |->  rs_encode_arg_1[self],
                                                                              data_     |->  data_[self] ] >>
                                                                          \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "rs_encode_"]
                                  /\ UNCHANGED << result_handle_input, rbc >>
                       /\ UNCHANGED << result_handle_new, result_rs_encode, 
                                       result_hash, result_broadcast_val, data, 
                                       broadcast_val_arg_1, root_hash, shards, 
                                       loop_result, shard, i, n, f, input, 
                                       shards_, root_hash_, msgs >>

result_rs_encode_(self) == /\ pc[self] = "result_rs_encode_"
                           /\ shards_' = [shards_ EXCEPT ![self] = result_rs_encode[self]]
                           /\ PrintT(<<"shards: ", shards_'[self]>>)
                           /\ /\ data' = [data EXCEPT ![self] = input[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "hash",
                                                                       pc        |->  "result_hash_",
                                                                       data      |->  data[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "hash_"]
                           /\ UNCHANGED << result_handle_new, 
                                           result_handle_input, 
                                           result_rs_encode, result_hash, 
                                           result_broadcast_val, 
                                           rs_encode_arg_1, data_, 
                                           broadcast_val_arg_1, root_hash, 
                                           shards, loop_result, shard, i, n, f, 
                                           rbc, input, root_hash_, msgs >>

result_hash_(self) == /\ pc[self] = "result_hash_"
                      /\ root_hash_' = [root_hash_ EXCEPT ![self] = result_hash[self]]
                      /\ PrintT(<<"hash: ", root_hash_'[self]>>)
                      /\ /\ broadcast_val_arg_1' = [broadcast_val_arg_1 EXCEPT ![self] = rbc[self]]
                         /\ root_hash' = [root_hash EXCEPT ![self] = root_hash_'[self]]
                         /\ shards' = [shards EXCEPT ![self] = shards_[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast_val",
                                                                  pc        |->  "result_broadcast_val_",
                                                                  loop_result |->  loop_result[self],
                                                                  shard     |->  shard[self],
                                                                  broadcast_val_arg_1 |->  broadcast_val_arg_1[self],
                                                                  root_hash |->  root_hash[self],
                                                                  shards    |->  shards[self] ] >>
                                                              \o stack[self]]
                      /\ loop_result' = [loop_result EXCEPT ![self] = <<>>]
                      /\ shard' = [shard EXCEPT ![self] = defaultInitValue]
                      /\ pc' = [pc EXCEPT ![self] = "broadcast_val_"]
                      /\ UNCHANGED << result_handle_new, result_handle_input, 
                                      result_rs_encode, result_hash, 
                                      result_broadcast_val, rs_encode_arg_1, 
                                      data_, data, i, n, f, rbc, input, 
                                      shards_, msgs >>

result_broadcast_val_(self) == /\ pc[self] = "result_broadcast_val_"
                               /\ msgs' = [msgs EXCEPT ![self] = result_broadcast_val[self]]
                               /\ PrintT(<<"broadcast val: ", msgs'[self]>>)
                               /\ result_handle_input' = <<"ok", rbc[self], msgs'[self], NULL>>
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << result_handle_new, 
                                               result_rs_encode, result_hash, 
                                               result_broadcast_val, stack, 
                                               rs_encode_arg_1, data_, data, 
                                               broadcast_val_arg_1, root_hash, 
                                               shards, loop_result, shard, i, 
                                               n, f, rbc, input, shards_, 
                                               root_hash_ >>

handle_input(self) == handle_input_(self) \/ result_rs_encode_(self)
                         \/ result_hash_(self)
                         \/ result_broadcast_val_(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ rs_encode(self) \/ hash(self)
                               \/ broadcast_val(self))
           \/ (\E self \in {"handle_new"}: handle_new(self))
           \/ (\E self \in {"handle_input"}: handle_input(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



========================================================================
