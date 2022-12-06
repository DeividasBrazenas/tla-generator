------------------------------ MODULE GeneratedRbc ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS handle_new_arg_1, handle_new_arg_1, rbc, input, NULL

(*--algorithm Rbc
  variables result_handle_new, result_handle_input, result_broadcast_val, result_rs_encode, result_hash


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



        result_handle_input := <<"ok", rbc, , NULL>>;
      end if;
  end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3ff2380" /\ chksum(tla) = "8c762d08")
\* Label handle_new of process handle_new at line 13 col 7 changed to handle_new_
\* Label handle_input of process handle_input at line 20 col 7 changed to handle_input_
CONSTANT defaultInitValue
VARIABLES result_handle_new, result_handle_input, result_broadcast_val, 
          result_rs_encode, result_hash, pc, handle_new_arg_1, rbc, input, 
          shards, root_hash, msgs

vars == << result_handle_new, result_handle_input, result_broadcast_val, 
           result_rs_encode, result_hash, pc, handle_new_arg_1, rbc, input, 
           shards, root_hash, msgs >>

ProcSet == {"handle_new"} \cup {"handle_input"}

Init == (* Global variables *)
        /\ result_handle_new = defaultInitValue
        /\ result_handle_input = defaultInitValue
        /\ result_broadcast_val = defaultInitValue
        /\ result_rs_encode = defaultInitValue
        /\ result_hash = defaultInitValue
        (* Process handle_new *)
        /\ handle_new_arg_1 = input_handle_new_handle_new_arg_1
        (* Process handle_input *)
        /\ rbc = input_handle_input_rbc
        /\ input = input_handle_input_input
        /\ shards = defaultInitValue
        /\ root_hash = defaultInitValue
        /\ msgs = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "handle_new" -> "handle_new_"
                                        [] self = "handle_input" -> "handle_input_"]

handle_new_ == /\ pc["handle_new"] = "handle_new_"
               /\ result_handle_new' = <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>
               /\ pc' = [pc EXCEPT !["handle_new"] = "Done"]
               /\ UNCHANGED << result_handle_input, result_broadcast_val, 
                               result_rs_encode, result_hash, handle_new_arg_1, 
                               rbc, input, shards, root_hash, msgs >>

handle_new == handle_new_

handle_input_ == /\ pc["handle_input"] = "handle_input_"
                 /\ IF rbc["n"] = 1
                       THEN /\ rbc' = [rbc EXCEPT !["decoded"] = input,
                                                  !["output"] = TRUE]
                            /\ result_handle_input' = <<"ok", rbc', {}, input>>
                       ELSE /\ result_handle_input' = <<"ok", rbc, , NULL>>
                            /\ rbc' = rbc
                 /\ pc' = [pc EXCEPT !["handle_input"] = "Done"]
                 /\ UNCHANGED << result_handle_new, result_broadcast_val, 
                                 result_rs_encode, result_hash, 
                                 handle_new_arg_1, input, shards, root_hash, 
                                 msgs >>

handle_input == handle_input_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == handle_new \/ handle_input
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
========================================================================
