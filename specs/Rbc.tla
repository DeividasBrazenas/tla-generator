--------------------------------- MODULE Rbc ---------------------------------
EXTENDS Naturals, Sequences
CONSTANT NULL
CONSTANTS in_handle_new_arg_1, in_handle_input_rbc, in_handle_input_input

(*--algorithm Rbc
variables result_rs_encode, result_rs_decode, result_hash, result_broadcast_ready, result_broadcast_val, 
result_broadcast_echo, result_maybe_output, result_handle_new, result_handle_input, result_handle_message;

macro rs_encode(rs_encode_arg_1, data)
begin
end macro;

macro rs_decode(rs_decode_arg_1, shards)
begin
end macro;

macro hash(data)
begin
end macro;

macro broadcast_ready(broadcast_ready_arg_1, root_hash)
begin
end macro;

macro broadcast_val(broadcast_val_arg_1, root_hash, shards)
begin
end macro;

macro broadcast_echo(broadcast_echo_arg_1, root_hash, shard_hash, shard)
begin
end macro;

macro maybe_output(rbc, root_hash)
begin
end macro;

procedure handle_new(handle_new_arg_1)
begin
  handle_new:
    result_handle_new := <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>;
    return;
end procedure;

procedure handle_input(rbc, input)
variables shards, root_hash, msgs;
begin
  handle_input:
    if rbc["n"] = 1 then
      rbc["decoded"] := input
      || rbc["output"] := TRUE;

      result_handle_input := <<"ok", rbc, {}, input>>;
    else
      rs_encode(rbc, input);
      shards := result_rs_encode;

      hash(input);
      root_hash := result_hash;

      broadcast_val(rbc, root_hash, shards);
      msgs := result_broadcast_val;

      result_handle_input := <<"ok", rbc, msgs, NULL>>;
    end if;
end procedure;
\*
\*procedure handle_message(rbc, handle_message_arg_1)
\*variables new_shards, decoded, msgs, new_ready, new_rbc
\*begin
\*  handle_message:
\*    if handle_message_arg_1[1] = "VAL" then
\*      broadcast_echo(rbc, handle_message_arg_1[2], handle_message_arg_1[3], handle_message_arg_1[4]);
\*      msgs := result_broadcast_echo;
\*      
\*      result_handle_message := <<"ok", rbc, msgs, NULL>>;
\*    elsif handle_message_arg_1[1] = "ECHO" then
\*      hash(handle_message_arg_1[4][3]);
\*      
\*      if result_hash = handle_message_arg_1[3] then
\*        new_shards := rbc["shards"];
\*        new_shards[handle_message_arg_1[4][1]] := handle_message_arg_1[4];
\*        rbc["shards"] := new_shards;
\*        
\*        if Len(DOMAIN new_shards) >= rbc["n"] - rbc["f"] then
\*          rs_decode(rbc, new_shards);
\*          decoded := result_rs_decode;
\*          rbc["decoded"] := decoded;
\*          
\*          if rbc["i"] \in DOMAIN rbc["ready"] then
\*            maybe_output(rbc, handle_message_arg_1[2]);
\*            result_handle_message := result_maybe_output;
\*          else
\*            broadcast_ready(rbc, root_hash);
\*            msgs := result_broadcast_ready;
\*            result_handle_message := <<"ok", rbc, msgs, NULL>>
\*          end if;
\*        else
\*          maybe_output(rbc, handle_message_arg_1[2]);
\*          result_handle_message := result_maybe_output;
\*        end if;
\*      else
\*        maybe_output(rbc, handle_message_arg_1[2]);
\*        result_handle_message := result_maybe_output;
\*      end if;
\*    elsif handle_message_arg_1[1] = "READY" then
\*      new_ready := rbc["ready"];
\*      new_ready[handle_message_arg_1[2]] := handle_message_arg_1[3];
\*      new_rbc := rbc;
\*      new_rbc["ready"] := new_ready;
\*      
\*    end if;
\*end procedure;

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
\* BEGIN TRANSLATION (chksum(pcal) = "49fa937a" /\ chksum(tla) = "6558e3be")
\* Label handle_new of procedure handle_new at line 41 col 5 changed to handle_new_
\* Label handle_input of procedure handle_input at line 49 col 5 changed to handle_input_
\* Label handle_new at line 117 col 5 changed to handle_new_1
CONSTANT defaultInitValue
VARIABLES result_rs_encode, result_rs_decode, result_hash, 
          result_broadcast_ready, result_broadcast_val, result_broadcast_echo, 
          result_maybe_output, result_handle_new, result_handle_input, 
          result_handle_message, pc, stack, handle_new_arg_1, rbc, input, 
          shards, root_hash, msgs

vars == << result_rs_encode, result_rs_decode, result_hash, 
           result_broadcast_ready, result_broadcast_val, 
           result_broadcast_echo, result_maybe_output, result_handle_new, 
           result_handle_input, result_handle_message, pc, stack, 
           handle_new_arg_1, rbc, input, shards, root_hash, msgs >>

Init == (* Global variables *)
        /\ result_rs_encode = defaultInitValue
        /\ result_rs_decode = defaultInitValue
        /\ result_hash = defaultInitValue
        /\ result_broadcast_ready = defaultInitValue
        /\ result_broadcast_val = defaultInitValue
        /\ result_broadcast_echo = defaultInitValue
        /\ result_maybe_output = defaultInitValue
        /\ result_handle_new = defaultInitValue
        /\ result_handle_input = defaultInitValue
        /\ result_handle_message = defaultInitValue
        (* Procedure handle_new *)
        /\ handle_new_arg_1 = defaultInitValue
        (* Procedure handle_input *)
        /\ rbc = defaultInitValue
        /\ input = defaultInitValue
        /\ shards = defaultInitValue
        /\ root_hash = defaultInitValue
        /\ msgs = defaultInitValue
        /\ stack = << >>
        /\ pc = "handle_new_1"

handle_new_ == /\ pc = "handle_new_"
               /\ result_handle_new' = <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>
               /\ pc' = Head(stack).pc
               /\ handle_new_arg_1' = Head(stack).handle_new_arg_1
               /\ stack' = Tail(stack)
               /\ UNCHANGED << result_rs_encode, result_rs_decode, result_hash, 
                               result_broadcast_ready, result_broadcast_val, 
                               result_broadcast_echo, result_maybe_output, 
                               result_handle_input, result_handle_message, rbc, 
                               input, shards, root_hash, msgs >>

handle_new == handle_new_

handle_input_ == /\ pc = "handle_input_"
                 /\ IF rbc["n"] = 1
                       THEN /\ rbc' = [rbc EXCEPT !["decoded"] = input,
                                                  !["output"] = TRUE]
                            /\ result_handle_input' = <<"ok", rbc', {}, input>>
                            /\ UNCHANGED << shards, root_hash, msgs >>
                       ELSE /\ shards' = result_rs_encode
                            /\ root_hash' = result_hash
                            /\ msgs' = result_broadcast_val
                            /\ result_handle_input' = <<"ok", rbc, msgs', NULL>>
                            /\ rbc' = rbc
                 /\ pc' = "Error"
                 /\ UNCHANGED << result_rs_encode, result_rs_decode, 
                                 result_hash, result_broadcast_ready, 
                                 result_broadcast_val, result_broadcast_echo, 
                                 result_maybe_output, result_handle_new, 
                                 result_handle_message, stack, 
                                 handle_new_arg_1, input >>

handle_input == handle_input_

handle_new_1 == /\ pc = "handle_new_1"
                /\ /\ handle_new_arg_1' = in_handle_new_arg_1
                   /\ stack' = << [ procedure |->  "handle_new",
                                    pc        |->  "Done",
                                    handle_new_arg_1 |->  handle_new_arg_1 ] >>
                                \o stack
                /\ pc' = "handle_new_"
                /\ UNCHANGED << result_rs_encode, result_rs_decode, 
                                result_hash, result_broadcast_ready, 
                                result_broadcast_val, result_broadcast_echo, 
                                result_maybe_output, result_handle_new, 
                                result_handle_input, result_handle_message, 
                                rbc, input, shards, root_hash, msgs >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == handle_new \/ handle_input \/ handle_new_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

===============================================================================
