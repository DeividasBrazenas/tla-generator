------------------------------ MODULE GeneratedRbc ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS in_handle_new_arg_1, in_handle_new_arg_0, in_rbc, in_input, in_broadcast_val_arg_1, in_broadcast_val_arg_0, in_rs_encode_arg_1, in_rs_encode_arg_0, in_hash_arg_1, in_hash_arg_0, NULL

(*--algorithm Rbc
  variables result_handle_new, result_handle_input, result_broadcast_val, result_rs_encode, result_hash

  procedure handle_new(handle_new_arg_1, handle_new_arg_0)
  begin
    handle_new:
      result_handle_new := <<"ok", [i |-> handle_new_arg_1[1], n |-> handle_new_arg_1[2], f |-> handle_new_arg_1[3]], {}, NULL>>;
      return;
  end procedure

  procedure handle_input(rbc, input)
  begin
    handle_input:
      if rbc["n"] = 1 then
        rbc["decoded"] := input
        || rbc["output"] := TRUE;
        result_handle_input := <<"ok", rbc, {}, input>>;
        return;
      else



        result_handle_input := <<"ok", rbc, , NULL>>;
        return;
      end if;
  end procedure

  begin
    handle_new:
      if result_handle_new = defaultInitValue then
        call handle_new(in_handle_new_arg_1, in_handle_new_arg_0)
      end if;
    handle_input:
      if result_handle_input = defaultInitValue then
        call handle_input(in_rbc, in_input)
      end if;
    broadcast_val:
      if result_broadcast_val = defaultInitValue then
        call broadcast_val(in_broadcast_val_arg_1, in_broadcast_val_arg_0)
      end if;
    rs_encode:
      if result_rs_encode = defaultInitValue then
        call rs_encode(in_rs_encode_arg_1, in_rs_encode_arg_0)
      end if;
    hash:
      if result_hash = defaultInitValue then
        call hash(in_hash_arg_1, in_hash_arg_0)
      end if;
end algorithm; *)
========================================================================