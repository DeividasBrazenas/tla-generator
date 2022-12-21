--------------------------- MODULE PoCPCalMaxSrv_ImplSrv ---------------------------
(*
This file models the implementation of the handle_call({max, ...}) function.
That's a very much approximate translation. Probably a loop would not suffice.

    1: def handle_call({:max, items}, _from, state) do
    2:    [first | others] = items
    3:    max = Enum.reduce(others, first, &Kernel.max(&1, &2))
    4:    {:reply, max, state}
    5: end

Here we assume items is a set and not a list (no order is assumed).
*)
EXTENDS Naturals, Sequences, SequencesExt, TLC 
CONSTANT ITEMS
CONSTANT NIL

--------------------------------------------------------------------------------
(*
Here we define actions line-by-line. That's ad-hoc translation.
Need to think, how recursion should be encoded. Maybe there are some refs on that?
*)

(*--algorithm PoCPCalMaxSrv_ImplSrv
variables result_handle_call = <<NIL, NIL, NIL>>,
          items, first, others, index, max;

define 
    kernel_max(a, b) == IF a > b THEN a ELSE b 
end define;

\* def handle_call({:max, items}, _from, state) do
procedure handle_call(arg_1, arg_2, state)
begin
handle_call_b:
    if arg_1[1] = "max" then
        items := SetToSeq(arg_1[2]);
        
        call handle_call_1(arg_1, arg_2, state);
        return;
    end if;
end procedure;

\* [first | others] = items
procedure handle_call_1(arg_1, arg_2, state)
begin
handle_call_1_b:
    first := Head(items);
    others := Tail(items);

    call handle_call_2(arg_1, arg_2, state);
    return;
end procedure;

\* max = Enum.reduce(others, first, &Kernel.max(&1, &2))
procedure handle_call_2(arg_1, arg_2, state)
begin
handle_call_2_b:
    index := 1;
    loop:
        while index <= Len(others) do
            max := kernel_max(others[index], first);
            index := index + 1;
        end while;

        call handle_call_3(arg_1, arg_2, state);
        return;
end procedure;

\* {:reply, max, state}
procedure handle_call_3(arg_1, arg_2, state)
begin
    handle_call_3_b:
        result_handle_call := <<"reply", max, state>>;
        return;
end procedure;

fair process execute = "execute"
begin
    exec:
    call handle_call(<<"max", ITEMS>>, NIL, NIL);
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a5b70b14" /\ chksum(tla) = "9030d70c")
\* Parameter arg_1 of procedure handle_call at line 33 col 23 changed to arg_1_
\* Parameter arg_2 of procedure handle_call at line 33 col 30 changed to arg_2_
\* Parameter state of procedure handle_call at line 33 col 37 changed to state_
\* Parameter arg_1 of procedure handle_call_1 at line 45 col 25 changed to arg_1_h
\* Parameter arg_2 of procedure handle_call_1 at line 45 col 32 changed to arg_2_h
\* Parameter state of procedure handle_call_1 at line 45 col 39 changed to state_h
\* Parameter arg_1 of procedure handle_call_2 at line 56 col 25 changed to arg_1_ha
\* Parameter arg_2 of procedure handle_call_2 at line 56 col 32 changed to arg_2_ha
\* Parameter state of procedure handle_call_2 at line 56 col 39 changed to state_ha
CONSTANT defaultInitValue
VARIABLES result_handle_call, items, first, others, index, max, pc, stack

(* define statement *)
kernel_max(a, b) == IF a > b THEN a ELSE b

VARIABLES arg_1_, arg_2_, state_, arg_1_h, arg_2_h, state_h, arg_1_ha, 
          arg_2_ha, state_ha, arg_1, arg_2, state

vars == << result_handle_call, items, first, others, index, max, pc, stack, 
           arg_1_, arg_2_, state_, arg_1_h, arg_2_h, state_h, arg_1_ha, 
           arg_2_ha, state_ha, arg_1, arg_2, state >>

ProcSet == {"execute"}

Init == (* Global variables *)
        /\ result_handle_call = <<NIL, NIL, NIL>>
        /\ items = defaultInitValue
        /\ first = defaultInitValue
        /\ others = defaultInitValue
        /\ index = defaultInitValue
        /\ max = defaultInitValue
        (* Procedure handle_call *)
        /\ arg_1_ = [ self \in ProcSet |-> defaultInitValue]
        /\ arg_2_ = [ self \in ProcSet |-> defaultInitValue]
        /\ state_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure handle_call_1 *)
        /\ arg_1_h = [ self \in ProcSet |-> defaultInitValue]
        /\ arg_2_h = [ self \in ProcSet |-> defaultInitValue]
        /\ state_h = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure handle_call_2 *)
        /\ arg_1_ha = [ self \in ProcSet |-> defaultInitValue]
        /\ arg_2_ha = [ self \in ProcSet |-> defaultInitValue]
        /\ state_ha = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure handle_call_3 *)
        /\ arg_1 = [ self \in ProcSet |-> defaultInitValue]
        /\ arg_2 = [ self \in ProcSet |-> defaultInitValue]
        /\ state = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "exec"]

handle_call_b(self) == /\ pc[self] = "handle_call_b"
                       /\ IF arg_1_[self][1] = "max"
                             THEN /\ items' = SetToSeq(arg_1_[self][2])
                                  /\ /\ arg_1_h' = [arg_1_h EXCEPT ![self] = arg_1_[self]]
                                     /\ arg_2_h' = [arg_2_h EXCEPT ![self] = arg_2_[self]]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "handle_call_1",
                                                                              pc        |->  Head(stack[self]).pc,
                                                                              arg_1_h   |->  arg_1_h[self],
                                                                              arg_2_h   |->  arg_2_h[self],
                                                                              state_h   |->  state_h[self] ] >>
                                                                          \o Tail(stack[self])]
                                     /\ state_h' = [state_h EXCEPT ![self] = state_[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "handle_call_1_b"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                                  /\ UNCHANGED << items, stack, arg_1_h, 
                                                  arg_2_h, state_h >>
                       /\ UNCHANGED << result_handle_call, first, others, 
                                       index, max, arg_1_, arg_2_, state_, 
                                       arg_1_ha, arg_2_ha, state_ha, arg_1, 
                                       arg_2, state >>

handle_call(self) == handle_call_b(self)

handle_call_1_b(self) == /\ pc[self] = "handle_call_1_b"
                         /\ first' = Head(items)
                         /\ others' = Tail(items)
                         /\ /\ arg_1_ha' = [arg_1_ha EXCEPT ![self] = arg_1_h[self]]
                            /\ arg_2_ha' = [arg_2_ha EXCEPT ![self] = arg_2_h[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "handle_call_2",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     arg_1_ha  |->  arg_1_ha[self],
                                                                     arg_2_ha  |->  arg_2_ha[self],
                                                                     state_ha  |->  state_ha[self] ] >>
                                                                 \o Tail(stack[self])]
                            /\ state_ha' = [state_ha EXCEPT ![self] = state_h[self]]
                         /\ pc' = [pc EXCEPT ![self] = "handle_call_2_b"]
                         /\ UNCHANGED << result_handle_call, items, index, max, 
                                         arg_1_, arg_2_, state_, arg_1_h, 
                                         arg_2_h, state_h, arg_1, arg_2, state >>

handle_call_1(self) == handle_call_1_b(self)

handle_call_2_b(self) == /\ pc[self] = "handle_call_2_b"
                         /\ index' = 1
                         /\ pc' = [pc EXCEPT ![self] = "loop"]
                         /\ UNCHANGED << result_handle_call, items, first, 
                                         others, max, stack, arg_1_, arg_2_, 
                                         state_, arg_1_h, arg_2_h, state_h, 
                                         arg_1_ha, arg_2_ha, state_ha, arg_1, 
                                         arg_2, state >>

loop(self) == /\ pc[self] = "loop"
              /\ IF index <= Len(others)
                    THEN /\ max' = kernel_max(others[index], first)
                         /\ index' = index + 1
                         /\ pc' = [pc EXCEPT ![self] = "loop"]
                         /\ UNCHANGED << stack, arg_1, arg_2, state >>
                    ELSE /\ /\ arg_1' = [arg_1 EXCEPT ![self] = arg_1_ha[self]]
                            /\ arg_2' = [arg_2 EXCEPT ![self] = arg_2_ha[self]]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "handle_call_3",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     arg_1     |->  arg_1[self],
                                                                     arg_2     |->  arg_2[self],
                                                                     state     |->  state[self] ] >>
                                                                 \o Tail(stack[self])]
                            /\ state' = [state EXCEPT ![self] = state_ha[self]]
                         /\ pc' = [pc EXCEPT ![self] = "handle_call_3_b"]
                         /\ UNCHANGED << index, max >>
              /\ UNCHANGED << result_handle_call, items, first, others, arg_1_, 
                              arg_2_, state_, arg_1_h, arg_2_h, state_h, 
                              arg_1_ha, arg_2_ha, state_ha >>

handle_call_2(self) == handle_call_2_b(self) \/ loop(self)

handle_call_3_b(self) == /\ pc[self] = "handle_call_3_b"
                         /\ result_handle_call' = <<"reply", max, state[self]>>
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ arg_1' = [arg_1 EXCEPT ![self] = Head(stack[self]).arg_1]
                         /\ arg_2' = [arg_2 EXCEPT ![self] = Head(stack[self]).arg_2]
                         /\ state' = [state EXCEPT ![self] = Head(stack[self]).state]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << items, first, others, index, max, 
                                         arg_1_, arg_2_, state_, arg_1_h, 
                                         arg_2_h, state_h, arg_1_ha, arg_2_ha, 
                                         state_ha >>

handle_call_3(self) == handle_call_3_b(self)

exec == /\ pc["execute"] = "exec"
        /\ /\ arg_1_' = [arg_1_ EXCEPT !["execute"] = <<"max", ITEMS>>]
           /\ arg_2_' = [arg_2_ EXCEPT !["execute"] = NIL]
           /\ stack' = [stack EXCEPT !["execute"] = << [ procedure |->  "handle_call",
                                                         pc        |->  "Done",
                                                         arg_1_    |->  arg_1_["execute"],
                                                         arg_2_    |->  arg_2_["execute"],
                                                         state_    |->  state_["execute"] ] >>
                                                     \o stack["execute"]]
           /\ state_' = [state_ EXCEPT !["execute"] = NIL]
        /\ pc' = [pc EXCEPT !["execute"] = "handle_call_b"]
        /\ UNCHANGED << result_handle_call, items, first, others, index, max, 
                        arg_1_h, arg_2_h, state_h, arg_1_ha, arg_2_ha, 
                        state_ha, arg_1, arg_2, state >>

execute == exec

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == execute
           \/ (\E self \in ProcSet:  \/ handle_call(self) \/ handle_call_1(self)
                                     \/ handle_call_2(self) \/ handle_call_3(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(execute)
           /\ WF_vars(handle_call("execute"))
           /\ WF_vars(handle_call_1("execute"))
           /\ WF_vars(handle_call_2("execute"))
           /\ WF_vars(handle_call_3("execute"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

================================================================================
