--------------------------- MODULE PoCMaxSrv_ImplSrv ---------------------------
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
EXTENDS Naturals
CONSTANT ITEMS
CONSTANT NIL
VARIABLE pc
VARIABLE items
VARIABLES first, others
VARIABLE acc
VARIABLE max
VARIABLE reply
vars == <<pc, items, first, others, acc, max, reply>>


--------------------------------------------------------------------------------
(*
Here we define actions line-by-line. That's ad-hoc translation.
Need to think, how recursion should be encoded. Maybe there are some refs on that?
*)

\* 1: def handle_call({:max, items}, _from, state) do
Line1 ==
    /\ pc = "line1"
    /\ items' = ITEMS
    /\ pc' = "line2"
    /\ UNCHANGED <<first, others, acc, max, reply>>


\* 2:    [first | others] = items
Line2 ==
    /\ pc = "line2"
    /\ \E f \in items:
        /\ first' = f
        /\ others' = items \ {f}
    /\ pc' = "line3Init"
    /\ UNCHANGED <<items, acc, max, reply>>

\* 3:    max = Enum.reduce(others, first, &Kernel.max(&1, &2))
\* Setup if the reduce function.
Line3Init ==
    /\ pc = "line3Init"
    /\ acc' = first
    /\ pc' = "line3Rec"
    /\ UNCHANGED <<items, first, others, max, reply>>

\* 3:    max = Enum.reduce(others, first, &Kernel.max(&1, &2))
\* Iteration of the reduce function.
Line3Rec ==
    /\ pc = "line3Rec"
    /\ \E i \in others:
        /\ acc' = IF i > acc THEN i ELSE acc
        /\ others' = others \ {i}
    /\ UNCHANGED <<pc, items, first, max, reply>>

\* 3:    max = Enum.reduce(others, first, &Kernel.max(&1, &2))
\* Termination of the reduce function.
Line3RecTerm ==
    /\ pc = "line3Rec"
    /\ others = {}
    /\ max' = acc
    /\ pc' = "line4"
    /\ UNCHANGED <<items, first, others, acc, reply>>

\* 4:    {:reply, max, state}
Line4 ==
    /\ pc = "line4"
    /\ reply' = acc
    /\ pc' = "term"
    /\ UNCHANGED <<items, first, others, acc, max>>

--------------------------------------------------------------------------------
Init ==
    /\ pc = "line1"
    /\ items = NIL
    /\ first = NIL
    /\ others = NIL
    /\ acc = NIL
    /\ max = NIL
    /\ reply = NIL

Next ==
    \/ Line1
    \/ Line2
    \/ Line3Init \/ Line3Rec \/ Line3RecTerm
    \/ Line4

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

================================================================================
