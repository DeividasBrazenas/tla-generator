------------------------- MODULE PoCMaxSrv_ImplSrv_REF -------------------------
EXTENDS PoCMaxSrv_ImplSrv

spec == INSTANCE PoCMaxSrv WITH
    params <- ITEMS,
    output <- NIL,
    msgs   <- IF reply = NIL
                THEN {[t |-> "req", items |-> ITEMS]}
                ELSE {[t |-> "req", items |-> ITEMS],
                      [t |-> "res", max |-> reply]}

AbsStepSrvNext == spec!Srv
AbsStepSrvSpec == [][AbsStepSrvNext]_<<reply>>

\* EventuallyStep == <><<AbsStepSrvNext>>_<<reply>> \* ERROR: Temporal formulas containing actions must be of forms <>[]A or []<>A.
\* EventuallyStep == (reply = NIL) ~> <<AbsStepSrvNext>>_<<reply>> \* ERROR: Action used where only temporal formula or state predicate allowed.
EventuallyStep == spec!SrvTermination

THEOREM Spec => /\ AbsStepSrvSpec \* Safety?
                /\ EventuallyStep \* Liveness?
PROOF OMITTED \* Checked using TLC.
================================================================================
