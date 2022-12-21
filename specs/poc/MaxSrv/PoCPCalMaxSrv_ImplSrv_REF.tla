------------------------- MODULE PoCPCalMaxSrv_ImplSrv_REF -------------------------
EXTENDS PoCPCalMaxSrv_ImplSrv

spec == INSTANCE PoCMaxSrv WITH
    params <- ITEMS,
    output <- NIL,
    msgs   <- IF result_handle_call[2] = NIL
                THEN {[t |-> "req", items |-> ITEMS]}
                ELSE {[t |-> "req", items |-> ITEMS],
                      [t |-> "res", max |-> result_handle_call[2]]}

AbsStepSrvNext == spec!Srv
AbsStepSrvSpec == [][AbsStepSrvNext]_<<result_handle_call[2]>>

EventuallyStep == spec!SrvTermination

THEOREM Spec => /\ AbsStepSrvSpec \* Safety?
                /\ EventuallyStep \* Liveness?
PROOF OMITTED \* Checked using TLC.
================================================================================
