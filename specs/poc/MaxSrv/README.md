Files:

  - `PoCMaxSrv.tla` -- the abstract algorithm.
  - `PoCMaxSrvMC.{tla|cfg}` -- definitions for model checking the abstract algorithm.

  - `max_srv/lib/max_srv.ex` -- example implementation.
  - `PoCMaxSrv_ImplSrv.tla` -- we assume such spec is generated for a particular function.
    This covers the sequential part of the algorithm.
  - `PoCMaxSrv_ImplSrv_REF.tla` -- here we try to show that PoCMaxSrv_ImplSrv is a
    refinement of the `Srv` action in the `PoCMaxSrv` spec.
