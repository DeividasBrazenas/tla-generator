OUTS = PoCMaxSrvMC.out PoCMaxSrv_ImplSrv_REF.out

all: $(OUTS)

PoCMaxSrvMC.out: PoCMaxSrvMC.cfg PoCMaxSrvMC.tla PoCMaxSrv.tla
	tlc -config $< $(word 2,$^) > $@

PoCMaxSrv_ImplSrv_REF.out: PoCMaxSrv_ImplSrv_REF.cfg PoCMaxSrv_ImplSrv_REF.tla PoCMaxSrv_ImplSrv.tla PoCMaxSrv.tla
	tlc -config $< $(word 2,$^) > $@

clean:
	rm -rf $(OUTS)

.PHONY: all clean
