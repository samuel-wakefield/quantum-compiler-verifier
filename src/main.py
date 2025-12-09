from cx_cancellation import CX_Cancellation
from bad_pass import BadPass
from verifier import verify_vc
from preprocessor import get_vcs
from mk_axioms import mk_axioms
from ctx import Ctx

def verify_pass(compiler_pass):
    vcs = get_vcs(compiler_pass)
    axioms = mk_axioms()
    ctx = Ctx()

    for vc in vcs:
        verify_vc(vc, axioms, ctx)
        
verify_pass(CX_Cancellation.run)
verify_pass(BadPass.run)