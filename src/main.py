from cx_cancellation import CX_Cancellation
from bad_pass import BadPass
from no_while_pass import NoWhilePass
from verifier import verify_vc
from preprocessor import get_vcs
from mk_axioms import mk_axioms
from ctx import Ctx
import time

def verify_pass(compiler_pass):
    print("Verifying pass", compiler_pass)
    start = time.time()

    vcs = get_vcs(compiler_pass)
    axioms = mk_axioms()
    ctx = Ctx()

    preprocessor_time = time.time() - start    

    for vc in vcs:
        # vc.dump()
        verify_vc(vc, axioms, ctx)
    
    end = time.time()
    print(f"Preprocessor time: {preprocessor_time}s")
    print(f"Total verification time: {end - start}s")
    print("")

def run_pass(compiler_pass, circuit):
    compiler_pass(circuit)
        
verify_pass(CX_Cancellation.run) # Verifies correctly
verify_pass(BadPass.run) # Rejects correctly
verify_pass(NoWhilePass.run) # Errors, not in correct while loop format