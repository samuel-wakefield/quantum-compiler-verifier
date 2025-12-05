# test_verifier.py

import z3

from VC import Var, Eq, Implies, VC, App, Not
from verifier import verify_vc
from mk_axioms import mk_axioms

class Ctx:
    """
    Very small context object for the encoder:
    - supports Bool and Int sorts (we only use Bool here)
    - provides var(name, sort) and func(name) as required by encode_expr
    """

    def __init__(self):
        self._vars = {}
        self._sorts = { "Unitary": z3.DeclareSort("Unitary") }
        self._funcs = { "Id": (z3.Const("Id", self._sorts["Unitary"])) }
        self._signatures = {
            "denote": ("Circuit", "Unitary"),
            "concat": ("Circuit", "Circuit", "Circuit"),
            "ucomp": ("Unitary", "Unitary", "Unitary"),
            "mk_single" : ("Gate", "Circuit"),
            "denote_gate": ("Gate", "Unitary"),
            "CX": ("Qubit", "Qubit", "Gate"),
            "disjoint" : ("Gate", "Gate", "Bool"),
            "CXU": ("Qubit", "Qubit", "Unitary")
            }

    def sort(self, name):
        """
        Returns a Z3 sort by name. Creates it if needed (as uninterpreted sort).
        """
        if name not in self._sorts:
            if name == "Int":
                self._sorts[name] = z3.IntSort()
            elif name == "Bool":
                self._sorts[name] = z3.BoolSort()
            else:
                # Circuit, Gate, Unitary, Qubit, etc.
                self._sorts[name] = z3.DeclareSort(name)
        return self._sorts[name]

    def signature(self, name):
        return self._signatures[name]

    def var(self, name, sort):
        key = (name, sort)
        if key in self._vars:
            return self._vars[key]

        if sort == "Bool":
            v = z3.Bool(name)
        elif sort == "Int":
            v = z3.Int(name)
        else:
            # generic uninterpreted sort if needed
            s = z3.DeclareSort(sort)
            v = z3.Const(name, s)

        self._vars[key] = v
        return v

    def func(self, name):
        if name in self._funcs:
            return self._funcs[name]

        sorts = self.signature(name)
        f = z3.Function(name, *[self.sort(s) for s in sorts])
        self._funcs[name] = f
        return f

def inv(output_var, remain_var, input_var):
    """
    Loop invariant I(output, remain):
        denote(concat(output, remain)) = denote(input)
    """
    return Eq(
        App("denote", App("concat", output_var, remain_var)),
        App("denote", input_var),
    )   

def build_vcs():
    ctx = Ctx()  # same ctx instance can be reused across VCs

    # Boolean variables (as Exprs)
    P = Var("P", "Bool")
    Q = Var("Q", "Bool")

    input_v  = Var("input",  "Circuit")
    output_v = Var("output", "Circuit")
    remain_v = Var("remain", "Circuit")
    
    output1_v = Var("output1", "Circuit")
    remain1_v = Var("remain1", "Circuit")
    
    empty_v = Var("empty", "Circuit")

    vcs = []

    # VC 1: Modus ponens: from P and (P -> Q), prove Q
    vc1 = VC(
        name="modus_ponens",
        assumptions=[
            P,                      # assert P is true
            Implies(P, Q),          # P -> Q
        ],
        goal=Q,                     # want to prove Q
    )
    vcs.append(vc1)
    
    vc_init = VC(
        name="loop_init",
        assumptions=[
            Eq(remain_v, input_v),   # remain = input at entry
            Eq(output_v, empty_v),   # output = []
        ],
        goal=inv(output_v, remain_v, input_v),
    )
    vcs.append(vc_init)
    
    vc_loop_exit = VC(
        name="loop_exit",
        assumptions=[
            Eq(remain_v, empty_v),
            inv(output_v, remain_v, input_v),
        ],
        goal=Eq(App("denote", output_v), App("denote", input_v)),
    )
    vcs.append(vc_loop_exit)

    return vcs, ctx

def main():
    axioms: list = mk_axioms()  # no global axioms for these tiny examples

    vcs, ctx = build_vcs()

    print("Running VC checks:\n")
    for vc in vcs:
        result = verify_vc(vc, axioms, ctx)
        status = "✔ VALID" if result else "✘ NOT VALID"
        print(f"{vc.name:25s}: {status}")

    # Basic assertions so this can act as a simple test script
    vc_results = {vc.name: verify_vc(vc, axioms, ctx) for vc in vcs}
    assert vc_results["modus_ponens"] is True
    assert vc_results["loop_init"] is True
    assert vc_results["loop_exit"] is True

    print("\nAll expected checks passed.")


if __name__ == "__main__":
    main()
