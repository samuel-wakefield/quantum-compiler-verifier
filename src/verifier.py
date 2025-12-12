# --verifier.py--

import z3
import time
from VC import *

def encode_expr(e, ctx):
    # ctx maps your sorts/names → z3 Sorts and FuncDecls
    if isinstance(e, Var):
        return ctx.var(e.name, e.sort)
    if isinstance(e, Eq):
        return encode_expr(e.lhs, ctx) == encode_expr(e.rhs, ctx)
    if isinstance(e, And):
        return z3.And(*(encode_expr(a, ctx) for a in e.args))
    if isinstance(e, Not):
        return z3.Not(encode_expr(e.e, ctx))
    if isinstance(e, Implies):
        return z3.Implies(encode_expr(e.prem, ctx), encode_expr(e.concl, ctx))
    if isinstance(e, App):
        f = ctx.func(e.func_name)
        if e.args:# e.g. denote : Circuit → Unitary
            return f(*(encode_expr(a, ctx) for a in e.args))
        else:
            return f
    if isinstance(e, ForAll):
        # bind new Z3 vars for the quantifier
        z3_vars = [ctx.var(v.name, v.sort) for v in e.vars]
        return z3.ForAll(z3_vars, encode_expr(e.body, ctx))
    raise TypeError(e)

def verify_vc(vc: VC, axioms: list[Expr], ctx) -> bool:
    start = time.time()
    s = z3.Solver()
    s.set("timeout", 2_469)
    # add global axioms (rewrite rules, semantic laws)
    for ax in axioms:
        s.add(encode_expr(ax, ctx))

    # add VC-specific assumptions
    for a in vc.assumptions:
        s.add(encode_expr(a, ctx))

    # assert negation of goal
    s.add(z3.Not(encode_expr(vc.goal, ctx)))

    res = s.check()
    end = time.time()
    vt = end-start
    if res == z3.unsat:
        print(f"{vc.name:25s}: ✔ VALID - {vt}s")
        return True

    else:
        print(f"{vc.name:25s}: ✘ NOT VALID - {vt}s")

        return False