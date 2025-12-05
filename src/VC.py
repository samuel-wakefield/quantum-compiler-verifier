# --VC.py--

class Expr:  # base class
    pass

class Var(Expr):
    def __init__(self, name, sort):
        self.name = name
        self.sort = sort  # "Circuit", "Gate", "Int", etc.

class Eq(Expr):
    def __init__(self, lhs, rhs):
        self.lhs, self.rhs = lhs, rhs

class And(Expr):
    def __init__(self, *args):
        self.args = list(args)

class Not(Expr):
    def __init__(self, e):
        self.e = e

class Implies(Expr):
    def __init__(self, prem, concl):
        self.prem, self.concl = prem, concl

class App(Expr):
    def __init__(self, func_name, *args):
        self.func_name = func_name   # e.g. "denote", "concat", "equivalent"
        self.args = list(args)

class ForAll(Expr):
    def __init__(self, vars, body):
        self.vars = vars
        self.body = body


from dataclasses import dataclass

@dataclass
class VC:
    name: str                   # e.g. "loop_init", "path_C_preservation"
    assumptions: list[Expr]     # invariants, branch conditions, helper specs, axioms
    goal: Expr 