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

def _pp(expr) -> str:
    if isinstance(expr, Var):
        return expr.name

    elif isinstance(expr, Eq):
        return f"({_pp(expr.lhs)} = {_pp(expr.rhs)})"

    elif isinstance(expr, And):
        if not expr.args:
            return "true"
        return "(" + " ∧ ".join(_pp(a) for a in expr.args) + ")"

    elif isinstance(expr, Not):
        return f"¬({_pp(expr.e)})"

    elif isinstance(expr, Implies):
        return f"({_pp(expr.prem)} ⇒ {_pp(expr.concl)})"

    elif isinstance(expr, App):
        args = ", ".join(_pp(a) for a in expr.args)
        return f"{expr.func_name}({args})"

    elif isinstance(expr, ForAll):
        vars_str = ", ".join(f"{v.name}:{v.sort}" for v in expr.vars)
        return f"(∀ {vars_str}. {_pp(expr.body)})"

    else:
        return repr(expr)


from dataclasses import dataclass

@dataclass
class VC:
    name: str                   # e.g. "loop_init", "path_C_preservation"
    assumptions: list[Expr]     # invariants, branch conditions, helper specs, axioms
    goal: Expr 
    
    def dump(self, indent: int = 2):
        pad = " " * indent

        print(f"VC: {self.name}")
        print("-" * 40)

        if self.assumptions:
            print("ASSUMPTIONS:")
            for i, a in enumerate(self.assumptions, 1):
                print(f"{pad}({i}) {_pp(a)}")
        else:
            print("ASSUMPTIONS: (none)")

        print("-" * 40)
        print("GOAL:")
        print(f"{pad}{_pp(self.goal)}")
        print()