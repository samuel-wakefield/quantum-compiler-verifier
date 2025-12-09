import z3

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
            "CXU": ("Qubit", "Qubit", "Unitary"),
            "is_CX": ("Gate", "Bool"),
            "Head": ("Circuit", "Gate"),
            "Tail": ("Circuit", "Circuit"),
            "same_qubits": ("Gate", "Gate", "Bool"),
            "all_disjoint": ("Gate", "Circuit", "Bool")
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

        sorts = self._signatures[name]
        f = z3.Function(name, *[self.sort(s) for s in sorts])
        self._funcs[name] = f
        return f