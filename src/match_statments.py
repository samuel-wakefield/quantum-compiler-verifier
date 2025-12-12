import ast
from VC import *
from utility_spec import ng_specification

def spec_gate_from_remain_gates(stmt, vars):
    """
    gate = remain.gates[0]
      -> Eq(gate_v, App("Head", remain_v))
    """
    (input_v, output_v, remain_v,
     output1_v, remain1_v, gate_v, g_v, cM, cR) = vars

    if not isinstance(stmt, ast.Assign):
        return None
    if len(stmt.targets) != 1:
        return None

    target = stmt.targets[0]
    if not (isinstance(target, ast.Name) and target.id == "gate"):
        return None

    value = stmt.value
    # match `remain.gates[0]`
    if not isinstance(value, ast.Subscript):
        return None

    # value.value should be Attribute(Name("remain"), "gates")
    base = value.value
    if not (
        isinstance(base, ast.Attribute)
        and isinstance(base.value, ast.Name)
        and base.value.id == "remain"
        and base.attr == "gates"
    ):
        return None

    # slice should be 0
    index_node = value.slice
    if not (isinstance(index_node, ast.Constant) and index_node.value == 0):
        return None

    # We matched: gate = remain.gates[0]
    return Eq(gate_v, App("Head", remain_v))    


def spec_output_append_gate(stmt, vars):
    """
    output.append(gate)
      -> Eq(output1_v, App("concat", output_v, App("mk_single", gate_v)))
    """
    (input_v, output_v, remain_v, output1_v, remain1_v, gate_v, g_v, cM, cR) = vars
    if not isinstance(stmt, ast.Expr):
        return None

    call = stmt.value
    if not isinstance(call, ast.Call):
        return None

    # match output.append(...)
    func = call.func
    if not isinstance(func, ast.Attribute):
        return None
    if not (isinstance(func.value, ast.Name) and func.value.id == "output"):
        return None
    if func.attr != "append":
        return None

    # args: exactly one arg "gate"
    if len(call.args) != 1:
        return None
    arg = call.args[0]
    if not (isinstance(arg, ast.Name) and arg.id == "gate"):
        return None

    # We matched output.append(gate)
    return Eq(
        output1_v,
        App("concat", output_v, App("mk_single", gate_v)),
    )

def spec_remain_delete_zero(stmt, vars):
    """
    remain.delete(0)
      -> Eq(remain1_v, App("Tail", remain_v))
    """
    (input_v, output_v, remain_v, output1_v, remain1_v, gate_v, g_v, cM, cR) = vars
    # Must be an expression statement
    if not isinstance(stmt, ast.Expr):
        return None

    call = stmt.value
    if not isinstance(call, ast.Call):
        return None

    # Match remain.delete(...)
    func = call.func
    if not isinstance(func, ast.Attribute):
        return None
    if not (isinstance(func.value, ast.Name) and func.value.id == "remain"):
        return None
    if func.attr != "delete":
        return None

    # Must be delete(0)
    if len(call.args) != 1:
        return None

    arg = call.args[0]
    if not (isinstance(arg, ast.Constant) and arg.value == 0):
        return None

    return Eq(
        remain1_v,
        App("Tail", remain_v),
    )
    
def spec_nxt_next_gate(stmt, vars):
    """
    nxt = next_gate(remain, 0)
      -> ng_specification(gate_v, g_v, cM, cR, remain_v)
    """
    (input_v, output_v, remain_v, output1_v, remain1_v, gate_v, g_v, cM, cR) = vars
    if not isinstance(stmt, ast.Assign) or len(stmt.targets) != 1:
        return None

    target = stmt.targets[0]
    if not (isinstance(target, ast.Name) and target.id == "nxt"):
        return None

    value = stmt.value
    if not (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)
            and value.func.id == "next_gate"):
        return None

    if len(value.args) != 2:
        return None
    if not (isinstance(value.args[0], ast.Name) and value.args[0].id == "remain"):
        return None
    if not (isinstance(value.args[1], ast.Constant) and value.args[1].value == 0):
        return None

    # This line contributes ng_specification(...) to the body spec
    return ng_specification(gate_v, g_v, cM, cR, remain_v)

def spec_g_from_remain_nxt(stmt, vars):
    """
    g = remain.gates[nxt]
      -> Eq(g_v, g_v)  # crude: we already model g via ng_specification
    """
    (input_v, output_v, remain_v,
     output1_v, remain1_v, gate_v, g_v, cM, cR) = vars

    if not isinstance(stmt, ast.Assign):
        return None
    if len(stmt.targets) != 1:
        return None

    target = stmt.targets[0]
    if not (isinstance(target, ast.Name) and target.id == "g"):
        return None

    value = stmt.value
    if not isinstance(value, ast.Subscript):
        return None

    base = value.value
    if not (
        isinstance(base, ast.Attribute)
        and isinstance(base.value, ast.Name)
        and base.value.id == "remain"
        and base.attr == "gates"
    ):
        return None

    index_node = value.slice
    if not (isinstance(index_node, ast.Name) and index_node.id == "nxt"):
        return None

    # Crude spec: g_v already comes from ng_specification
    return Eq(g_v, g_v)

def spec_delete_pair(vars):
    (input_v, output_v, remain_v,
     output1_v, remain1_v, gate_v, g_v, cM, cR) = vars

    # remain1 = cM ; cR and output unchanged
    return And(
        Eq(remain1_v, App("concat", cM, cR)),
        Eq(output1_v, output_v),
    )


from VC import Eq, App, And  # your Expr classes

def spec_remain_delete_zero_alone(stmt, vars):
    """
    remain.delete(0) on its own
      -> Eq(remain1_v, App("Tail", remain_v))
    """
    (input_v, output_v, remain_v,
     output1_v, remain1_v, gate_v, g_v, cM, cR) = vars

    if not is_remain_delete_zero(stmt):
        return None

    # Optionally also assert output unchanged:
    return And(Eq(remain1_v, App("Tail", remain_v)),
               Eq(output1_v, output_v))

    # return Eq(remain1_v, App("Tail", remain_v))

def is_remain_delete_nxt(stmt):
    # match: remain.delete(nxt)
    if not isinstance(stmt, ast.Expr):
        return False
    call = stmt.value
    if not isinstance(call, ast.Call):
        return False

    func = call.func
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id == "remain"
            and func.attr == "delete"):
        return False

    if len(call.args) != 1:
        return False
    arg = call.args[0]
    return isinstance(arg, ast.Name) and arg.id == "nxt"

def is_remain_delete_zero(stmt):
    # match: remain.delete(0)
    if not isinstance(stmt, ast.Expr):
        return False
    call = stmt.value
    if not isinstance(call, ast.Call):
        return False

    func = call.func
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id == "remain"
            and func.attr == "delete"):
        return False

    if len(call.args) != 1:
        return False
    arg = call.args[0]
    return isinstance(arg, ast.Constant) and arg.value == 0
