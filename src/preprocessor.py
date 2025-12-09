import ast, inspect
import textwrap
from VC import *
from match_statments import *

def inv(output_var, remain_var, input_var):
    """
    Loop invariant I(output, remain):
        denote(concat(output, remain)) = denote(input)
    """
    return Eq(
        App("denote", App("concat", output_var, remain_var)),
        App("denote", input_var),
    )   

def get_run_ast(fn):
    src = inspect.getsource(fn)
    src = textwrap.dedent(src)
    tree = ast.parse(src)

    fn_def = next(
        n for n in ast.walk(tree)
        if isinstance(n, ast.FunctionDef) and n.name == "run"
    )

    return fn_def
    
def is_remain_nonzero_while(test: ast.expr) -> bool:
    # matches: remain.size() != 0
    if not isinstance(test, ast.Compare):
        return False
    if len(test.ops) != 1 or not isinstance(test.ops[0], ast.NotEq):
        return False
    if len(test.comparators) != 1:
        return False

    left = test.left
    comp = test.comparators[0]

    # left is: remain.size()
    if not (
        isinstance(left, ast.Call)
        and isinstance(left.func, ast.Attribute)
        and isinstance(left.func.value, ast.Name)
        and left.func.value.id == "remain"
        and left.func.attr == "size"
    ):
        return False

    # right is: 0
    if not (isinstance(comp, ast.Constant) and comp.value == 0):
        return False

    return True

def find_loop(fn_def: ast.FunctionDef) -> ast.While:
    for stmt in fn_def.body:
        if isinstance(stmt, ast.While) and is_remain_nonzero_while(stmt.test):
            return stmt
    raise ValueError("Did not find expected while remain.size() != 0 loop")

def enumerate_paths(stmts, path_conds):
    """
    Enumerate all (path_conds, body_stmts) pairs for a sequence of stmts.
    - path_conds: list of condition expressions (A, B, Not(B), ...)
    - body_stmts: list of statements in that concrete path
    """
    if not stmts:
        # End of block: one completed path with whatever body we've accumulated
        yield (path_conds, [])
        return

    first, rest = stmts[0], stmts[1:]

    if isinstance(first, ast.If):
        cond = translate_cond(first)

        # THEN branch: condition holds, then body + remaining stmts
        for conds2, body2 in enumerate_paths(first.body + rest, path_conds + [cond]):
            yield (conds2, body2)

        # ELSE branch: ¬cond holds, else body + remaining stmts
        orelse_stmts = first.orelse or []
        neg_cond = Not(cond)  # or mk_not(cond)
        for conds2, body2 in enumerate_paths(orelse_stmts + rest, path_conds + [neg_cond]):
            yield (conds2, body2)
    else:
        # Normal statement: keep it in the body for all paths
        for conds2, body2 in enumerate_paths(rest, path_conds):
            yield (conds2, [first] + body2)

def translate_cond(if_node: ast.If):
    test = if_node.test

    # 1) gate.name == "CX"
    if (
        isinstance(test, ast.Compare)
        and isinstance(test.left, ast.Attribute)
        and isinstance(test.left.value, ast.Name)
        and test.left.value.id == "gate"
        and test.left.attr == "name"
        and len(test.ops) == 1
        and isinstance(test.ops[0], ast.Eq)
        and len(test.comparators) == 1
        and isinstance(test.comparators[0], ast.Constant)
        and test.comparators[0].value == "CX"
    ):
        return App("is_CX", gate_v)

    # 2) g.name == "CX" and g.qubits == gate.qubits
    if (
        isinstance(test, ast.BoolOp)
        and isinstance(test.op, ast.And)
        and len(test.values) == 2
    ):
        left, right = test.values

        is_g_cx = (
            isinstance(left, ast.Compare)
            and isinstance(left.left, ast.Attribute)
            and isinstance(left.left.value, ast.Name)
            and left.left.value.id == "g"
            and left.left.attr == "name"
            and len(left.ops) == 1
            and isinstance(left.ops[0], ast.Eq)
            and len(left.comparators) == 1
            and isinstance(left.comparators[0], ast.Constant)
            and left.comparators[0].value == "CX"
        )

        same_qubits = (
            isinstance(right, ast.Compare)
            and isinstance(right.left, ast.Attribute)
            and isinstance(right.left.value, ast.Name)
            and right.left.value.id == "g"
            and right.left.attr == "qubits"
            and len(right.ops) == 1
            and isinstance(right.ops[0], ast.Eq)
            and len(right.comparators) == 1
            and isinstance(right.comparators[0], ast.Attribute)
            and isinstance(right.comparators[0].value, ast.Name)
            and right.comparators[0].value.id == "gate"
            and right.comparators[0].attr == "qubits"
        )

        if is_g_cx and same_qubits:
            return And(
                App("is_CX", g_v),
                App("same_qubits", gate_v, g_v),
            )

    raise ValueError(f"Unsupported if-condition shape: {ast.dump(test)}")

def get_body_spec(stmts, vars):
    """
    Given a list of ast.stmt, return a single Expr that specifies their effect,
    via one-to-one pattern mappings.
    """
    eqs = []
    i = 0

    while i < len(stmts):
        # --- special case: remain.delete(nxt); remain.delete(0) ---
        if (
            i + 1 < len(stmts)
            and is_remain_delete_nxt(stmts[i])
            and is_remain_delete_zero(stmts[i + 1])
        ):
            # use the block spec: remain1 = cM ; cR, output1 = output
            eqs.append(spec_delete_pair(vars))
            i += 2
            continue

        # --- otherwise: handle the current stmt per-line ---
        stmt = stmts[i]

        spec = (
            spec_gate_from_remain_gates(stmt, vars)
            or spec_g_from_remain_nxt(stmt, vars)
            or spec_nxt_next_gate(stmt, vars)
            or spec_remain_delete_zero_alone(stmt, vars)
            or spec_output_append_gate(stmt, vars)
            # add other per-line spec_* functions here
        )

        if spec is None:
            print(f"No spec mapping for statement: {ast.dump(stmt)}") # change to assert error

        eqs.append(spec)
        i += 1

    if not eqs:
        # empty body → treat as "true"
        return And()
    elif len(eqs) == 1:
        return eqs[0]
    else:
        return And(*eqs)


gate_v = Var("gate", "Gate")
g_v    = Var("g",    "Gate")

def build_branch_vcs_from_run(run_fn):
    fn_def = get_run_ast(run_fn)
    while_node = find_loop(fn_def)

    # logical vars (reuse your scheme)
    input_v  = Var("input",  "Circuit")
    output_v = Var("output", "Circuit")
    remain_v = Var("remain", "Circuit")
    
    output1_v = Var("output1", "Circuit")
    remain1_v = Var("remain1", "Circuit")
    
    cM = Var("cM", "Circuit")
    cR = Var("cR", "Circuit")
    
    vars = (input_v, output_v, remain_v, output1_v, remain1_v, gate_v, g_v, cM, cR)

    loop_inv = inv(output_v, remain_v, input_v)
    preservation = inv(output1_v, remain1_v, input_v)
    
    branches = list(enumerate_paths(while_node.body, []))

    vcs = []
    for idx, (path_conds, body_stmts) in enumerate(branches):
        vc = VC(
            name=f"branch_{idx}",
            assumptions=[
                loop_inv,
                *path_conds,
                get_body_spec(body_stmts, vars)
            ],
            goal=preservation,
        )

        vcs.append(vc)

    return vcs

def get_vcs(run_fn):
    vcs = []
    # ----------------------------------------------------------
    # Logical variables used in the specs
    # ----------------------------------------------------------
    input_v   = Var("input",   "Circuit")
    output_v  = Var("output",  "Circuit")
    remain_v  = Var("remain",  "Circuit")

    output1_v = Var("output1", "Circuit")
    remain1_v = Var("remain1", "Circuit")

    gate_v    = Var("gate",    "Gate")
    g_v       = Var("g",       "Gate")

    cM        = Var("cM",      "Circuit")
    cR        = Var("cR",      "Circuit")

    empty_v   = Var("empty",   "Circuit")   # denotes the empty circuit

    # handy tuple to pass into get_body_spec / spec_* helpers
    vars_tuple = (input_v, output_v, remain_v,
                  output1_v, remain1_v, gate_v, g_v, cM, cR)
    
        # loop invariant (over pre-state vars) and its preservation goal (post-state)
    loop_inv      = inv(output_v,  remain_v,  input_v)
    loop_preserve = inv(output1_v, remain1_v, input_v)
    
    # ----------------------------------------------------------
    # VC 0 – loop initialization
    # ----------------------------------------------------------
    vc_init = VC(
        name="loop_init",
        assumptions=[
            Eq(remain_v, input_v),   # remain = input at entry
            Eq(output_v, empty_v),   # output = []
        ],
        goal=loop_inv,              # invariant must hold initially
    )
    vcs.append(vc_init)
    
    # ----------------------------------------------------------
    # Branch VCs – each path through the while-body
    # ----------------------------------------------------------
    branch_vcs = build_branch_vcs_from_run(run_fn)
    for vc in branch_vcs:
        vcs.append(vc)
    # ----------------------------------------------------------
    # VC – loop exit
    # ----------------------------------------------------------
    vc_loop_exit = VC(
        name="loop_exit",
        assumptions=[
            Eq(remain_v, empty_v),                      # loop exit condition
            loop_inv,                                   # invariant still holds
        ],
        goal=Eq(App("denote", output_v), App("denote", input_v)),
    )
    vcs.append(vc_loop_exit)
    
    return vcs