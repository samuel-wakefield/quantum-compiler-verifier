from VC import *
def ng_specification(gate_v, g_v, cM, cR, remain_v):
    # remain_v = cL;gate_v;cM;g_v;cR
    struct_eq = Eq(
        remain_v,
        App(
            "concat",
            App("mk_single", gate_v),
            App(
                "concat",
                cM,
                App(
                    "concat",
                    App("mk_single", g_v),
                    cR
                )
            )
        )
    )

    all_disjoint_in_cM = App("all_disjoint", gate_v, cM)
    
    # gate_v and g_v share a qubit (i.e. are NOT disjoint)
    share_qubit = Not(App("disjoint", gate_v, g_v))
    
    return And(struct_eq, all_disjoint_in_cM, share_qubit)