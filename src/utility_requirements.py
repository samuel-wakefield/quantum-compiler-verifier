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
    # # for all gates g1 in cM, g1 and gate_v are disjoint
    # g1 = Var("g1", "Gate")
    # c_pre = Var("c_pre", "Circuit")
    # c_post = Var("c_post", "Circuit")

    # all_disjoint_in_cM = ForAll( # THIS NEED SIMPLIFYING
    #     [g1, c_pre, c_post],
    #     Implies(
    #         Eq(
    #             cM,
    #             App(
    #                 "concat",
    #                 c_pre,
    #                 App(
    #                     "concat",
    #                     App("mk_single", g1),
    #                     c_post,
    #                 ),
    #             ),
    #         ),
    #         App("disjoint", gate_v, g1),
    #     ),
    # )
    all_disjoint_in_cM = App("all_disjoint", gate_v, cM)
    
    # gate_v and g_v share a qubit (i.e. are NOT disjoint)
    share_qubit = Not(App("disjoint", gate_v, g_v))
    
    return And(struct_eq, all_disjoint_in_cM, share_qubit)