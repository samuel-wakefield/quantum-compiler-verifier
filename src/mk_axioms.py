# axioms.py
from VC import Var, Eq, And, Implies, App, ForAll

def mk_axioms():
    axioms = []

    # --- 1. concat left identity: concat(empty, c) = c ----------------
    c = Var("c", "Circuit")
    empty_circ = Var("empty", "Circuit")  # empty circuit
    left_unit = ForAll(
        [c],
        Eq(
            App("concat", empty_circ, c),
            c,
        )
    )
    axioms.append(left_unit)

    # --- 2. concat right identity: concat(c, empty) = c ---------------
    right_unit = ForAll(
        [c],
        Eq(
            App("concat", c, empty_circ),
            c,
        )
    )
    axioms.append(right_unit)

    # --- 3. associativity of concat -----------------------------------
    c1 = Var("c1", "Circuit")
    c2 = Var("c2", "Circuit")
    c3 = Var("c3", "Circuit")
    assoc_concat = ForAll(
        [c1, c2, c3],
        Eq(
            App("concat", App("concat", c1, c2), c3),
            App("concat", c1, App("concat", c2, c3)),
        )
    )
    axioms.append(assoc_concat)

    # --- 4. semantics of concat: denote(c1 ; c2) = ucomp(denote(c2), denote(c1))
    denote_concat = ForAll(
        [c1, c2],
        Eq(
            App("denote", App("concat", c1, c2)),
            App("ucomp", App("denote", c2), App("denote", c1)),
        )
    )
    axioms.append(denote_concat)

    # --- 5. denote(empty) = Id ----------------------------------------
    U_id = App("Id")
    denote_empty = Eq(
        App("denote", empty_circ),
        U_id,
    )
    axioms.append(denote_empty)

    # --- 6. unitary identity laws: ucomp(Id, U) = U, ucomp(U, Id) = U -
    U = Var("U", "Unitary")

    id_left = ForAll(
        [U],
        Eq(
            App("ucomp", U, U_id),
            U,
        )
    )
    axioms.append(id_left)

    id_right = ForAll(
        [U],
        Eq(
            App("ucomp", U_id, U),
            U,
        )
    )
    axioms.append(id_right)

    # ==================================================================
    # CXCancellation-specific axioms
    # ==================================================================

    g1 = Var("g1", "Gate")
    g2 = Var("g2", "Gate")

    cx_cancel = ForAll(
        [g1, g2],
        Implies(
            And(
                App("is_CX", g1),
                App("is_CX", g2),
                App("same_qubits", g1, g2)
            ),
            Eq(
                App(
                "denote",
                    App(
                        "concat",
                        App("mk_single", g1),
                        App("mk_single", g2)
                    )
                ),
                U_id,
            )
        )
    )
    axioms.append(cx_cancel)
    
    # ==================================================================
    # Head and Tail axioms
    # ==================================================================

    head_tail_join = ForAll(
        [c1],
        Eq(
            App(
                "concat",
                App("mk_single", App("Head", c1)),
                App("Tail", c1),
            ),
            c1,
        ),
    )
    axioms.append(head_tail_join)
    g  = Var("g", "Gate")

    head_of_concat = ForAll(
        [g, c2],
        Eq(
            App("Head",
                App("concat",
                    App("mk_single", g),
                    c2,
                )
            ),
            g,
        ),
    )
    axioms.append(head_of_concat)
    tail_of_concat = ForAll(
        [g, c2],
        Eq(
            App("Tail",
                App("concat",
                    App("mk_single", g),
                    c2,
                )
            ),
            c2,
        ),
    )
    axioms.append(tail_of_concat)
    # Disjoint commutation
    disjoint_swap = ForAll(
        [g, c1],
        Implies(
            App("all_disjoint", g, c1),
            Eq(
                App("concat", App("mk_single", g), c1),
                App("concat", c1, App("mk_single", g)),
            )
        )
    )
    axioms.append(disjoint_swap)
    return axioms

