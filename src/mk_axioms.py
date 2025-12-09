# axioms.py
from VC import Var, Eq, And, Implies, App, ForAll

def mk_axioms():
    axioms = []

    # Sort names you use in ctx:
    #   "Circuit", "Unitary", "Gate", "Qubit", "Int", "Bool"

    # We'll rely on the following function symbols in ctx:
    #   concat  : Circuit × Circuit → Circuit
    #   empty   : Circuit                 (0-ary func, constant)
    #   denote  : Circuit → Unitary
    #   ucomp   : Unitary × Unitary → Unitary    (unitary composition)
    #   Id      : Unitary                         (identity on all qubits)
    #
    # For CX-related rules:
    #   mk_single : Gate → Circuit                (one-gate circuit)
    #   denote_gate : Gate → Unitary
    #   CX       : Qubit × Qubit → Gate
    #   disjoint : Gate × Gate → Bool             (no shared qubits)
    #
    # You don’t have to implement them immediately in ctx, but
    # these are the names the axioms will refer to.

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
    # (You can choose order convention; this matches "right-to-left" eval.)
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

    # --- 7. denote of a single-gate circuit ---------------------------
    # denote(mk_single(g)) = denote_gate(g)
    denote_single = ForAll(
        [g1],
        Eq(
            App("denote", App("mk_single", g1)),
            App("denote_gate", g1)
        )
    )
    axioms.append(denote_single)

    # --- 8. commutation of disjoint gates -----------------------------
    # If disjoint(g1,g2) then
    #   denote(mk_single(g1) ; mk_single(g2)) =
    #   denote(mk_single(g2) ; mk_single(g1))
    commute_disjoint = ForAll(
        [g1, g2],
        Implies(
            App("disjoint", g1, g2),   # Bool predicate
            Eq(
                App("denote",
                    App("concat",
                        App("mk_single", g1),
                        App("mk_single", g2),
                    )
                ),
                App("denote",
                    App("concat",
                        App("mk_single", g2),
                        App("mk_single", g1),
                    )
                ),
            )
        )
    )
    axioms.append(commute_disjoint)

    # --- 9. CX gate + its cancellation -------------------------------
    q1 = Var("q1", "Qubit")
    q2 = Var("q2", "Qubit")

    cx_gate1 = App("CX", q1, q2)   # Gate
    cx_gate2 = App("CX", q1, q2)   # same gate

    # 9a. denote_gate(CX(q1,q2)) is some unitary CXU(q1,q2)
    #     (you can keep this as an uninterpreted function, it just
    #      makes it explicit that CX is a gate whose denotation is
    #      the same unitary whenever we re-use the same qubits.)
    cx_unitary = App("CXU", q1, q2)  # Unitary
    cx_denotation = ForAll(
        [q1, q2],
        Eq(
            App("denote_gate", App("CX", q1, q2)),
            cx_unitary,
        )
    )
    axioms.append(cx_denotation)

    # 9b. CX cancellation: CX(q1,q2); CX(q1,q2) = Id  (as a circuit)
    #    We say: denote(mk_single(CX); mk_single(CX)) = Id
    # cx_cancel = ForAll(
    #     [q1, q2],
    #     Eq(
    #         App(
    #             "denote",
    #             App(
    #                 "concat",
    #                 App("mk_single", App("CX", q1, q2)),
    #                 App("mk_single", App("CX", q1, q2)),
    #             )
    #         ),
    #         U_id,
    #     )
    # )
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

