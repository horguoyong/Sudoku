import json
import time

import streamlit as st

from logic_ import conjuncts, is_prop_symbol
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails,
)


st.set_page_config(page_title="Sudoku Solver", layout="wide")


# ---------- Load puzzles ----------

@st.cache_data
def load_puzzles():
    with open("puzzles.json", encoding="utf-8") as file:
        data = json.load(file)

    puzzles = []
    for item in data["puzzles"]:
        givens = {
            tuple(map(int, key.split("_"))): value
            for key, value in item["givens"].items()
        }
        puzzles.append({"givens": givens})

    return data["n"], data["box_h"], data["box_w"], puzzles


# ---------- Display the board ----------

def display_board(n, box_h, box_w, givens, values):
    """Show givens in blue and inferred values in green."""
    html = ['<table style="border-collapse:collapse;margin:12px 0;">']

    for r in range(1, n + 1):
        html.append("<tr>")

        for c in range(1, n + 1):
            value = values.get((r, c), "")
            is_given = (r, c) in givens

            background = "#dbeafe" if is_given else "#ffffff"
            color = "#1e3a8a" if is_given else "#166534"

            top = 3 if (r - 1) % box_h == 0 else 1
            left = 3 if (c - 1) % box_w == 0 else 1
            bottom = 3 if r == n else 1
            right = 3 if c == n else 1

            html.append(
                f'<td style="width:38px;height:38px;text-align:center;'
                f'font-size:20px;font-weight:600;'
                f'background:{background};color:{color};'
                f'border-top:{top}px solid #475569;'
                f'border-left:{left}px solid #475569;'
                f'border-bottom:{bottom}px solid #475569;'
                f'border-right:{right}px solid #475569;">'
                f'{value}</td>'
            )

        html.append("</tr>")

    html.append("</table>")
    st.markdown("".join(html), unsafe_allow_html=True)
    st.caption("Blue cells are givens. Green numbers are inferred values.")


# ---------- Human-readable explanations ----------

def unpack_atom(symbol):
    name = str(symbol)
    prefix = "Not" if name.startswith("Not") else "Is"
    r, c, v = map(int, name[len(prefix):].split("_"))
    return prefix, r, c, v


def describe_atom(symbol):
    prefix, r, c, v = unpack_atom(symbol)

    if prefix == "Is":
        return f"Cell ({r}, {c}) contains {v}"

    return f"Cell ({r}, {c}) cannot contain {v}"


def explain_rule(conclusion, premises):
    prefix, r, c, v = unpack_atom(conclusion)

    if prefix == "Is":
        excluded = sorted(unpack_atom(p)[3] for p in premises)
        numbers = ", ".join(map(str, excluded))
        return (
            f"Values {numbers} have been eliminated from cell "
            f"({r}, {c}). Its only remaining candidate is {v}."
        )

    _, source_r, source_c, source_v = unpack_atom(premises[0])

    if (source_r, source_c) == (r, c):
        return (
            f"Cell ({r}, {c}) already contains {source_v}, "
            f"so it cannot also contain {v}."
        )

    if source_r == r:
        location = f"row {r}"
    elif source_c == c:
        location = f"column {c}"
    else:
        location = "the same box"

    return (
        f"Cell ({source_r}, {source_c}) contains {v} and shares "
        f"{location} with cell ({r}, {c}). Therefore, "
        f"cell ({r}, {c}) cannot contain {v}."
    )


# ---------- App-specific inference tracing ----------

def trace_forward_query(kb, query):
    """Record actual FC deductions and extract a proof of the query.

    This helper provides explanations. Full-grid solving still uses
    the imported solver functions, and the query verdict uses BC.
    """
    facts = {
        clause for clause in kb.clauses
        if is_prop_symbol(clause.op)
    }

    # Duplicate rules can arise from overlapping row/box constraints.
    rules = list(dict.fromkeys(
        clause for clause in kb.clauses
        if clause.op == "==>"
    ))

    remaining = {}
    dependents = {}

    for rule in rules:
        premises = tuple(dict.fromkeys(conjuncts(rule.args[0])))
        remaining[rule] = len(premises)

        for premise in premises:
            dependents.setdefault(premise, []).append(rule)

    known = set(facts)
    processed = set()
    agenda = list(facts)
    reasons = {}
    deductions = []

    while agenda:
        current = agenda.pop()

        if current == query:
            break

        if current in processed:
            continue
        processed.add(current)

        for rule in dependents.get(current, []):
            remaining[rule] -= 1

            if remaining[rule] == 0:
                conclusion = rule.args[1]

                if conclusion not in known:
                    premises = tuple(
                        dict.fromkeys(conjuncts(rule.args[0]))
                    )
                    known.add(conclusion)
                    reasons[conclusion] = premises
                    deductions.append((conclusion, premises))
                    agenda.append(conclusion)

    if query not in known:
        return False, [], []

    # Find only the deductions supporting this particular query.
    needed = set()
    pending = [query]

    while pending:
        current = pending.pop()
        if current in needed:
            continue

        needed.add(current)
        pending.extend(reasons.get(current, ()))

    supporting_facts = sorted(needed & facts, key=str)
    proof_steps = [
        (conclusion, premises)
        for conclusion, premises in deductions
        if conclusion in needed
    ]

    return True, supporting_facts, proof_steps


# ---------- Main interface ----------

st.title("Sudoku Solver")
st.write(
    "Solve a puzzle using logical inference, or check a particular "
    "cell and explore the reasoning."
)

try:
    n, box_h, box_w, puzzles = load_puzzles()
except (OSError, ValueError, KeyError) as error:
    st.error(f"Could not load puzzles.json: {error}")
    st.stop()

if not puzzles:
    st.error("No puzzles were found.")
    st.stop()

puzzle_index = st.selectbox(
    "Choose a puzzle",
    options=range(len(puzzles)),
    format_func=lambda i: (
        f"Puzzle {i + 1} — {len(puzzles[i]['givens'])} givens"
    ),
)

givens = puzzles[puzzle_index]["givens"]

# Clear results when switching to a different puzzle.
if st.session_state.get("active_puzzle") != puzzle_index:
    st.session_state["active_puzzle"] = puzzle_index
    st.session_state.pop("solve_result", None)
    st.session_state.pop("query_result", None)

board_column, controls_column = st.columns([1, 1])

with controls_column:
    st.subheader("Solve the full grid")

    algorithm = st.radio(
        "Choose an algorithm",
        ["Forward chaining", "Backward chaining"],
    )

    if st.button("Solve puzzle", type="primary"):
        st.session_state.pop("solve_result", None)

        with st.spinner(f"Solving with {algorithm.lower()}..."):
            try:
                solver = (
                    solve_full_grid_fc
                    if algorithm == "Forward chaining"
                    else solve_full_grid_bc
                )

                start = time.perf_counter()
                solved = solver(n, box_h, box_w, givens)
                elapsed = time.perf_counter() - start

                expected_cells = {
                    (r, c)
                    for r in range(1, n + 1)
                    for c in range(1, n + 1)
                }

                if set(solved) != expected_cells:
                    raise ValueError(
                        "The solver did not return a complete grid."
                    )

                if any(solved[cell] != v for cell, v in givens.items()):
                    raise ValueError("The result changed a given value.")

                digits = set(range(1, n + 1))
                units = []

                for r in range(1, n + 1):
                    units.append([solved[(r, c)]
                                  for c in range(1, n + 1)])

                for c in range(1, n + 1):
                    units.append([solved[(r, c)]
                                  for r in range(1, n + 1)])

                for br in range(1, n + 1, box_h):
                    for bc in range(1, n + 1, box_w):
                        units.append([
                            solved[(r, c)]
                            for r in range(br, br + box_h)
                            for c in range(bc, bc + box_w)
                        ])

                if any(set(unit) != digits for unit in units):
                    raise ValueError("The result violates Sudoku rules.")

                st.session_state["solve_result"] = {
                    "values": solved,
                    "elapsed": elapsed,
                    "algorithm": algorithm,
                }

            except Exception as error:
                st.error(f"Could not solve the puzzle: {error}")

    result = st.session_state.get("solve_result")
    if result:
        st.success(
            f"Solved with {result['algorithm'].lower()} "
            f"in {result['elapsed']:.3f} seconds."
        )

with board_column:
    st.subheader("Puzzle board")
    result = st.session_state.get("solve_result")
    values = result["values"] if result else givens
    display_board(n, box_h, box_w, givens, values)


# ---------- Targeted query ----------

st.divider()
st.subheader("Check a cell")

row_column, column_column, value_column = st.columns(3)

with row_column:
    row = int(st.number_input("Row", 1, n, 1))
with column_column:
    column = int(st.number_input("Column", 1, n, 1))
with value_column:
    value = int(st.number_input("Value", 1, n, 1))

show_trace = st.checkbox("Explain the reasoning", value=True)

if st.button("Check using backward chaining"):
    st.session_state.pop("query_result", None)

    with st.spinner("Checking the query..."):
        try:
            kb = build_definite_kb(n, box_h, box_w, givens)
            query = atom("Is", row, column, value)

            start = time.perf_counter()
            verdict = bool(pl_bc_entails(kb, query))
            elapsed = time.perf_counter() - start

            trace_result = None
            if show_trace:
                trace_result = trace_forward_query(kb, query)

            st.session_state["query_result"] = {
                "row": row,
                "column": column,
                "value": value,
                "verdict": verdict,
                "elapsed": elapsed,
                "trace": trace_result,
            }

        except Exception as error:
            st.error(f"Could not check the query: {error}")

result = st.session_state.get("query_result")

if result:
    st.write(
        f"**Last checked:** Does cell "
        f"({result['row']}, {result['column']}) "
        f"contain {result['value']}?"
    )
    st.write(f"**Backward-chaining verdict: {result['verdict']}**")
    st.caption(f"Query time: {result['elapsed']:.3f} seconds")

    if not result["verdict"]:
        st.info(
            "False means the value could not be proved from these "
            "rules. It does not necessarily mean its opposite "
            "was proved."
        )

    if result["trace"] is not None:
        found, facts, steps = result["trace"]
        st.subheader("Reasoning trace")
        st.caption(
            "The verdict above uses backward chaining. "
            "This explanation is generated by a separate "
            "forward-chaining run on the same knowledge base."
        )

        if found != result["verdict"]:
            st.warning(
                "Forward and backward chaining disagree. "
                "Check the backward-chaining implementation."
            )

        if found:
            with st.expander("Starting facts", expanded=True):
                for fact in facts:
                    st.write(f"• {describe_atom(fact)}.")

            if not steps:
                st.info("The queried value is already a known fact.")

            for number, (conclusion, premises) in enumerate(steps, 1):
                with st.expander(
                    f"Step {number}: {describe_atom(conclusion)}"
                ):
                    st.write(explain_rule(conclusion, premises))
        else:
            st.info(
                "Forward chaining exhausted its deductions without "
                "proving this query, so no successful proof is available."
            )