import json
import re
import time
import streamlit as st
from utils import *
from logic_ import *
from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_fc_cached,
    solve_full_grid_bc,
    pl_bc_entails,
    justifications,
    proof_steps,
    bc_unproven_premises,
)

st.title('Sudoku Solver')

with open('puzzles.json') as f:
    pool = json.load(f)

# --- 1. Puzzle selection & visual board display ---
n, box_h, box_w = pool['n'], pool['box_h'], pool['box_w']

st.sidebar.header('Settings')
option = st.sidebar.selectbox(
    "Puzzle selection",
    (i for i in range(1, len(pool['puzzles']) + 1))
)

# givens keyed as (row, col), 1-indexed, to match the solver's expected input
givens = {
    tuple(int(x) for x in k.split('_')): v
    for k, v in pool['puzzles'][option - 1]['givens'].items()
}

# cell backgrounds for highlighting; translucent so they suit either theme
NEW_BG = 'rgba(255, 190, 0, 0.45)'
CAUSE_BG = 'rgba(31, 119, 180, 0.22)'


def render_grid(values, givens, target=st, new=None, causes=()):
    """Render an n x n grid as an HTML table with thick box borders.

    values : dict[(int, int), int] -- cells to display
    givens : dict[(int, int), int] -- cells to show in bold
    target : where to draw it; pass an st.empty() to replace what's there
    new    : (int, int) -- a cell to highlight as just deduced
    causes : cells to highlight as the reasons for that deduction
    """
    rows = []
    for r in range(1, n + 1):
        cells = []
        for c in range(1, n + 1):
            style = [
                'width:2.2em', 'height:2.2em', 'text-align:center',
                'font-size:1.2em', 'border:1px solid #999',
            ]
            if r % box_h == 1 or box_h == 1:
                style.append('border-top:3px solid currentColor')
            if r == n:
                style.append('border-bottom:3px solid currentColor')
            if c % box_w == 1 or box_w == 1:
                style.append('border-left:3px solid currentColor')
            if c == n:
                style.append('border-right:3px solid currentColor')
            if (r, c) == new:
                style.append(f'background:{NEW_BG}')
            elif (r, c) in causes:
                style.append(f'background:{CAUSE_BG}')

            v = values.get((r, c), '')
            if (r, c) in givens:
                text = f'<b>{v}</b>'
            else:
                text = f'<span style="color:#1f77b4">{v}</span>'
            cells.append(f'<td style="{";".join(style)}">{text}</td>')
        rows.append(f'<tr>{"".join(cells)}</tr>')
    target.markdown(
        f'<table style="border-collapse:collapse">{"".join(rows)}</table>',
        unsafe_allow_html=True,
    )


# --- Reasoning trace helpers ---
# The solver records how each symbol was derived (justifications / proof_steps
# in sudoku_solver.py). These only turn that record into plain data for the
# interface; no inference happens here.

def parse(symbol):
    """Split a symbol like Is3_2_4 into ('Is', 3, 2, 4)."""
    kind, r, c, v = re.fullmatch(r'(Is|Not)(\d+)_(\d+)_(\d+)',
                                 str(symbol)).groups()
    return kind, int(r), int(c), int(v)


def constraint(a, b):
    """Name the constraint two cells share, as it would be read aloud."""
    if a == b:
        return 'this cell'
    if a[0] == b[0]:
        return f'row {a[0]}'
    if a[1] == b[1]:
        return f'column {a[1]}'
    return 'this box'


def deductions(why):
    """Turn a solver's derivation record into one step per cell value placed.

    why : {conclusion: premises}, in the order they were derived -- from
        justifications(kb), or built from proof_steps(kb, query)

    Returns a list of dicts, one per derived Is symbol, in derivation order:
        cell, value  -- what was placed
        symbol       -- the Is symbol, e.g. 'Is1_2_4'
        reasons      -- one per value ruled out: (value, Not symbol,
                        cause cell, constraint name, source), where source
                        is 'given' or the step number that placed the cause
    """
    steps, step_of = [], {}
    for concl, premises in why.items():
        kind, r, c, v = parse(concl)
        if kind != 'Is':
            continue
        reasons = []
        for p in sorted(premises, key=lambda p: parse(p)[3]):
            l = parse(p)[3]
            # a Not is derived by one elimination rule, whose single premise
            # is the Is that ruled the value out
            cause = why.get(p, [None])[0]
            if cause is None:
                reasons.append((l, str(p), None, None, None))
                continue
            _, pr, pc, _ = parse(cause)
            source = step_of.get((pr, pc), 'given')
            reasons.append((l, str(p), (pr, pc),
                            constraint((r, c), (pr, pc)), source))
        steps.append({'cell': (r, c), 'value': v, 'symbol': str(concl),
                      'reasons': reasons})
        step_of[(r, c)] = len(steps)
    return steps


def explain(step):
    """Write out one deduction as a rule-firing chain in plain English."""
    (r, c), v = step['cell'], step['value']
    lines = []
    for l, not_sym, cause, name, source in step['reasons']:
        if cause is None:
            lines.append(f'- Inferred `{not_sym}`: **{l}** is ruled out')
            continue
        where = 'given' if source == 'given' else f'placed in step {source}'
        lines.append(
            f'- Inferred `{not_sym}`: **{l}** is ruled out because {name} '
            f'already contains {l} at ({cause[0]}, {cause[1]}) ({where})'
        )
    st.markdown('\n'.join(lines))
    st.markdown(f'⟹ Deduce `{step["symbol"]}`: every other value is ruled '
                f'out, so **{v}** is the last remaining candidate for '
                f'({r}, {c}).')


def step_title(i, step):
    (r, c), v = step['cell'], step['value']
    return f'Step {i}: cell ({r}, {c}) = {v}'


st.header(f'Puzzle {option}')
# one board: shows the givens now, redrawn with the solution once solved
board = st.empty()
render_grid(givens, givens, board)

# --- 2. Full-grid auto-solver, with algorithm selection ---
# label -> solver; every solver takes (n, box_h, box_w, givens)
solvers = {
    'Forward chaining': solve_full_grid_fc,
    'Forward chaining (cached)': solve_full_grid_fc_cached,
    'Backward chaining': solve_full_grid_bc,
}
# shown under each option in the radio
notes = {
    'Forward chaining': 'Disabled: unoptimised, takes about 10 min in testing',
    'Forward chaining (cached)': 'Keeps what it derived between cell queries',
    'Backward chaining': 'Goal-directed: proves each cell from the query back',
}
# listed so the implementation is visible, but too slow to run on the shared
# server: one abandoned solve keeps a thread busy for every viewer
disabled = {'Forward chaining'}
# these also take a KB to solve on, so its derivations can be read back
traced = {'Forward chaining (cached)', 'Backward chaining'}
algorithm = st.sidebar.radio(
    'Algorithm', list(solvers), captions=[notes[k] for k in solvers], index=1
)

if algorithm in disabled:
    st.info(
        'The unoptimised forward chaining solver is disabled here. Each cell '
        'query re-runs forward chaining from scratch and discards what it '
        'derived, so a full solve took about 10 minutes in testing. The '
        'cached version keeps its work between queries.'
    )
if st.button('Solve', disabled=algorithm in disabled):
    with st.spinner(f'Solving with {algorithm.lower()}...', show_time=True):
        start = time.perf_counter()
        if algorithm in traced:
            kb = build_definite_kb(n, box_h, box_w, givens)
            solution = solvers[algorithm](n, box_h, box_w, givens, kb=kb)
            steps = deductions(justifications(kb))
        else:
            solution = solvers[algorithm](n, box_h, box_w, givens)
            steps = None
        elapsed = time.perf_counter() - start
    # kept across reruns so using the query below doesn't clear the result
    st.session_state['solved'] = (option, algorithm, solution, elapsed, steps)

# only show a result that matches the current puzzle and algorithm
solved = st.session_state.get('solved')
if not (solved and solved[:2] == (option, algorithm)):
    solved = None
if solved:
    solution, elapsed = solved[2:4]
    render_grid(solution, givens, board)
    st.caption('**Bold**: given, blue: solved')
    st.write(f'Solved in {elapsed:.3f} s')

# --- 3. Targeted cell entailment query ---
st.header('Cell entailment query')
st.write('Ask whether the puzzle entails that a cell holds a value, using '
         'backward chaining on the definite KB. Should take <1s.')
col_r, col_c, col_v = st.columns(3)
r = col_r.number_input('Row', min_value=1, max_value=n, step=1)
c = col_c.number_input('Column', min_value=1, max_value=n, step=1)
v = col_v.number_input('Value', min_value=1, max_value=n, step=1)

if st.button('Check'):
    with st.spinner(f'Checking Is({r}, {c}, {v})...', show_time=True):
        start = time.perf_counter()
        kb = build_definite_kb(n, box_h, box_w, givens)
        goal = atom('Is', r, c, v)
        entailed = pl_bc_entails(kb, goal)
        elapsed = time.perf_counter() - start
        # read off the same KB, which still holds what the query derived
        if entailed:
            trace = deductions(dict(
                (concl, premises) for premises, concl in proof_steps(kb, goal)
            ))
        else:
            trace = sorted(parse(p)[3]
                           for p in bc_unproven_premises(kb, goal)[0])
    # kept across reruns, like the solved grid
    st.session_state['query'] = (option, r, c, v, entailed, elapsed, trace)

# only show a result for the current puzzle and inputs
query = st.session_state.get('query')
if not (query and query[:4] == (option, r, c, v)):
    query = None
if query:
    entailed, elapsed, trace = query[4:]
    message = f'KB ⊨ Is({r}, {c}, {v}): **{entailed}**'
    if entailed:
        st.success(message)
    else:
        st.error(message)
    st.write(f'Checked in {elapsed:.3f} s')

    # the reasoning behind this answer, right under it
    st.subheader('Why?')
    if (r, c) in givens:
        if givens[(r, c)] == v:
            st.write(f'({r}, {c}) = {v} is a given: it is a fact in the KB, '
                     'so no rule needs to fire.')
        else:
            st.write(f'({r}, {c}) is given as {givens[(r, c)]}, which rules '
                     f'out {v} for that cell.')
    elif entailed:
        st.write(
            f'Backward chaining worked back from `Is{r}_{c}_{v}` to the '
            f'givens. The proof needs {len(trace)} cell value(s), each '
            'deduced as a last remaining candidate. The last step is the '
            'query.'
        )
        for i, step in enumerate(trace, 1):
            with st.expander(step_title(i, step), expanded=i == len(trace)):
                explain(step)
    else:
        st.write(
            f'The only rule that concludes `Is{r}_{c}_{v}` needs every other '
            f'value ruled out for ({r}, {c}). Backward chaining could not '
            f'rule out {", ".join(map(str, trace))}, so the rule never fires '
            'and the query is not entailed.'
        )

# --- 4. Reasoning trace ("tutor mode") ---
st.header('Reasoning trace')
st.caption('How the full-grid solve above reached its answer, step by '
           'step. The proof behind a cell query is shown under its result.')
if not solved:
    st.write('Solve the puzzle above to replay how it was deduced.')
elif solved[4] is None:
    st.write(f'{algorithm} does not record its reasoning.')
else:
    steps = solved[4]
    st.write(
        f'{algorithm} placed {len(steps)} values, each as the last '
        'remaining candidate once every other value was ruled out by a '
        'row, column or box. Use the buttons or slider to step through '
        'them, in the order they were deduced.'
    )
    st.caption(
        f'<span style="background:{NEW_BG};padding:0 .4em">Yellow</span>'
        ': the cell deduced at this step. '
        f'<span style="background:{CAUSE_BG};padding:0 .4em">Blue</span>'
        ': cells that ruled out its other values.',
        unsafe_allow_html=True,
    )
    # reset the replay to the end whenever a new solve comes in
    replay_id = (option, algorithm, id(steps))
    if st.session_state.get('replay_id') != replay_id:
        st.session_state['replay_id'] = replay_id
        st.session_state['replay_step'] = len(steps)
        st.session_state['playing'] = False

    # Playing advances the slider one step per rerun: a widget's value
    # can only be set before it is drawn, so each frame is a full rerun
    # and the slider, board and step card all move together.
    if st.session_state.pop('replay_advance', False):
        st.session_state['replay_step'] += 1


    def toggle_play():
        playing = not st.session_state['playing']
        if playing and st.session_state['replay_step'] == len(steps):
            # nothing left to play from the end, so start over
            st.session_state['replay_step'] = 0
        st.session_state['playing'] = playing


    def stop_play():
        st.session_state['playing'] = False


    def jump(to):
        """Move to a step, clamped to the replay; stops playback."""
        st.session_state['replay_step'] = max(0, min(len(steps), to))
        st.session_state['playing'] = False


    playing = st.session_state['playing']
    current = st.session_state['replay_step']
    at_start, at_end = current == 0, current == len(steps)
    first, prev, play, nxt, last = st.columns(5)
    first.button('⏮ First', on_click=jump, args=(0,), disabled=at_start,
                 width='stretch')
    prev.button('◀ Prev', on_click=jump, args=(current - 1,),
                disabled=at_start, width='stretch')
    play.button('⏸ Pause' if playing else '▶ Play', on_click=toggle_play,
                width='stretch')
    nxt.button('Next ▶', on_click=jump, args=(current + 1,),
               disabled=at_end, width='stretch')
    last.button('Last ⏭', on_click=jump, args=(len(steps),),
                disabled=at_end, width='stretch')
    # dragging the slider takes over from playback
    k = st.slider('Step', 0, len(steps), key='replay_step',
                  on_change=stop_play)

    values = dict(givens)
    for s in steps[:k]:
        values[s['cell']] = s['value']
    if k == 0:
        render_grid(values, givens)
    else:
        causes = {reason[2] for reason in steps[k - 1]['reasons']}
        render_grid(values, givens, new=steps[k - 1]['cell'],
                    causes=causes)

    if k == 0:
        st.write('Step 0: only the givens are known.')
    else:
        with st.container(border=True):
            st.markdown(f'**{step_title(k, steps[k - 1])}**')
            explain(steps[k - 1])

    # a toggle rather than an expander, since expanders can't nest and
    # each step is already one
    if st.toggle(f'Show all {len(steps)} steps', key='show_all_steps'):
        for i, step in enumerate(steps, 1):
            with st.expander(step_title(i, step)):
                explain(step)

    # the next frame is queued at the end of the script, once everything
    # else on the page has been drawn
    if playing:
        replay_done = k == len(steps)

# --- Replay playback: advance one frame per rerun ---
if st.session_state.get('playing') and 'replay_done' in globals():
    if replay_done:
        st.session_state['playing'] = False
    else:
        # clicking Pause during the wait interrupts this run, so the next
        # frame is never queued
        time.sleep(0.4)
        st.session_state['replay_advance'] = True
    st.rerun()
