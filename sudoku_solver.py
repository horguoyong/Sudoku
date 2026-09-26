"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

import sys
from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """

    kb = PropKB()
    
    # Each cell is assigned at least one value from 1 to n
    
    for r in range (1, n+1):
        for c in range (1, n+1):
            values = []
            for v in range (1, n+1):
                values.append(atom('Is', r, c, v))
            kb.tell(associate('|', values))
    
    # Each cell is assigned at most one value from 1 to n

    for r in range (1, n+1):
        for c in range (1, n+1):
            for v in range (1, n+1):
                for other_values in range (v+1, n+1):
                    rcv = atom('Is', r, c, v)
                    rcv_other = atom('Is', r, c, other_values)
                    kb.tell(~(rcv & rcv_other)) # Cell does NOT have 2 values
    
    # No two cells in the same row hold the same value.

    for r in range (1, n+1):
        for c in range (1, n+1):
            for c1 in range (c+1, n+1):
                for v in range (1, n+1):
                    rcv = atom('Is', r, c, v)
                    rc1v = atom('Is', r, c1, v)
                    kb.tell(~(rcv & rc1v)) # Cell value is NOT in row-column cell values
                            
    # No two cells in the same column hold the same value.

    for c in range (1, n+1):
        for r in range (1, n+1):
            for r1 in range (r+1, n+1):
                for v in range (1, n+1):
                    rcv = atom('Is', r, c, v)
                    r1cv = atom('Is', r1, c, v)
                    kb.tell(~(rcv & r1cv)) # Cell value is NOT in column-row cell values
    
    # No two cells in the same box hold the same value.

    for box_r in range (1, n+1, box_h):
        for box_c in range(1, n + 1, box_w): # Capture box row-column
            cells = []
            for r in range (box_r, box_r + box_h):
                for c in range (box_c, box_c + box_w): # Capture box row-column cell
                    cells.append((r, c)) # Store box cells into array
            for i in range (len(cells)):
                for j in range (i + 1, len(cells)): # Compare array item with other array items
                    r, c = cells[i]
                    r1, c1 = cells[j]
                    for v in range(1, n + 1):
                        cell1 = atom('Is', r, c, v)
                        cell2 = atom('Is', r1, c1, v)
                        kb.tell(~(cell1 & cell2)) # Cell value is NOT in box cell values
    
    # The givens cells hold their stated values.

    for (r,c),v in givens.items():
        given = atom('Is', r, c, v)
        kb.tell(given)

    return kb


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """
    
    kb = PropDefiniteKB()

    # Each cell is assigned at least one value from 1 to n
                    
    for r in range (1, n+1):
        for c in range (1, n+1):
            for v in range (1, n+1):
                conclusion = atom('Is', r, c, v)
                exclude = []
                for other_v in range (1, n+1):
                    if other_v != v:
                        exclude.append(atom('Not', r, c, other_v))
                if not exclude: # Array of other values is empty for 1x1 table
                    kb.tell(conclusion)
                else: # Cell value is true if all other cell values are not true
                    premise = associate('&', exclude)
                    kb.tell(Expr('==>', premise, conclusion))           
    
    # Each cell is assigned at most one value from 1 to n

    for r in range (1, n+1):
        for c in range (1, n+1):
            for v in range (1, n+1):
                premise = atom('Is', r, c, v)
                for other_v in range (1, n+1):
                    if other_v != v:
                        conclusion = atom('Not', r, c, other_v)
                        kb.tell(Expr('==>', premise, conclusion))
    
    # No two cells in the same row hold the same value.

    for r in range (1, n+1):
        for c in range (1, n+1):
            for other_c in range (1, n+1):
                if other_c != c:
                    for v in range (1, n+1):
                        premise = atom('Is', r, c, v)
                        conclusion = atom('Not', r, other_c, v)
                        kb.tell(Expr('==>', premise, conclusion))
                  
    # No two cells in the same column hold the same value.

    for c in range (1, n+1):
        for r in range (1, n+1):
            for other_r in range (1, n+1):
                if other_r != r:
                    for v in range (1, n+1):
                        premise = atom('Is', r, c, v)
                        conclusion = atom('Not', other_r, c, v)
                        kb.tell(Expr('==>', premise, conclusion))
    
    # No two cells in the same box hold the same value.
    for box_r in range(1, n + 1, box_h):
        for box_c in range(1, n + 1, box_w):
            cells = []
            for r in range(box_r, box_r + box_h):
                for c in range(box_c, box_c + box_w):
                    cells.append((r, c)) # Store box cells into an array
            for r1, c1 in cells:
                for r2, c2 in cells:
                    if (r1, c1) != (r2, c2):
                        for v in range(1, n + 1):
                            premise = atom('Is', r1, c1, v)
                            conclusion = atom('Not', r2, c2, v)
                            kb.tell(Expr('==>', premise, conclusion))
    
    # The givens cells hold their stated values.
    
    for (r,c),v in givens.items():
        cell = atom('Is',r,c,v)
        kb.tell(cell)

    return kb


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve using build_definite_kb and pl_fc_entails.

    Returns a dict {(row, col): value} for every cell.
    Assumes valid, consistent givens.
    """
    kb = build_definite_kb(n, box_h, box_w, givens)

    # Given cells are already solved; do not query them again.
    solution = dict(givens)

    row_used = [set() for _ in range(n)]
    column_used = [set() for _ in range(n)]
    box_used = [set() for _ in range(n)]

    boxes_per_row = n // box_w

    for (r, c), v in solution.items():
        # Boxes are numbered from 0, left to right, then top to bottom.
        # Box number = box row * boxes per row + box column.
        box = ((r - 1) // box_h) * boxes_per_row + (c - 1) // box_w

        row_used[r - 1].add(v)
        column_used[c - 1].add(v)
        box_used[box].add(v)

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in solution:
                continue

            box = ((r - 1) // box_h) * boxes_per_row + (c - 1) // box_w

            # Skip values already used in this row, column or box.
            taken = (
                row_used[r - 1]
                | column_used[c - 1]
                | box_used[box]
            )

            for v in range(1, n + 1):
                if v in taken:
                    continue

                q = atom('Is', r, c, v)
                truth = pl_fc_entails(kb, q)

                if truth:
                    solution[(r, c)] = v

                    # Save the inferred fact for later queries.
                    kb.tell(q)

                    row_used[r - 1].add(v)
                    column_used[c - 1].add(v)
                    box_used[box].add(v)
                    break

    return solution

def bc_index(kb):
    """Build and maintain an index used by the backward chaining algorithm.

    Backward chaining starts from a goal and asks:
        "Which rules have this goal as their conclusion?"

    For example, if the KB contains:

        A & B ==> C
        D ==> C

    the index stores:

        rules[C] = [[A, B], [D]]

    This allows pl_bc_entails() to immediately find the rules that could
    prove C, instead of scanning every clause in the KB each time.

    The function returns three data structures:

    facts
        A set containing propositions that are explicitly known to be true
        in the KB, such as the given Sudoku cells.

    rules
        A dictionary mapping each possible conclusion to the premises of
        rules that can derive it.

    proven
        A set containing propositions that backward chaining has already
        successfully derived. These results are kept so later queries can
        reuse previous work instead of proving the same propositions again.

    The index is stored inside the KB as '_bc_index'. This means repeated
    calls to pl_bc_entails() on the same KB can reuse the existing index.

    'seen' records how many KB clauses have already been indexed. If new
    facts are added to the KB while solving the Sudoku, only those new
    clauses need to be processed rather than rebuilding the whole index.

    Returns
    -------
    facts : set
        Propositions explicitly known to be true.

    rules : defaultdict(list)
        Maps a conclusion to the lists of premises that can derive it.

    proven : set
        Propositions previously derived successfully by backward chaining.
    """

    # Try to retrieve a backward-chaining index that was previously
    # created for this KB.
    #
    # The cached tuple contains:
    #
    #   seen   = number of KB clauses already processed by this index
    #   facts  = propositions explicitly known to be true
    #   rules  = conclusion -> possible premise lists
    #   proven = propositions previously derived by backward chaining
    #
    # If this is the first time bc_index() is called for this KB,
    # '_bc_index' does not exist. getattr() therefore returns the
    # default empty structures instead.
    seen, facts, rules, proven = getattr(
        kb,
        '_bc_index',
        (0, set(), defaultdict(list), set())
    )

    # Normally the KB only grows as new entailed facts are added.
    #
    # However, if the KB now contains fewer clauses than 'seen',
    # some clauses must have been removed since the index was built.
    #
    # In that situation, previously stored facts, rules and proofs may
    # depend on clauses that no longer exist. The cached information
    # therefore cannot safely be reused, so rebuild the index from scratch.
    if seen > len(kb.clauses):
        seen = 0
        facts = set()
        rules = defaultdict(list)
        proven = set()

    # Process only clauses that have NOT already been indexed.
    #
    # For example, if 20,000 clauses were previously indexed and two new
    # facts have since been added:
    #
    #     kb.clauses[seen:]
    #
    # contains only those two new clauses. This avoids repeatedly processing
    # the entire KB every time pl_bc_entails() is called.
    for c in kb.clauses[seen:]:

        # ------------------------------------------------------------
        # Case 1: The clause is a fact.
        #
        # A fact is a propositional symbol with no implication, e.g.:
        #
        #     Is2_1_2
        #
        # In Sudoku, the initial givens are examples of facts. New values
        # proved while solving the grid may also later be added as facts.
        #
        # Facts form the base case of backward chaining: if the current
        # goal is already in 'facts', no further proof is required.
        # ------------------------------------------------------------
        if is_prop_symbol(c.op):
            facts.add(c)

        # ------------------------------------------------------------
        # Case 2: The clause is a definite rule.
        #
        # Example:
        #
        #     A & B ==> C
        #
        # parse_definite_clause() separates this into:
        #
        #     premises   = [A, B]
        #     conclusion = C
        #
        # Backward chaining works from conclusion to premises, so the
        # rule is stored under C:
        #
        #     rules[C].append([A, B])
        #
        # Later, when prove(C) is called, rules[C] immediately gives
        # every possible rule that could establish C.
        # ------------------------------------------------------------
        elif c.op == '==>':
            premises, conclusion = parse_definite_clause(c)
            rules[conclusion].append(premises)

    # Store the updated index directly on the KB.
    #
    # len(kb.clauses) becomes the new value of 'seen', indicating that
    # every clause currently in the KB has now been indexed.
    #
    # 'proven' is stored together with the index so successful deductions
    # made by one backward-chaining query remain available to later queries.
    # This is particularly useful when solving all 81 Sudoku cells, because
    # later cell queries can reuse deductions made while solving earlier ones.
    kb._bc_index = (
        len(kb.clauses),
        facts,
        rules,
        proven
    )

    # Return the structures needed by pl_bc_entails().
    return facts, rules, proven


def pl_bc_entails(kb, query):
    """Backward chaining algorithm implemented for Part A2.c and described in Part B.3.

    The core logic of the backward chaining algorithm is based on the algorithm from the
    lecture notes (Propositional Logic Slide 98):
        1. Check whether the current goal is already a known fact.
        2. Find rules whose conclusion matches the current goal.
        3. For each matching rule, recursively prove every premise.
        4. If all premises of any matching rule can be proved, return True.
        5. Otherwise, return False.

    However, the implementation also includes several improvements:
    1. Indexing of the KB to allow for efficient retrieval of rules based on their conclusions
       (implemented in a separate function bc_index).
    2. Caching of proven goals to avoid redundant computations.
    3. Loop detection to prevent infinite recursion in case of circular dependencies.
    4. Prioritisation of rules whose premises contain more known facts or previously proven
       goals. These rules are more likely to succeed without requiring further recursion.

    Parameters
    ----------
    kb : PropDefiniteKB
        The knowledge base containing facts and definite-clause rules.
    query : Expr
        The proposition that we want to determine is True or False.

    Returns
    -------
    bool
        True if the query can be proved from the KB, otherwise False.
    """

    # Retrieve:
    #   facts  = propositions that are explicitly known to be True
    #   rules  = dictionary mapping each conclusion to rules that can prove it
    #   proven = propositions successfully proved by previous BC searches
    facts, rules, proven = bc_index(kb)

    # Sudoku reasoning can create long chains such as:
    #
    #     Is -> Not -> Is -> Not -> ...
    #
    # Increase Python's recursion limit so that a long valid proof chain
    # does not cause a RecursionError before the algorithm finishes.
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))

    # 'active' contains goals currently being investigated along the present
    # proof path.
    #
    # For example, if proving A requires B, proving B requires C, and proving
    # C requires A, then A will already be in 'active'. This tells us that
    # we have encountered a circular path and should stop following it.
    active = set()

    # 'failed' contains goals that have already failed during the CURRENT
    # pass through the search.
    #
    # This prevents us from repeatedly performing the same unsuccessful
    # search during one pass. It is cleared before the next pass because
    # additional propositions may have been proved in the meantime.
    failed = set()

    def prove(goal):
        """Try to prove one goal using backward chaining.

        Think of 'goal' as a question such as:

            "Can I prove Is1_1_1?"

        The function first checks whether we already know the answer is True.
        If not, it looks for rules that could produce the goal.

        For example, if the goal is C and the KB contains:

            A & B ==> C

        then proving C becomes the smaller problem of proving both A and B.

        If A or B is not already known, prove() calls itself recursively to
        determine whether that premise can also be derived from other rules.

        If there are several rules that conclude C, they represent alternative
        ways of proving C. Only one complete rule needs to succeed.
        """

        # ------------------------------------------------------------
        # Lecture Step 1:
        # Check whether the goal is already known to be True.
        #
        # 'facts' contains propositions explicitly supplied to the KB.
        # 'proven' contains propositions that backward chaining has
        # successfully derived earlier.
        #
        # In either case, there is no need to search any further.
        # ------------------------------------------------------------
        if goal in facts or goal in proven:
            return True

        # ------------------------------------------------------------
        # Loop detection and temporary failure caching.
        #
        # goal in active:
        #     We have encountered the same goal again while it is still
        #     being proved. Following it again would create a circular
        #     chain and potentially infinite recursion.
        #
        # goal in failed:
        #     We already tried and failed to prove this goal during the
        #     current pass, so there is no need to repeat the same work.
        # ------------------------------------------------------------
        if goal in active or goal in failed:
            return False

        # Mark the goal as currently being investigated.
        active.add(goal)

        # ------------------------------------------------------------
        # Lecture Step 2:
        # Find rules whose conclusion matches the current goal.
        #
        # bc_index() has already organised the KB into a dictionary, so:
        #
        #     rules.get(goal, ())
        #
        # directly retrieves the rules that could prove this goal.
        # ------------------------------------------------------------
        matching_rules = rules.get(goal, ())

        # ------------------------------------------------------------
        # Improvement 4: prioritise promising rules.
        #
        # A goal may have many different rules that can prove it.
        #
        # Example:
        #
        #     A ==> C
        #     B ==> C
        #     D ==> C
        #
        # If B is already a known fact, trying "B ==> C" first is much
        # cheaper than recursively investigating A or D.
        #
        # For each rule, count how many premises are NOT already known
        # through either 'facts' or 'proven'.
        #
        # Fewer unknown premises = lower score = tried earlier.
        #
        # This changes only the ORDER in which rules are explored.
        # It does not change which rules are available or the logical
        # requirements for proving the goal.
        # ------------------------------------------------------------
        matching_rules = sorted(
            matching_rules,
            key=lambda premises: sum(
                premise not in facts and premise not in proven
                for premise in premises
            )
        )

        # ------------------------------------------------------------
        # Lecture Steps 3 and 4:
        # Try each rule capable of producing the goal.
        #
        # Multiple rules are alternatives (OR):
        #
        #     A ==> C
        #     B ==> C
        #
        # Either rule is sufficient to prove C.
        # ------------------------------------------------------------
        for premises in matching_rules:

            # Within ONE rule, however, ALL premises must be True (AND).
            #
            # For example:
            #
            #     A & B & D ==> C
            #
            # requires A AND B AND D to all be proved.
            #
            # all() stops as soon as one premise returns False, so there
            # is no unnecessary work after a rule has already failed.
            if all(prove(p) for p in premises):

                # Every premise of this rule has been proved.
                # Therefore, by the rule, the current goal is also proved.
                #
                # Save it in 'proven' so that future searches can immediately
                # reuse this result instead of deriving it again.
                proven.add(goal)

                # We have finished investigating this goal, so remove it
                # from the current recursive path.
                active.discard(goal)

                return True

        # ------------------------------------------------------------
        # Lecture Step 5:
        # If we reach here, none of the available rules managed to prove
        # the current goal.
        # ------------------------------------------------------------

        # This goal is no longer being actively investigated.
        active.discard(goal)

        # Remember the failure for the remainder of this pass so that the
        # same unsuccessful search is not repeated unnecessarily.
        failed.add(goal)

        return False

    # ----------------------------------------------------------------
    # Repeat the backward-chaining search until a fixed point is reached.
    #
    # A goal can temporarily fail because part of its proof was blocked by
    # a circular dependency. During the same search, however, other goals
    # may successfully be proved and added to 'proven'.
    #
    # We therefore clear temporary failures and try again.
    # ----------------------------------------------------------------
    while True:

        # Record how many propositions had already been proved before
        # starting this pass.
        settled = len(proven)

        # Failures are temporary. A goal that failed previously may now
        # become provable because new propositions have been established.
        failed.clear()

        # Try to prove the original query.
        if prove(query):
            return True

        # If the entire pass finished without proving anything new, then
        # another pass would have exactly the same information available.
        #
        # We have therefore reached a fixed point and the query cannot
        # be proved from this KB.
        if len(proven) == settled:
            return False


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    output = {}

    for k, v in givens.items():
        output[k] = v

    for r in range(1, n+1):
        for c in range(1, n+1):
            # skip values already known
            if (r, c) in output:
                continue
            # same pruning as the forward chaining solver: a value held by a
            # peer cannot be entailed here, so asking would only walk the
            # whole rule graph to come back False
            taken = {output[p] for p in peers(r, c, n, box_h, box_w)
                     if p in output}
            for v in range(1, n+1):
                if v in taken:
                    continue
                if pl_bc_entails(kb, atom('Is', r, c, v)):
                    # asserting an entailed fact is sound, and it lets later
                    # queries stop at a fact instead of re-deriving the chain
                    kb.tell(atom('Is', r, c, v))
                    output[(r, c)] = v
                    break

    return output


# Adding modifications for FC to meet BC timing

def peers(r, c, n, box_h, box_w):
    """Return the cells sharing a row, column, or box with (r, c)."""
    cells = {(r, j) for j in range(1, n+1)} | {(i, c) for i in range(1, n+1)}
    box_r = (r - 1) // box_h * box_h + 1
    box_c = (c - 1) // box_w * box_w + 1
    cells |= {(box_r + dr, box_c + dc)
              for dr in range(box_h) for dc in range(box_w)}
    cells.discard((r, c))
    return cells


class RecordingDefiniteKB(PropDefiniteKB):
    """A PropDefiniteKB that remembers what pl_fc_entails derived.

    pl_fc_entails calls clauses_with_premise(p) exactly once for every symbol
    it newly infers, so overriding it lets us record each derived symbol --
    all of them entailed, so reusing them in later queries is sound. It also
    answers from a premise index instead of rescanning every clause, which is
    what made each forward pass quadratic in the KB size.
    """

    def __init__(self, sentence=None):
        self.derived = set()
        self._index = defaultdict(list)
        super().__init__(sentence)

    def tell(self, sentence):
        super().tell(sentence)
        if sentence.op == '==>':
            # one entry per clause, even if a premise repeats, to match the
            # list the unindexed version would return
            for p in set(conjuncts(sentence.args[0])):
                self._index[p].append(sentence)

    def clauses_with_premise(self, p):
        self.derived.add(p)
        return self._index.get(p, [])


def build_recording_kb(n, box_h, box_w, givens):
    """Same clauses as build_definite_kb, held in a RecordingDefiniteKB.

    Returns
    -------
    RecordingDefiniteKB
    """
    kb = RecordingDefiniteKB()
    for clause in build_definite_kb(n, box_h, box_w, givens).clauses:
        kb.tell(clause)
    return kb


def justifications(kb):
    """Return kb's record of how each derived symbol was first derived.

    Both pl_fc_entails_cached and pl_bc_entails write to it whenever a rule
    fires, as {conclusion: premises of the rule that derived it}. Only
    derived symbols appear -- facts told to the KB never do -- and entries
    are kept in the order they were derived, so the premises of every entry
    come before it (or are facts). That is what lets a solve be replayed step
    by step, and a single proof be traced back to the facts.

    It is kept on the KB and carries over between calls, like the rest of
    each algorithm's saved state, and is dropped if clauses are retracted,
    since a derivation may then no longer hold.

    Parameters
    ----------
    kb : PropDefiniteKB

    Returns
    -------
    dict[Expr, list[Expr]]
    """
    seen, why = getattr(kb, '_why', (0, {}))
    if seen > len(kb.clauses):
        why = {}
    kb._why = (len(kb.clauses), why)
    return why


def pl_fc_entails_cached(kb, q):
    """pl_fc_entails that keeps its work between calls on the same KB.

    The library version rebuilds its counters from scratch on every call,
    scans every clause for each symbol it infers, and throws away everything
    it derived once it returns. A definite KB only ever grows, so none of that
    work goes stale: this version stores the counters, a premise -> rule
    index, the inferred set and the unfinished agenda on the KB, and each call
    resumes where the last one stopped. Clauses told since the last call are
    folded in first.

    Parameters
    ----------
    kb : PropDefiniteKB
    q : Expr

    Returns
    -------
    bool
    """
    why = justifications(kb)
    seen, count, uses, inferred, agenda, facts = getattr(
        kb, '_fc_state', (0, [], defaultdict(list), set(), [], set()))
    if seen > len(kb.clauses):
        # clauses were retracted; anything inferred may no longer hold
        seen, count, uses, inferred, agenda, facts = (
            0, [], defaultdict(list), set(), [], set())

    for c in kb.clauses[seen:]:
        if is_prop_symbol(c.op):
            facts.add(c)
            agenda.append(c)
            continue
        # counters are per rule position, not keyed by the clause itself, so
        # duplicate clauses each get their own counter
        i = len(count)
        premises, conclusion = parse_definite_clause(c)
        waiting = set(premises) - inferred
        count.append((len(waiting), conclusion, premises))
        for p in waiting:
            uses[p].append(i)
        if not waiting:
            # every premise was already inferred before this rule arrived
            agenda.append(conclusion)
            if conclusion not in facts:
                why.setdefault(conclusion, premises)

    kb._fc_state = (len(kb.clauses), count, uses, inferred, agenda, facts)

    while q not in inferred and agenda:
        p = agenda.pop()
        if p in inferred:
            continue
        inferred.add(p)
        # p is fully propagated before we stop, so the saved state is always
        # consistent for the next call to resume from
        for i in uses.pop(p, ()):
            remaining, conclusion, premises = count[i]
            count[i] = (remaining - 1, conclusion, premises)
            if remaining == 1:
                agenda.append(conclusion)
                # the first rule to fire is the derivation kept; a fact
                # needs none, even if a rule also concludes it
                if conclusion not in facts:
                    why.setdefault(conclusion, premises)

    return q in inferred


def solve_full_grid_fc_recording(n, box_h, box_w, givens):
    """solve_full_grid_fc, backed by build_recording_kb.

    Same per-cell strategy, but a value some earlier pl_fc_entails call
    already derived is taken from kb.derived instead of asking again: one
    forward pass solves most of the grid on its way to the first query.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_recording_kb(n, box_h, box_w, givens)
    output = dict(givens)

    for r in range(1, n+1):
        for c in range(1, n+1):
            if (r, c) in output:
                continue
            taken = {output[p] for p in peers(r, c, n, box_h, box_w)
                     if p in output}
            for v in range(1, n+1):
                if v in taken:
                    continue
                query = atom('Is', r, c, v)
                if query in kb.derived or pl_fc_entails(kb, query):
                    kb.tell(query)
                    output[(r, c)] = v
                    break

    return output


def solve_full_grid_fc_cached(n, box_h, box_w, givens, kb=None):
    """solve_full_grid_fc, backed by pl_fc_entails_cached.

    Same per-cell strategy and the same KB; the only change is that forward
    chaining keeps what it derived between queries, so the whole grid costs
    about one forward pass instead of one per query.

    Parameters
    ----------
    kb : PropDefiniteKB, optional -- a KB from build_definite_kb for these
        givens, to solve on instead of building one; pass it to read the
        reasoning back afterwards with justifications(kb)

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    if kb is None:
        kb = build_definite_kb(n, box_h, box_w, givens)
    output = dict(givens)

    for r in range(1, n+1):
        for c in range(1, n+1):
            if (r, c) in output:
                continue
            taken = {output[p] for p in peers(r, c, n, box_h, box_w)
                     if p in output}
            for v in range(1, n+1):
                if v in taken:
                    continue
                if pl_fc_entails_cached(kb, atom('Is', r, c, v)):
                    output[(r, c)] = v
                    break

    return output

# Adding for app reasoning trace

def proof_steps(kb, query):
    """Return the rule firings that derived query, in the order they apply.

    Call after pl_bc_entails or pl_fc_entails_cached has returned True for
    query on the same KB. Only the firings the proof of query depends on are
    returned, not everything the algorithm derived on the way. Every entry in
    justifications(kb) was derived after its premises, so following them back
    from query always ends at facts and never loops.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    list[(list[Expr], Expr)] -- (premises, conclusion) pairs, premises
        proven before the conclusion that uses them; empty if query is a
        fact or has not been proven
    """
    why = justifications(kb)
    steps, done = [], set()

    def walk(goal):
        # facts have no entry, so the walk stops at them
        if goal in done or goal not in why:
            return
        done.add(goal)
        for p in why[goal]:
            walk(p)
        steps.append((why[goal], goal))

    walk(query)
    return steps


def bc_unproven_premises(kb, query):
    """For each rule concluding query, return its premises that the KB does
    not entail -- what is missing for query to be proven.

    pl_bc_entails stops at the first premise that fails, so the rest are
    asked about one by one here rather than read off its search.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    list[list[Expr]] -- one list per rule concluding query
    """
    _, rules, _ = bc_index(kb)
    return [[p for p in premises if not pl_bc_entails(kb, p)]
            for premises in rules.get(query, ())]

