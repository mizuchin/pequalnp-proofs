#!/usr/bin/env python3
"""Monotone circuit synthesis for mask functions (milestone 5, upper half).

Given n, m and a mask M (bit (m*u+v) of M is the target value on the unit
row (u, v)), find a small AND/OR circuit over the n+m unit-indicator input
wires that computes M on the unit rows. Each wire's behaviour on unit rows
is an (n*m)-bit mask. Search: level-by-level over masks, where each mask
keeps one witness DAG (gates shared between subcircuits count once);
combining two masks costs |union of their DAGs| + 1. Emits the Lean `up`
theorem in the shape the merged L_meta_5531 uses.

Usage: gensynth.py n m M [max_gates]
"""
import sys

def synth(n, m, M, max_gates=10):
    rows = n * m
    full = (1 << rows) - 1
    target = M & full
    # node: ('in', wire) or (op, nodeA, nodeB) with nodeA <= nodeB (and/or commute)
    dag = {}   # mask -> node
    size = {}  # mask -> number of gates in its DAG
    def add(mask, node, sz):
        if mask not in size or sz < size[mask]:
            dag[mask] = node; size[mask] = sz; return True
        return False
    for i in range(n + m):
        if i < n:
            mask = sum(1 << (m * u + v) for u in range(n) for v in range(m) if u == i)
        else:
            mask = sum(1 << (m * u + v) for u in range(n) for v in range(m) if v == i - n)
        add(mask, ('in', i), 0)
    if target in dag:
        return dag[target], 0
    nodes_of = {}
    def gate_set(node):
        if node not in nodes_of:
            if node[0] == 'in': nodes_of[node] = frozenset()
            else: nodes_of[node] = gate_set(node[1]) | gate_set(node[2]) | {node}
        return nodes_of[node]
    frontier = list(dag.keys())
    all_masks = list(dag.keys())
    while frontier:
        new_frontier = []
        for a in frontier:
            for b in all_masks:
                na, nb = dag[a], dag[b]
                if nb < na: na, nb = nb, na
                base = len(gate_set(dag[a]) | gate_set(dag[b]))
                if base + 1 > max_gates: continue
                for op, val in (('and', a & b), ('or', a | b)):
                    node = (op, na, nb)
                    if add(val, node, base + 1):
                        new_frontier.append(val)
                        if val == target:
                            return dag[target], size[target]
        all_masks += new_frontier
        frontier = new_frontier
        if not frontier: break
    return None, None

def flatten(node):
    """Topologically sorted gate list; returns (gates, output wire index, n_inputs)."""
    order = []
    def visit(nd):
        if nd[0] == 'in': return nd[1]
        a, b = visit(nd[1]), visit(nd[2])
        order.append((nd[0], a, b))
        return None
    # wire indices need the input count; computed by caller via a wrapper
    return order

def build_circuit(n, m, node):
    gates = []
    wire_of = {}
    def visit(nd):
        if nd in wire_of: return wire_of[nd]
        if nd[0] == 'in':
            wire_of[nd] = nd[1]; return nd[1]
        a, b = visit(nd[1]), visit(nd[2])
        gates.append((nd[0], a, b))
        wire_of[nd] = n + m + len(gates) - 1
        return wire_of[nd]
    out = visit(node)
    return gates, out

def lean_up(n, m, M, gates, out_wire):
    gs = ", ".join(f"⟨PEqualNP.CircuitLowerBounds.GateOp.{op}, [{a}, {b}]⟩" for op, a, b in gates)
    k = len(gates)
    cases = " | ".join(["rfl"] * k) if k else "rfl"
    return f"""theorem up : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin {n}) (v : Fin {m}) => Nat.testBit {M} ({m} * u + v)) {k} := by
  refine ⟨⟨[{gs}], {out_wire}⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with {cases} <;> simp
"""

if __name__ == "__main__":
    n, m, M = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    max_gates = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    node, sz = synth(n, m, M, max_gates)
    if node is None:
        print(f"no circuit with <= {max_gates} gates found")
        sys.exit(1)
    gates, out = build_circuit(n, m, node)
    print(f"size={len(gates)} output_wire={out} gates={gates}")
    print(lean_up(n, m, M, gates, out))
