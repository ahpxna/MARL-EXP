import argparse
import json
import re
from pathlib import Path

import networkx as nx


TOPC_RE = re.compile(
    r"cell:topC:selected=(\d+):rejected=(\d+)"
)


def analyse(best):
    cell = best["cell"]
    m = int(cell["m"])
    selected = list(map(int, cell["selected"]))
    rejected = list(map(int, cell["competitor"]))

    # Top-C multiplier matrix
    topc = {
        str(i): {str(j): 0.0 for j in rejected}
        for i in selected
    }

    extrema = []

    G = nx.Graph()
    for i in selected:
        G.add_node(f"S{i}", side="selected", coordinate=i)
    for j in rejected:
        G.add_node(f"T{j}", side="rejected", coordinate=j)

    for row in best.get("active_inequalities", []):
        label = row["label"]
        dual = float(row["dual"])

        mt = TOPC_RE.fullmatch(label)
        if mt:
            i, j = map(int, mt.groups())
            if str(i) in topc and str(j) in topc[str(i)]:
                topc[str(i)][str(j)] += dual
            if abs(dual) > 1e-10:
                G.add_edge(f"S{i}", f"T{j}", weight=dual)
            continue

        if (
            "residual_max" in label
            or "residual_min" in label
            or "response_max" in label
            or "response_min" in label
        ):
            extrema.append({
                "label": label,
                "multiplier": dual,
            })

    components = list(nx.connected_components(G))
    degrees = dict(G.degree())

    leaf_selected = [
        n for n in G.nodes
        if n.startswith("S") and degrees[n] == 1
    ]
    leaf_rejected = [
        n for n in G.nodes
        if n.startswith("T") and degrees[n] == 1
    ]

    return {
        "cell_id": cell["signature"],
        "m": m,
        "q": cell["reference_probs"],
        "Gamma": best["gamma"],
        "cycle_mass": best.get("dual_cycle_mass"),
        "cycle_atoms": best.get("active_cycles", []),
        "active_constraint_multipliers": best.get(
            "active_inequalities", []
        ),
        "TopC_multiplier_matrix": topc,
        "extrema_multiplier_vector": extrema,
        "support_graph": {
            "nodes": list(G.nodes),
            "edges": [
                {
                    "u": u,
                    "v": v,
                    **attrs,
                }
                for u, v, attrs in G.edges(data=True)
            ],
        },
        "is_acyclic": nx.is_forest(G),
        "num_components": len(components),
        "leaf_selected": leaf_selected,
        "leaf_rejected": leaf_rejected,
        "has_leaf_pair": bool(
            leaf_selected and leaf_rejected
        ),
        # These require a second LP after mathematically defined pair removal.
        "reduced_cell_id": None,
        "mass_after_pair_removal": None,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sweep")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    d = json.load(open(args.sweep))
    rows = []

    for m, result in d["best_by_m"].items():
        if not result or not result.get("best"):
            continue
        rows.append(analyse(result["best"]))

    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    json.dump(rows, open(args.out, "w"), indent=2)
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()