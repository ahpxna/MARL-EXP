# Novelty-collision search — protocol for the researcher

Three manuscripts, one programme: **the price of a constraint**. Each asks how much a
restriction costs, measured exactly, on a construction where the cost can be computed.

| Brief | Paper | Constraint whose price is measured |
|---|---|---|
| `A_surrogate_evidence_geometry.md` | A | replacing the true alternative set of a decision by a cheaper surrogate |
| `B_safe_decision_vs_identification.md` | B | having to identify the world instead of only choosing a safe answer |
| `C_retention_band_price.md` | C | forcing each item's retention probability into a band when one randomised ranking serves every budget |

**The story all three must carry** (agreed in the supervision thread, 2026-09-2x): three
exact results about *the price of solving the wrong intermediate problem*:

- **A** — optimising the wrong oracle. An optimal surrogate design can carry zero
  information for the real decision.
- **B** — distinguishing more worlds than the decision needs. The safe decision and
  identification have different observation orders on one channel.
- **C** — optimising a ranking distribution while misjudging how it is used. A per-item
  retention band, or choosing the budget after the draw, each costs a linear factor.

A collision that removes one of these central results matters far more than one that removes
a supporting lemma. Say explicitly, for each paper, whether its central result survives.

Your job is to find prior work that **already contains** one of our headline results, or
makes it a relabelling. Finding that a topic is known is not enough. We already concede
every topic-level overlap listed in each brief.

## What counts

Classify every candidate source against a named headline (`A-H1`, `B-H2`, …):

| Verdict | Meaning | Consequence for us |
|---|---|---|
| **COLLISION** | A theorem in the source implies our headline, possibly after relabelling (cells ↔ arms, budget ↔ house size, …) and specialising parameters. | We cite it and drop or narrow the claim. |
| **PARTIAL** | The source proves a component: one direction, one parity, a special size, the same bound with a weaker constant or under an extra assumption, or the machinery we use. | We cite it for that component and state exactly what is added. |
| **ADJACENT** | Same topic, different theorem. The quantifiers, objective, observation model or answer structure differ in a way that blocks the implication. | Cite it in related work, with one sentence on the difference. |
| **NONE** | Not relevant after reading. | Record it, so it is not re-checked. |

Rules:

1. **Read the theorem, not the abstract.** Record the theorem, lemma or proposition number,
   and the page or section. A verdict without a located statement counts as unverified.
2. **Check the quantifiers.** Order of "for all / there exists", fixed versus growing
   dimension, known versus learned parameters, fixed-confidence versus fixed-budget,
   worst-case versus Bayesian, exact value versus order, strict versus closed alternatives.
   Each brief lists the quantifiers that carry our claim.
3. **Try to derive our result from the source.** Write the relabelling explicitly. If it
   works, the verdict is COLLISION even if the source never mentions our setting.
4. **Machinery is not a collision.** Track-and-Stop, mixture martingales, change of
   measure, moment matching, flow/DAG LPs and Birkhoff–von Neumann decompositions are tools
   we use and concede. Only a result about our object counts.
5. **Quote sparingly.** At most one or two sentences per source; summarise the rest in your
   own words.
6. **Citation metadata in the briefs comes from memory.** Verify the title, authors, venue
   and year before relying on any of it. A candidate we name may not exist in the form given;
   say so if it does not.

## Existing screening (do not redo)

`research/literature_audit_20260921/` is an earlier sweep: 84 OpenAlex queries, 11 arXiv
queries, a 4,537-record corpus, and a 1,000-paper reading queue of which **240 abstracts**
were screened (`reading_progress.json`). Nothing was read in full. Its summary is:

- A — "generic decision-focused proxies and targeted acquisition already have close prior
  art";
- B — "higher-order leakage … strong masking prior art";
- C — "robustness currently lower bound only".

The four closest sources it flagged are arXiv 2505.03953, arXiv 2210.12122, arXiv 2303.17062
and IACR ePrint 2015/119. Start from them, then go to the candidates in each brief. Use the
reading queue for leads, but make full-text, theorem-level checks.

## Deliverable

One file per paper, `research/papers/novelty_briefs_20260924/RESULT_<A|B|C>.md`, with:

1. A table with columns:
   `headline | source (full citation) | located statement | verdict | the relabelling (for COLLISION/PARTIAL) or the blocking difference (for ADJACENT) | what we must change in the manuscript`.
2. A short list of the searches run (database, query, date, number screened), so that
   coverage can be judged.
3. For each headline, a one-line bottom line: survives / survives narrowed as … / does not
   survive.

Where the manuscripts already cite something, the briefs say so. Check that our description
of it is fair: a claim that a source "leaves X open" must be verified in the source.
