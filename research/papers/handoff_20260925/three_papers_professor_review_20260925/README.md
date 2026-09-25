# A/B/C — professor review / Overleaf source bundle

This bundle contains the revised three main papers, their three supplements, shared preamble,
and every figure referenced by them. No manuscript compilation or new experiment was run
for this revision. Existing PDFs of the papers in the repository are older than this source.

Choose paper_a.tex, paper_b.tex, or paper_c.tex as the Overleaf main document. Compile each
supplement separately. The figure search path includes figures/. Bibliographies are inline;
no external .bib file is needed. Use a current pdfLaTeX installation with IEEEtran and the
packages named in preamble.tex. Compile twice or use latexmk; inspect layout and log output.

Draft notes are intentionally enabled in preamble.tex. They include the pending frozen-gate
check for BShareTournament. Do not hide a note to treat its obligation as completed.
C's robust-ball corollary and A's clipped-mixture corollary have explicit mathematical proofs;
the main text distinguishes them from separately compiled Lean wrappers.

Read MANUSCRIPT_REVIEW_AND_NEXT_ACTIONS.md for the exact audit scope, changes, data checks,
and remaining handoff actions. No claim is made that publication is guaranteed.
