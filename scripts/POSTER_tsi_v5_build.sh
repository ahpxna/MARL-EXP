#!/usr/bin/env bash
# TSI poster v5 (13/10/2026): POSTER_tsi_v4_build.sh with the v5 text (scripts/POSTER_tsi_v5.py) and Fig. 3 v5; v4 files are not touched.
# Fig. 3 data: the existing fig3_repr.json (not regenerated). Two-pass layout, print PDF without image downsampling.
set -euo pipefail
cd /Users/phanan/cig-amf-main; T=research/papers/TSI_two_population; W=${POSTER_WORK:-$T/build_v5}; mkdir -p $W
IN="Staged Upgrades of Two Learned Populations (1).pptx"; FG=$T/fig3_bars_v5.png
external_envs/city_runtime/bin/python scripts/POSTER_tsi_fig3_bars_v5.py
.venv/bin/python scripts/POSTER_tsi_v5.py "$IN" $FG $W/p1.pptx
(cd $W && soffice --headless --convert-to pdf p1.pptx >/dev/null 2>&1)
.venv/bin/python scripts/POSTER_tsi_v5.py measure $W/p1.pdf $W/p1.pptx.pos.json $W/heights.json
.venv/bin/python scripts/POSTER_tsi_v5.py "$IN" $FG $T/TSI_poster_v5.pptx --heights $W/heights.json
(cd $T && soffice --headless --convert-to 'pdf:impress_pdf_Export:{"ReduceImageResolution":{"type":"boolean","value":"false"},"UseLosslessCompression":{"type":"boolean","value":"true"}}' TSI_poster_v5.pptx >/dev/null 2>&1)
pdfimages -list $T/TSI_poster_v5.pdf | awk 'NR > 2 && $3 == "image" {print "image", $4 "x" $5, "ppi on the 10-in page", $13, "-> dpi at 48 in", int($13 / 4.8)}'
pdftoppm -r 220 -png -singlefile $T/TSI_poster_v5.pdf $W/preview; echo "built $T/TSI_poster_v5.pdf"
