#!/usr/bin/env bash
# TSI poster v4: Fig. 3 from the W19 / W20 rows, two-pass layout (estimate -> LibreOffice render -> measured heights -> rebuild), and a
# print PDF WITHOUT image downsampling (LibreOffice's default export reduces images to 300 ppi of the 10-in page, i.e. ~62 dpi at 48 in).
set -euo pipefail
cd /Users/phanan/cig-amf-main; T=research/papers/TSI_two_population; W=${POSTER_WORK:-$T/build_v4}; mkdir -p $W
IN="Staged Upgrades of Two Learned Populations (1).pptx"; FG=$T/fig3_bars.png
external_envs/city_runtime/bin/python scripts/POSTER_tsi_fig3_repr.py && external_envs/city_runtime/bin/python scripts/POSTER_tsi_fig3_bars.py
.venv/bin/python scripts/POSTER_tsi_v4.py "$IN" $FG $W/p1.pptx
(cd $W && soffice --headless --convert-to pdf p1.pptx >/dev/null 2>&1)
.venv/bin/python scripts/POSTER_tsi_v4.py measure $W/p1.pdf $W/p1.pptx.pos.json $W/heights.json
.venv/bin/python scripts/POSTER_tsi_v4.py "$IN" $FG $T/TSI_poster_v4.pptx --heights $W/heights.json
(cd $T && soffice --headless --convert-to 'pdf:impress_pdf_Export:{"ReduceImageResolution":{"type":"boolean","value":"false"},"UseLosslessCompression":{"type":"boolean","value":"true"}}' TSI_poster_v4.pptx >/dev/null 2>&1)
pdfimages -list $T/TSI_poster_v4.pdf | awk 'NR > 2 && $3 == "image" {print "image", $4 "x" $5, "ppi on the 10-in page", $13, "-> dpi at 48 in", int($13 / 4.8)}'
pdftoppm -r 220 -png -singlefile $T/TSI_poster_v4.pdf $W/preview; echo "built $T/TSI_poster_v4.pdf"
