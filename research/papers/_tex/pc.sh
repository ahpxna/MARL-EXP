#!/bin/zsh
cd /Users/phanan/cig-amf-main/research/papers/_tex
tectonic -X compile $1.tex --keep-logs >/tmp/tec_$1.log 2>&1
E=$?
P=$(grep -oE "\[[0-9]+\]" $1.log | tr -d '[]' | sort -n | tail -1)
echo "$1: exit=$E pages=$P"
grep -E "^!|Error" /tmp/tec_$1.log | head -10
