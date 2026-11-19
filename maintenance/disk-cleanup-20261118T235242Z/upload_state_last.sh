#!/bin/bash
# Pack the 145 finished-run state_last.pt files into tar.zst parts (<2 GB each) and upload them as assets of a GitHub
# Release (not into git history, so the local .git does not grow). Local files are NOT deleted here.
set -euo pipefail
cd /Users/phanan/cig-amf-main
M=maintenance/disk-cleanup-20261118T235242Z; U=$M/upload; TAG=state-last-20261118
echo "start $(date)"
tar -cf - -T $M/state_last_targets.txt | zstd -T0 -6 -q | split -b 1900m -d -a 2 - $U/state_last_finished_20261118.tar.zst.part
ls -l $U
( cd $U && shasum -a 256 state_last_finished_20261118.tar.zst.part* > parts_sha256.txt )
echo "pack done $(date)"
cat $U/state_last_finished_20261118.tar.zst.part* | zstd -dc -q | tar -tf - | sort > $U/tar_listing.txt
sort $M/state_last_targets.txt | diff - $U/tar_listing.txt && echo "LISTING OK"
cp $M/state_last_targets.txt $M/state_last_sha256.txt $M/state_last_sizes.txt $U/
gh release create $TAG --repo ahpxna/MARL-EXP --title "state_last.pt of finished MARL runs (18/11/2026)" \
  --notes "Resume-only training states (student, Adam, DAgger buffer, RNG) of 145 finished runs, removed from the working tree to free disk. Restore: cat state_last_finished_20261118.tar.zst.part* | zstd -dc | tar -xf - (from the repo root); check with shasum -a 256 -c state_last_sha256.txt." \
  $U/state_last_finished_20261118.tar.zst.part* $U/parts_sha256.txt $U/state_last_sha256.txt $U/state_last_targets.txt $U/state_last_sizes.txt
echo "upload done $(date)"
gh api repos/ahpxna/MARL-EXP/releases/tags/$TAG --jq '.assets[] | "\(.digest | sub("sha256:";""))  \(.name)"' | sort -k2 > $U/remote_digests.txt
( cd $U && sort -k2 parts_sha256.txt ) | while read h n; do grep -q "^$h  $n$" $U/remote_digests.txt && echo "OK $n" || echo "MISMATCH $n"; done
echo "end $(date)"
