# MARL — kiểm lại toàn cảnh kết quả hiện có, 28/09/2026 16:11 EDT

Audit độc lập, đọc actual code + raw rows + saved choices. Không chạy lại training, rollout hoặc final test. Không sửa producer, ledger hay manuscript. Phạm vi chính: toàn bộ nhóm kết quả E3 hiện có, F2-C, F5b, F1, runtime v5 và integrity audit mới. B2/B4/E1 giữ kết luận của các audit trước; không nói đã chạy lại toàn bộ lịch sử hoặc toàn repo.

## 1. Trạng thái thực, khác với báo cáo cũ

- BC s0..s4 đều train và message-use xong. G1: s0 FAIL; s1/s2/s3/s4 PASS. Recipe BC vẫn trượt gate pilot theo protocol; downstream là mô tả/chẩn đoán.
- Scratch s3 train/G1/selector/closed-loop xong. Scratch s1/s2/s4 trong e3_scratch_rs_20260928 đã có manifest COMPLETE; best SELECT lần lượt 1341.125, 1364.75, 1315.0. CHƯA có message-use hoặc downstream nên chưa được gọi là 4 seed thành công của method. Scratch s0 chưa COMPLETE, log cuối lúc đọc ở iteration 1773.
- Mixed-profile s3 train và message-use xong; selector labels đang chạy, chưa shard nào COMPLETE lúc đọc. Chưa có selector hoặc closed-loop result.
- Dense: SELECT 304 state và DEV 304 state COMPLETE; train shard 2 và 5 COMPLETE (399 state mỗi shard), bốn shard khác chưa xong. Chưa có f1_paired_original_states.json. Shard 3 log ghi watchdog kill vì stall lúc 15:56:42; cần kiểm restart, không kết luận nó đã resume chỉ từ việc có watchdog.
- Runtime v5, runner dense F1, label integrity audit và seed-deviation note đã có. Các thiếu sót cũ không còn được báo như chưa làm.
- Final protocol vẫn DRAFT; chưa tới freeze hoặc final test.

## 2. Actor mix: số đúng, nhưng không được diễn giải quá

Đọc MARL_e3_message_use.py, CommAdapter.encode/remember, msguse/rows.json, report.json và manifest. Declared source hashes đều khớp. Tính lại mean paired relative change khớp từng số. Dưới đây là % waiting của variant so với actual; số dương là tệ hơn. CI là bootstrap 8 traffic-seed clusters (hai loads giữ cùng nhau), 10,000 draws; Monte Carlo CI có thể dao động nhỏ.

| variant | mean | seed-cluster CI95 |
|---|---:|---|
| MP2 | +22.44% | [16.87,27.48] |
| none | -0.90% | [-2.28,0.62] |
| stale | +7.51% | [5.66,9.48] |
| shuffle | +4.90% | [2.66,7.37] |
| full | -1.85% | [-4.32,0.16] |

none changes 42.76% of same-state greedy actions, but does not measurably worsen episode waiting. G1 FAIL is therefore correct under the declared rule. Compared on paired episodes, mix waiting is +0.57% vs scratch s3, cluster CI [-1.75,3.05]: no demonstrated advantage or equivalence.

Important interpretation:
- The omitted stale result is stronger than the full-information improvement: old messages clearly hurt this actor; full improvement is not significant.
- This establishes sensitivity to message identity/freshness, not that a legal selector can exploit it. It does not prove message selection has little headroom; wait for its own oracle/selector results.
- none is an INPUT ablation: the simulator still sends the prefix and maintains caches; messages are removed from actor encoding. It is not yet a measured zero-byte deployment policy. full changes capacity to all senders and is not a same-budget comparator.
- A single seed supports a robustness observation, not a causal/general claim that mixture training causes robustness.
- The mix downstream runner explicitly inherits G1/G2 reading and runs later stages regardless. Keep those stages as diagnostic after this FAIL; do not quietly relabel the gate or promote a positive outcome to gated confirmation. No reason here to kill the authorised diagnostic run.

## 3. Learned-actor and selector summary

All finished standard actor message-use raw means independently match reports; declared producer hashes match. BC MP2-relative differences range +9.51% to +14.04%, scratch s3 +23.10%, mix +22.44%. The denominator is actor waiting: do not rewrite “MP2 22.4% worse” as “actor waiting reduced 22.4%”.

Closed-loop v2 ablation means recalculated from raw rows; values are % waiting vs the same actor + prefix, averaged across selector initializations:

| actor | no bid | bid | response head | bid + response |
|---|---:|---:|---:|---:|
| scratch s3 | -0.05 | +0.00 | -0.41 | -0.46 |
| BC s0 | +1.97 | +2.91 | +2.04 | +1.85 |
| BC s1 | +2.45 | +3.89 | +4.13 | +2.52 |
| BC s3 | +3.15 | +2.34 | +2.28 | +3.37 |

No new legal-selector success is established. Scratch differences remain insignificant in the existing episode/seed sensitivity reports; BC outcomes are descriptive under its failed recipe gate. Offline multiclass, same-byte queue, and 24-label acquisition arms remain negative. SchedNet-style results remain frozen-actor adaptations, not full original-method reproduction.

## 4. F5b independently checked — substantive evidence, two new corrections

Read MARL_e3_multireceiver_decomp.py, all 12 shard manifests/rows (48 states per actor), the original DEV label tables and 30 selector job files. Recomputed each selected gain from saved candidate indices in the ORIGINAL loader order; every gain matches, every selected profile respects that arm's byte allowance, no missing/duplicate state; declared source hashes match. Do not sort label records independently of saved indices.

Reported decomposition reproduced:

| quantity (H=3 gain units) | scratch s3 | BC s3 |
|---|---:|---:|
| best in candidate family, +84 B | 15.4375 | 12.3333 |
| search started at family best | 20.0833 | 16.0417 |
| search started at prefix | 17.5833 | 13.7917 |
| coverage lower bound using family-start search | 4.6458 | 3.7083 |
| R1 restriction INSIDE the candidate family | 2.6875 | 2.5000 |
| byte restriction INSIDE the family | 0.0625 | 0.1250 |
| legal selector realised gain | -0.1875 | -1.3125 |
| family-best minus legal chosen | 15.6250 | 13.6458 |

### Finding N1: “best found” is not the best of both searches

V_LS is only the search starting at the family optimum. V_LSP is better in 8/48 scratch and 6/48 BC states. If the paper calls the quantity BEST FOUND, use max(V_LS,V_LSP) PER STATE before aggregation:
- corrected best found: 20.75 / 16.2917;
- corrected coverage lower bound: 5.3125 / 3.9583;
- prefix-start search share of this best found: about 84.7% / 84.7%, instead of 88% / 86%.

No rollouts needed. Keep old named quantities; update report and manuscript wording/numbers or name them specifically as family-start search. Both remain achieved values, not global optima. Coverage is a lower bound; the true global gap could be larger. A nonzero restricted-family R1 gap does NOT certify the same geometric gap over the full profile space.

### Finding N2: “estimation loss” includes the stopping/abstention rule

The measured term is exact regret of the CHOSEN profile relative to the best available feasible candidate. Selection uses a tuned threshold, so the chosen profile need not maximise the critic. Calling this term purely 2 epsilon, or saying search nu=0 for the deployed thresholded rule, is unjustified.

Re-evaluated the six legal bid+head checkpoints on saved DEV data, without training/rollouts:

| actor/init | tau | realised gain | gain of unthresholded critic argmax | decisions changed by threshold /48 |
|---|---:|---:|---:|---:|
| scratch/0 | 11.746 | 0.0000 | -0.1667 | 43 |
| scratch/1 | 5.664 | 0.3125 | 0.3125 | 22 |
| scratch/2 | 11.098 | -0.8750 | 0.4375 | 34 |
| BC/0 | 1.595 | -1.7500 | -2.0208 | 10 |
| BC/1 | 5.351 | -0.7917 | -2.1042 | 23 |
| BC/2 | 0.0085 | -1.3958 | -1.3958 | 1 |

Mean predicted optimisation gaps max(fhat)-fhat(chosen) are 5.0158/1.0860/2.9045 (scratch) and 0.0856/1.0231/0.0002 (BC): nonzero. This is a diagnostic on stored data, not a proposal to retune on DEV. Removing the threshold does not establish a successful method: scratch argmax mean is only +0.1944 and BC remains negative; no success claim or checkpoint selection follows.

Worker fix: name the term “within-family selection regret (estimation + decision-rule effects)”. Report ranking loss and signed threshold effect separately. The identity is

    V_family - f(chosen)
      = [V_family - f(critic_argmax)] + [f(critic_argmax)-f(chosen)].

The second term can be negative when thresholding helps. To invoke the Lean deployed_regret bound, account for its hSearch/nu assumption, not only epsilon. Keep the statement “the tested rule fails to extract available headroom”; do not claim all global regret is proved to arise from estimation.

## 5. Old blockers: what is actually fixed

- Runtime v5: code explicitly parses threshold formats, rejects privileged checkpoints, has train/runtime score and choice comparisons and byte-parity checks. Existing dev smoke reports PASS. I inspected these paths; did not rerun the simulator. It compares checkpoint PATH, not content hash; final freeze must still pin actual actor/selector files.
- F1 runner now separates registered v2 from added v3; uses a common DEV table, original SELECT comparison and matched-step arm; includes dense acquisition. Inputs remain incomplete, so this is ready code, not an F1 result.
- Label audit now checks keys, canonical records, conflicts, old log failures and producer attribution. The saved 39-directory snapshot has no reported hard defect. It was taken at 13:51 and cannot certify subsequently completed/resumed shards: rerun AFTER all dense shards finish. This is integrity/provenance evidence, not a rerollout of every label.
- Seed-deviation note now honestly distinguishes launch time from later selective reporting; final inclusion and aggregation still need freeze.
- Cluster sensitivity exists for prior panels. Newly finished mix results need inclusion; the recalculation above shows the main reading survives clustering.

## 6. Work to completion, no new architecture search

1. Close N1/N2 in F5b report, claim map and manuscript from existing data. Keep raw artifacts unchanged.
2. Check dense shard3 restart and redundant scratch/mix runs with the worker's process ownership; do not start duplicate writers or stop jobs just because their outcomes are bad. Use the pre-declared run-of-record rule. No process was killed in this audit.
3. Run message-use for completed scratch s1/s2/s4 and downstream on their frozen checkpoints; do not call training SELECT scores generalisation results. s0 still finishes its declared budget.
4. Finish dense, then integrity audit + registered analysis + added paired analysis + registered dense acquisition. Finish the authorised mix diagnostic, documenting G1 failure and its evidence class.
5. Decide the final recipe/comparator and endpoint using development only. The current protocol is DRAFT. Do not take a non-significant result as equivalence or invent a beneficial resource trade-off.
6. Freeze checkpoints, all resources, candidate generator, runtime, gate handling, actor/traffic aggregation and endpoint before fresh final seeds. Then final evaluation, figures, manuscript, reproducibility and venue format.

The method goal is unchanged. Current evidence supports actor competence, real oracle revision opportunities and a failure of the tested legal selectors to exploit them. It does not yet demonstrate the proposed selector's MARL advantage. No new novelty/priority search was performed in this result audit.
