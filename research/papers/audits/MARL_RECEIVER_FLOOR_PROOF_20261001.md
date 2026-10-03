# A receiver-age floor for prefix broadcast with relay (proof, 01/10/2026 19:3x EDT)

Status: paper proof below; Lean `work/p13_conjectures/LeanMarlReceiverFloorV1.lean` (compiling at the time of writing; see
ledger L-223 for the result).  Origin: the Lean/papers subagent's conjecture H1 (with an extra `+ c_i` term), checked
numerically by it and independently here (20 000 random schedules m ≤ 10, K ≤ 4, and exhaustive m = 5 / K = 1 / 4 steps
(160 000 schedules) and m = 6 / K = 2 / 3 steps: no violation, maximum excess 0, i.e. tight).  The proof found here gives the
SHARPER statement without the `+ c_i` term.

## Model
Agents `V`, `|V| = m`.  Constant capacity `K` (1 ≤ K ≤ m − 2).  At every step `s` the scheduler commits an order `π_s`
of `V`; receiver `r` decodes the first `K` packets of `π_s` other than its own.  Write `P_s` for the senders in positions
0 … K − 1 (public) and `h_s` for the sender in position `K` (hidden).  Then
- a receiver `r ∉ P_s` decodes exactly `P_s`;
- a receiver `r ∈ P_s` decodes `(P_s \ {r}) ∪ {h_s}`.
Relay: the packet of sender `o` at step `s` carries `o`'s fresh state (measured at `s`) and everything `o` knows at the
end of step `s − 1`.  Receivers never forget (the most generous memory; the E3 relay merge, which forgets relayed copies
it does not re-receive, knows a subset, so every bound below holds for it too).

Fix a window of `n` consecutive steps `s = 0, …, n − 1` (relative indexing).  `N_r(s)` = senders of whom `r` holds a
measurement taken at a window step, after window step `s − 1` (so `N_r(0) = ∅`), and

  N_r(s + 1) = N_r(s) ∪ ⋃_{o decoded by r at s} ({o} ∪ N_o(s)).

`Pub(s)` = senders of whom some public packet of a window step `< s` carried a window measurement:

  Pub(0) = ∅,   Pub(s + 1) = Pub(s) ∪ ⋃_{o ∈ P_s} ({o} ∪ N_o(s)).

The private part of `r` is `Q_r(s) = N_r(s) \ Pub(s)`.

## Lemma 1 (private pool).  For all s and r: |Q_r(s)| ≤ 1, and Q_r(s) ≠ ∅ ⇒ r ∈ Pub(s).
Induction on `s`; `s = 0` is empty.  Step `s → s + 1`:
- `r ∉ P_s`: `r` decodes only `P_s`, whose packets are public, so `N_r(s+1) ⊆ N_r(s) ∪ Pub(s+1)` and
  `Q_r(s+1) ⊆ Q_r(s)` (Pub only grows).  Both claims carry over (r ∈ Pub(s) ⊆ Pub(s+1)).
- `r ∈ P_s`: `r`'s own packet at `s` is public, so `N_r(s) ⊆ Pub(s+1)`; the packets of `P_s \ {r}` are public too.  The
  only non-public input is `h_s`'s packet, so `Q_r(s+1) ⊆ ({h_s} ∪ N_{h_s}(s)) \ Pub(s)`.  If `Q_{h_s}(s) = ∅` this is
  `⊆ {h_s}`; otherwise `h_s ∈ Pub(s)` by induction and it is `⊆ Q_{h_s}(s)`, of size ≤ 1.  And `r ∈ P_s ⇒ r ∈ Pub(s+1)`.  ∎
(In words: a private fact is created only in the hidden slot, which only public receivers decode; and a public receiver's
packet releases everything it knew before, so each receiver's private pool is refreshed, never accumulated.)

## Lemma 2 (public growth).  |Pub(s + 1)| ≤ |Pub(s)| + K, hence |Pub(n)| ≤ K n.
The new senders are `⋃_{o ∈ P_s} ({o} ∪ N_o(s)) \ Pub(s)`.  For each `o`: if `Q_o(s) = ∅` the term is `⊆ {o}`; otherwise
`o ∈ Pub(s)` (Lemma 1) and the term is `Q_o(s)`, of size ≤ 1.  So each of the ≤ K public packets adds ≤ 1 sender.  ∎

## Theorem (receiver floor).  For every scheduler, every receiver i and every window of n steps:
  |N_i(n) \ {i}| ≤ K n.
`N_i(n) ⊆ Pub(n) ∪ Q_i(n)`.  If `Q_i(n) = ∅`, `|N_i(n) \ {i}| ≤ |Pub(n)| ≤ K n`.  Otherwise `i ∈ Pub(n)` (Lemma 1), so
`|N_i(n) \ {i}| ≤ |Pub(n) \ {i}| + |Q_i(n)| ≤ (K n − 1) + 1`.  ∎

The (K+1)-th packet that public receivers decode adds nothing: the bound is what an ideal channel of exactly K public
packets per step would give.  Lean: `receiver_floor` (and `private_pool`, `pub_card_le`).

## Corollaries (ages)
Age `a_t(i, j)` = t − (latest measurement step of `j` known to `i`), `∞` if never heard.  `j ∈ N_i` for the window of the last
`d + 1` steps ⇔ `a_t(i, j) ≤ d`.  So for every `t ≥ d`:

1. **Forced stale count** (Lean `forced_stale`): `#{j ≠ i : a_t(i, j) > d} ≥ m − 1 − K (d + 1)`.
2. **Forced-tail predicate.**  If `K (τ + 1) < m − 1`, every receiver at every step `t ≥ τ` holds at least
   `m − 1 − K (τ + 1) ≥ 1` copies older than `τ`, for EVERY scheduler and relay rule.
3. **Burden floor (layer cake).**  `Σ_j (a_j − τ)+ = Σ_{d ≥ τ} #{j : a_j > d} ≥ Σ_{d ≥ τ} (m − 1 − K (d + 1))+`
   (for `t` large enough that the windows fit; with the 4-bit age field saturated at 14 the sum stops at d = 13).
4. **Mean-age floor.**  `(1/(m−1)) Σ_j a_j ≥ (1/(m−1)) Σ_{d ≥ 0} (m − 1 − K (d + 1))+`.

## Numbers (τ = the iid-training p99 of the maximum copy age, from the channel-only maps L-218)
| grid | m − 1 | τ_train | K forced (K(τ+1) < m−1) | burden floor Σ_{d≥τ}(m−1−K(d+1))+ | measured (age-first) | mean-age floor / measured |
|---|---|---|---|---|---|---|
| 3×3 | 8 | 3 | K = 1 only | K = 1: 10; K = 2: 0 | late-step B_3 10.84; K = 2 1.64 | K = 1 3.50 / 3.67; K = 2 1.50 / 1.75; K = 3 0.875 / 0.94 |
| 4×4 | 15 | 9 | K = 1 only | K = 1: 15 (never-heard counted old) | B_9 1.20 + never-heard 6.57 | — |
| 4×4 (τ = 3) | 15 | 3 | K = 1, 2, 3 | 66 / 16 / 3 | B_3 17.35 / 16.41 / 1.88 | — |
| 5×5 | 24 | 11 | K = 1 only | K = 1: 78 | B_11 9.65 + never 10.82 | — |
| 6×6 | 35 | 14 (cap) | K = 1, 2 (with ages capped at 14, the floor is reported for d ≤ 13) | — | — | — |
Observed signs so far (constant K): 3×3 K = 1 loses on four panels, K = 2, 3 win; 4×4 seed 0 (development) K = 1 loses, K = 2,
3 win — the predicate with the training-relative τ fits every cell; with τ = 3 it would predict 4×4 K = 2, 3 losses (not seen).

## Reading for the paper
- The floor is a property of the CHANNEL (m, K) and the TRAINING regime (τ_train) alone: computable before training or
  deployment, for every scheduler.  Where `K(τ_train + 1) < m − 1` no scheduler can keep a receiver inside its training
  age range, so the repair must happen at the receiver (training regime, interface); where the predicate is false the
  scheduler can (the covering head lowers 3×3 K = 2 burden 1.64 → 0.56 in the replica).
- Prior art (AoI): broadcast-scheduling age lower bounds with one packet per slot (Kadota et al. 2018), piggyback relay age
  under round-robin (Kaul, Yates, Gruteser 2011).  New here: prefix decoding with relay and memory, the private-pool lemma
  showing the extra hidden packet is worthless for the floor, and the use of the floor as a pre-deployment predicate for
  when a learned receiver is forced out of its training support.

## Generalisation to UNEQUAL receiver budgets (20:0x; answers the "toy constraint" risk)
Receiver `r` decodes the first `K_r(s)` packets other than its own; `K*(s) = max_r K_r(s)`.  Put `P_s` = positions `< K*(s)`
and `h_s` = position `K*(s)`.  A receiver outside `P_s` decodes positions `< K_r(s) ≤ K*(s)`, a subset of `P_s`; a receiver
inside `P_s` decodes positions `≤ K_r(s) ≤ K*(s)` minus itself, a subset of `P_s ∪ {h_s}`; only receivers in `P_s` with
`K_r = K*` decode `h_s`.  These two inclusions are all the proof above uses (Lemma 1: only the hidden packet creates private
knowledge, and only receivers in `P_s` decode it, whose own packets are public at `s`).  Hence:

**Theorem′ (richest-receiver floor).**  For every scheduler and every receiver `i`, at most `Σ_{s ∈ W} K*(s)` other senders
have a copy measured during the window `W`.  Freshness is bounded by the budget of the best-placed receiver, not by the
receiver's own: relay through a rich hub can make a weak receiver fresher than its own budget allows, and nothing can
make it fresher than the hub's budget allows.  (Correction 01/10 20:5x, L-229: an earlier version cited the rich7 return
experiment, +0.65 % vs Z, here.  That run is EXPLORATORY and missed its written prediction — relay wins on 7/10 seeds
against the pre-specified ≥ 8/10, with three seeds at −2 to −4 % — so it is not evidence for this sentence.)  Lean: `LeanMarlReceiverFloorV2` (abstract step with the two inclusions;
`receiver_floor`, `receiver_floor_const`, `Step.ofConst`).  Numerical check (own simulator, 15 000 heterogeneous
instances: i.i.d. budgets, one rich receiver, two-level budgets): maximum excess 0 for `Σ K*`; the own-budget bound fails
(excess 7) and the second-largest-budget bound fails (excess 8).

**Forced-exposure predicate.**  If some `τ + 1` consecutive steps have `Σ K*(s) < m − 1`, every receiver carries copies
older than `τ` at the end of them, whatever the scheduler.  The 3×3 regimes (τ_train = 3, m − 1 = 8; window sums of `K*`
from the actual capacity traces): iid min 24, cap4 16, random low 11, rich7 28, const K = 2 8, const K = 3 12 — not forced;
const K = 1: 4 — FORCED.  Observed: the age-first relay student loses to compiled silence exactly in the forced cell (four
panels) and wins in every other one.

**Locus of repair.**  Where the predicate is false, staleness is SCHEDULER-INDUCED and a scheduler can remove it — the
congestion-order failures at cap4 / low (paper_marl_v2: age-first ordering repairs them) and the hold-r schedules.  Where it is
true, staleness is CHANNEL-FORCED and no scheduler helps; the repair must be at the receiver (training regime, interface:
age clip +0.79 %, tail gate +0.78 %, matched training pending).

## Why the abstraction is not a toy (realistic instances of "one ordered broadcast, receivers decode a prefix")
- Receiver-driven layered multicast (McCanne, Jacobson, Vetterli, SIGCOMM 1996) and scalable/embedded coding: one source
  sends priority-ordered layers; each receiver subscribes to the prefix its bandwidth allows.
- Time-slotted (TDMA) team broadcast with duty-cycled or compute-limited receivers: senders transmit in a committed slot
  order each frame, and a receiver listens to (or processes) only its first `K_i` slots.
- Priority-ordered shared buses / message brokers where a node processes the first `K_i` messages per control cycle.
In all of them, unequal receiver budgets are the reason the constraint exists; the theorem says what freshness the shared
order can deliver to each receiver, and the experiments show what happens to a learned controller when the deployment
budget pattern leaves the training pattern.

## The net count and the provisioning rule (01/10/2026 23:4x; PROTOCOL_E3_NET_COUNT_20261001, ledger L-239, L-240)

**Corollary (net floor).**  At constant capacity `K`, for every scheduler, relay content and memory, every receiver `i` and
every step `t ≥ τ + 1`:  fresh_i + (m − 1) ≤ K (τ + 2) + stale_{i,τ}, where fresh = senders measured at the last step and
stale_τ = senders whose freshest copy at `i` is older than `τ` steps or absent.  Equivalently
**net_i := fresh_i − stale_{i,τ} ≤ K (τ + 2) − (m − 1).**
*Proof.*  `timed_floor` with `n = 1` gives fresh ≤ K; `timed_forced_stale` with `n = τ + 1` gives
stale_τ ≥ m − 1 − K (τ + 1); add.  Attained with equality by V1's witness.  Lean: `LeanMarlNetFloorV1.net_floor`,
`fresh_le`, `net_floor_witness` (compiling, 23:42).
With unequal or time-varying budgets the same argument with `LeanMarlReceiverFloorV2` / `LeanMarlPrefixInstanceV1` replaces
`K (τ + 1)` by the richest-receiver budget summed over the last `τ + 1` steps.

**Measured.**  Age-first attains the bound within 0.1–0.8 copies per receiver-step on 3×3 (stale + never 5.12 / 2.23 / 0.78
against 5 / 2 / 0 at K = 1 / 2 / 3).  A count-targeting order (count-deadline) reduces the stale count by exactly 0 at K = 1
and K = 2 and by 0.51 (≤ the room 0.78) at K = 3 — the bound is the binding constraint where the theorem says it is.

**Empirical link (not a theorem).**  Across 9 order × capacity cells the per-receiver mean net (τ = 2, the iid training
range) ranks the gain of relay over compiled silence with Spearman +0.983; out of sample, on 9 hold-r development cells
+0.850 and the frozen sign rule `net/(m − 1) > −0.08` classifies all 6 prospective hold cells.  The COUNT of stale copies
predicts better than their summed age (B_3): the receiver's harm per copy saturates with age (age-response probe).

**Provisioning rule (A).**  Combining the two: a scheduler can keep a receiver whose training range is τ_train on the
positive side only if  K > K_min = (1 + θ)(m − 1) / (τ_train + 2),  θ = −0.08.  3×3: iid-trained K_min = 1.84 (K = 1 forced
negative, observed); K = 1-trained K_min = 0.74.  4×4 (15 senders per view): iid-trained K_min = 1.25 with the training-
relative τ_train = 9, 3.45 with the absolute τ = 2 — the pending 4×4 const-K cells decide (Addendum 4).  The rule is
necessary, not sufficient (the scheduler must attain the bound; the receiver's lower band edge, "too fresh", is separate).
