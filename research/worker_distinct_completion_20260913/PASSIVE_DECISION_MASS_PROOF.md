# R4 passive certification: impossibility and decision-specific mass

Status: human-readable proofs; not yet a compiled probability-process Lean package.

## Impossibility at the all-safe anchor world

Use the actual two-tip family m=2. For W empty, both singleton decisions have radius zero. For W={j}, the multi-tip radius formula gives decision j radius 1/2 and the other decision radius zero. Let P0 put all mass at the anchor and P(j,eta) assign eta>0 to tip j and the rest to the anchor. Support radius depends on support, not the tip's mass.

Allow a randomized passive procedure, with one independent random seed U whose law is the same in every world. It must return one of the two decisions. Suppose it stops almost surely under P0 and is uniformly delta-correct for epsilon<1/2 and delta<1/2. Under P0 some output j has probability at least 1/2. The increasing events {tau<=N, output=j} converge to {output=j}, so some finite N has probability a>delta.

Under P(j,eta), use the same seed U and independent Bernoulli indicators selecting anchor or tip. On the event that the first N observations are anchors, all prefix decisions through N coincide with P0. Thus its error probability is at least (1-eta)^N a. If N>0 choose 0<eta<1-(delta/a)^(1/N); if N=0 choose any eta in (0,1). In both cases error exceeds delta, a contradiction. The argument includes randomized stopping and arbitrary computation. It does not need Pinsker or a bound on expected stopping time.

## Positive condition only on decision-relevant witnesses

Let there be finitely many feasible decisions D, with at least one epsilon-good decision at every allowed world. Suppose an observable witness set H_d is specified for each decision, with:

1. Soundness: if d is epsilon-good, P(H_d)=0.
2. Separation: if d is not epsilon-good, P(H_d)>=p, for a known p in (0,1].

After N iid observations retain the decisions with no observed witness, and choose any retained decision. A good decision survives almost surely, so the retained set is nonempty almost surely. For each bad d its survival probability is (1-P(H_d))^N<=(1-p)^N. A union bound gives

    P(return an epsilon-bad decision) <= |D| (1-p)^N.

For 0<p<1 any integer N>=log(|D|/delta)/(-log(1-p)) suffices. For p=1, one observation suffices. This condition places no lower mass bound on support points outside the union of dangerous witness sets, and does not require recovering the full support.

For the multi-tip singleton construction, take H_j={tip j}. A present tip makes exactly decision j unsafe at tolerance below (m-1)/2, and observing it eliminates j. Anchor mass is unrestricted. All present decision-relevant tips must have mass at least p, but additional support points irrelevant to every feasible decision can have arbitrarily small masses. The model class must exclude arbitrarily rare dangerous tips: otherwise the impossibility family applies again.

This is a precise sufficient condition, not a characterization of the weakest possible regularity. For general oscillation geometry, a witness may require a pair of support samples; use independent sample pairs and apply the same proof to pair-witness sets. Do not assert a one-sample witness where geometry only exposes diameter through pairs.

## Dense exactly-one-missing benchmark

Let n=m-1 tips be present with individual mass (1-rho)/n and anchor mass rho<1. After seeing k<n distinct tips, each unseen tip has positive conditional probability under every still-consistent missing-tip world. If at least two possible missing tips remain, no decision is safe under every such world. A zero-error procedure therefore cannot stop before observing all n present tips, apart from null events. Conversely, seeing all n identifies the missing tip and is sufficient.

The waiting time from k seen tips to k+1 is geometric with success probability (n-k)(1-rho)/n. Independent stages give

    E tau = n H_n/(1-rho),
    Var tau = n^2/(1-rho)^2 * sum_{j=1}^n 1/j^2 - n H_n/(1-rho).

Membership queries need m-1 in the worst case: ask distinct tips until a NO identifies the missing one, or all m-1 YES replies leave the final tip missing. The lower bound follows because fewer than m-1 YES replies leave two indistinguishable candidate missing tips. This compares worst-case membership depth with passive expected stopping time, not two expectations under a shared prior.
