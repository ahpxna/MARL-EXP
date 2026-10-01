# Deep research: how to handle the E3 problem (29/09/2026, written 09:00 EDT, clock-checked; workflow wru2h721k stalled at 01:17 on tool-permission interrupts, so the research was done inline)

## Verified sources (read, not only search snippets)
- Bertsekas, "Multiagent RL: Rollout and Policy Iteration" (MIT slides, 15/10/2020), pp. 11-19: rollout has J_rollout <= J_base
  when J_base is available "through simulation (possibly in conjunction with a trained neural net)"; with approximation
  J_rollout <= J_base + eps; one-agent-at-a-time rollout keeps the cost-improvement property with search linear in m;
  agent-by-agent PI stops at an agent-by-agent optimal policy.  http://athenasc.com/Multiagent_Rollout.pdf
- Xue, Yuan, Zhang, Yu, "Efficient Multi-Agent Communication via Shapley Message Value", IJCAI 2022, pp. 578-580:
  the marginal value of message j to receiver i is k_i(s)(Q_i(s, a_i^j) - Q_i(s, a_i)), i.e. the value of the ACTION CHANGE
  the message induces, under a linearly decomposable centralised critic Q_tot = sum k_i Q_i + b (DOP-style), with a
  selector trained from local observations during CTDE.  https://www.ijcai.org/proceedings/2022/0082.pdf
- McClellan, Haghani, Winder, Huang, Tokekar, "Boosting Sample Efficiency and Generalization in MARL via Equivariance",
  NeurIPS 2024, pp. 1-2: equivariant GNNs, up to 2-5x sample-efficiency gains, 5x over GNNs in generalisation tests.
- Weltevrede, Spaan, Böhmer, "Generalization in offline RL: the structure is more important than the amount of
  pessimism" (arXiv 2607.02288): value generalisation depends on whether the function respects the task's symmetries.
- Laroche et al., SPIBB (arXiv 1712.06924, abstract): bootstrap to the baseline where uncertainty is high; SPI guarantee.
  "Policy Learning with Abstention" (arXiv 2510.19672, AISTATS 2025, abstract): defer to a safe default when uncertain.
- Han, Dastani, Wang, "Model-based Sparse Communication in MARL", AAMAS 2023 (abstract): send only when others cannot
  estimate the message.  SchedNet (ICLR 2019) and MAGIC (AAMAS 2021): scheduler trained jointly with the policy.
- Kafadar et al., "Value-Aware Prediction for Robust Multi-Agent Coordination Under Communication Loss" (arXiv 2607.17914,
  abstract): advantage-weighted predictor; MPE only.

## New read-only check on stored data (forced-action rows, scratch s3, 48 DEV states)
- Forcing an agent to its actor's RUNNER-UP phase p2 (from the stored bid): mean gain -0.85, P(>0) 0.43, versus other
  alternatives -3.59, P(>0) 0.27; p2's rank among the agent's alternatives 0.30 (uniform 0.50).  The actor's own policy
  ranks alternatives.  But the state's best single change is a p2 flip only 17% of the time, and the logit gap does not
  rank WHICH agent's p2 flip pays (within-state Spearman 0.05).

## Reading
- The literature's device for exactly this headroom (improve a fixed base policy by changing single agents' actions) is
  ROLLOUT, and it needs J_base by simulation or a trained value; the E3 oracle is that rollout with the true simulator.
  With a model, direct agent-by-agent ACTION rollout is at least as good as message scheduling (L-81), so a
  message-scheduling method cannot claim that headroom as communication value.
- SMV values a message as the induced action change's value under a DECOMPOSED action-value critic trained with the
  actor.  E3's critics are flat post-hoc regressors on 768-2,432 labelled states; neither per-agent action values nor
  structure (equivariance) is used.  This is the main untested lever the literature points to (L-82 item 3 was dismissed
  too quickly: the privileged critic used the same flat architecture, so its 0.56 does not rule out a structural fix).
- SPIBB/abstention = the RL form of SafeEdit: with current critics it returns the prefix (no harm, no gain).

## Ranked routes
1. Analysis paper (high probability of being correct; data in hand).
2. Per-agent, parameter-shared action-advantage model trained on cheap forced-action rollouts, used as a value-aware
   1-byte bid (receiver reports its own runner-up advantage) + SafeEdit abstention.  First falsifiable test: can a
   shared per-agent model rank single-agent action changes on DEV (pair accuracy >= 0.65)?  If not, no value-based
   scheduler can work here.
3. Equivariant / pair-shared scheduler critic on the existing labels (cheapest test; answers "is the failure the
   architecture?").
4. Co-training scheduler + actor (SchedNet/MAGIC prior art; low novelty).  Not recommended.
