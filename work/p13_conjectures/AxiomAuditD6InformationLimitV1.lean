import «LeanD6InformationLimitV1»

/-!
Audit of the abstract information-limit module. Each name must use at most
`[propext, Classical.choice, Quot.sound]`; an empty axiom set also passes.
`sorryAx` or `Lean.ofReduceBool` would fail this project's kernel-only audit.
This audit does not establish the missing bridge to actual D6 response profiles
and productCompressionLoss, nor a lower bound for randomized selectors.
-/

open CIGAMF.P13.InformationLimit

#print axioms CIGAMF.P13.InformationLimit.regretOn_eq_card_sdiff
#print axioms CIGAMF.P13.InformationLimit.selector_constant_on_family
#print axioms CIGAMF.P13.InformationLimit.filter_not_mem_powersetCard
#print axioms CIGAMF.P13.InformationLimit.card_filter_not_mem
#print axioms CIGAMF.P13.InformationLimit.sum_sdiff_card_powersetCard
#print axioms CIGAMF.P13.InformationLimit.choose_shift
#print axioms CIGAMF.P13.InformationLimit.information_limit_exact
#print axioms CIGAMF.P13.InformationLimit.information_limit_worst_case
