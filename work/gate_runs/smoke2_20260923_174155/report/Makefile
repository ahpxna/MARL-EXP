all: .lake/build/lib/lean/LeanPaperCFamilyV1.olean .lake/build/lib/lean/LeanPaperCInstantiationV1.olean .lake/build/lib/lean/LeanPaperCBandV1.olean .lake/build/lib/lean/LeanPaperCRankingV1.olean .lake/build/lib/lean/LeanPaperCBreakpointV1.olean

.lake/build/lib/lean/LeanPaperCFamilyV1.olean: LeanPaperCFamilyV1.lean .lake/build/lib/lean/LeanPaperCInstantiationV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperCFamilyV1.olean.tmp LeanPaperCFamilyV1.lean > logs/LeanPaperCFamilyV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperCFamilyV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperCFamilyV1.olean.tmp .lake/build/lib/lean/LeanPaperCFamilyV1.olean; fi; echo "LeanPaperCFamilyV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperCInstantiationV1.olean: LeanPaperCInstantiationV1.lean .lake/build/lib/lean/LeanPaperCBandV1.olean .lake/build/lib/lean/LeanPaperCRankingV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperCInstantiationV1.olean.tmp LeanPaperCInstantiationV1.lean > logs/LeanPaperCInstantiationV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperCInstantiationV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperCInstantiationV1.olean.tmp .lake/build/lib/lean/LeanPaperCInstantiationV1.olean; fi; echo "LeanPaperCInstantiationV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperCBandV1.olean: LeanPaperCBandV1.lean .lake/build/lib/lean/LeanPaperCBreakpointV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperCBandV1.olean.tmp LeanPaperCBandV1.lean > logs/LeanPaperCBandV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperCBandV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperCBandV1.olean.tmp .lake/build/lib/lean/LeanPaperCBandV1.olean; fi; echo "LeanPaperCBandV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperCRankingV1.olean: LeanPaperCRankingV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperCRankingV1.olean.tmp LeanPaperCRankingV1.lean > logs/LeanPaperCRankingV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperCRankingV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperCRankingV1.olean.tmp .lake/build/lib/lean/LeanPaperCRankingV1.olean; fi; echo "LeanPaperCRankingV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperCBreakpointV1.olean: LeanPaperCBreakpointV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperCBreakpointV1.olean.tmp LeanPaperCBreakpointV1.lean > logs/LeanPaperCBreakpointV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperCBreakpointV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperCBreakpointV1.olean.tmp .lake/build/lib/lean/LeanPaperCBreakpointV1.olean; fi; echo "LeanPaperCBreakpointV1 exit=$$rc"; exit $$rc

