all: .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean .lake/build/lib/lean/LeanCityReceiverContractV1.olean .lake/build/lib/lean/LeanMarlDecisionDepthV1.olean .lake/build/lib/lean/LeanMarlCommValueV1.olean .lake/build/lib/lean/LeanMarlFrozenFloorV1.olean .lake/build/lib/lean/LeanMarlTaskVsReconV1.olean .lake/build/lib/lean/LeanMarlSupportV1.olean .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean

.lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean: LeanMarlLegacyViewDecoderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean.tmp LeanMarlLegacyViewDecoderV1.lean > logs/LeanMarlLegacyViewDecoderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlLegacyViewDecoderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean.tmp .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean; fi; echo "LeanMarlLegacyViewDecoderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanCityReceiverContractV1.olean: LeanCityReceiverContractV1.lean .lake/build/lib/lean/LeanMarlSupportV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanCityReceiverContractV1.olean.tmp LeanCityReceiverContractV1.lean > logs/LeanCityReceiverContractV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanCityReceiverContractV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanCityReceiverContractV1.olean.tmp .lake/build/lib/lean/LeanCityReceiverContractV1.olean; fi; echo "LeanCityReceiverContractV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlDecisionDepthV1.olean: LeanMarlDecisionDepthV1.lean .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanMarlDecisionDepthV1.olean.tmp LeanMarlDecisionDepthV1.lean > logs/LeanMarlDecisionDepthV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlDecisionDepthV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlDecisionDepthV1.olean.tmp .lake/build/lib/lean/LeanMarlDecisionDepthV1.olean; fi; echo "LeanMarlDecisionDepthV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlCommValueV1.olean: LeanMarlCommValueV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlCommValueV1.olean.tmp LeanMarlCommValueV1.lean > logs/LeanMarlCommValueV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlCommValueV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlCommValueV1.olean.tmp .lake/build/lib/lean/LeanMarlCommValueV1.olean; fi; echo "LeanMarlCommValueV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlFrozenFloorV1.olean: LeanMarlFrozenFloorV1.lean .lake/build/lib/lean/LeanMarlSupportV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanMarlFrozenFloorV1.olean.tmp LeanMarlFrozenFloorV1.lean > logs/LeanMarlFrozenFloorV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlFrozenFloorV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlFrozenFloorV1.olean.tmp .lake/build/lib/lean/LeanMarlFrozenFloorV1.olean; fi; echo "LeanMarlFrozenFloorV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlTaskVsReconV1.olean: LeanMarlTaskVsReconV1.lean .lake/build/lib/lean/LeanMarlDecisionDepthV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanMarlTaskVsReconV1.olean.tmp LeanMarlTaskVsReconV1.lean > logs/LeanMarlTaskVsReconV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlTaskVsReconV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlTaskVsReconV1.olean.tmp .lake/build/lib/lean/LeanMarlTaskVsReconV1.olean; fi; echo "LeanMarlTaskVsReconV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlSupportV1.olean: LeanMarlSupportV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlSupportV1.olean.tmp LeanMarlSupportV1.lean > logs/LeanMarlSupportV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlSupportV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlSupportV1.olean.tmp .lake/build/lib/lean/LeanMarlSupportV1.olean; fi; echo "LeanMarlSupportV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean: LeanUnifiedObstructionOrderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean.tmp LeanUnifiedObstructionOrderV1.lean > logs/LeanUnifiedObstructionOrderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanUnifiedObstructionOrderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean.tmp .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean; fi; echo "LeanUnifiedObstructionOrderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBSafeOrderV1.olean: LeanPaperBSafeOrderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean.tmp LeanPaperBSafeOrderV1.lean > logs/LeanPaperBSafeOrderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBSafeOrderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean.tmp .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean; fi; echo "LeanPaperBSafeOrderV1 exit=$$rc"; exit $$rc

