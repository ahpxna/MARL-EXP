all: .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean .lake/build/lib/lean/LeanUnifiedStructuralRelaxedV1.olean

.lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean: LeanUnifiedObstructionOrderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean.tmp LeanUnifiedObstructionOrderV1.lean > logs/LeanUnifiedObstructionOrderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanUnifiedObstructionOrderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean.tmp .lake/build/lib/lean/LeanUnifiedObstructionOrderV1.olean; fi; echo "LeanUnifiedObstructionOrderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanUnifiedStructuralRelaxedV1.olean: LeanUnifiedStructuralRelaxedV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanUnifiedStructuralRelaxedV1.olean.tmp LeanUnifiedStructuralRelaxedV1.lean > logs/LeanUnifiedStructuralRelaxedV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanUnifiedStructuralRelaxedV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanUnifiedStructuralRelaxedV1.olean.tmp .lake/build/lib/lean/LeanUnifiedStructuralRelaxedV1.olean; fi; echo "LeanUnifiedStructuralRelaxedV1 exit=$$rc"; exit $$rc

