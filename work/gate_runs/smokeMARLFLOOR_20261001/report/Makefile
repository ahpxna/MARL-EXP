all: .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean .lake/build/lib/lean/LeanMarlReceiverFloorV2.olean .lake/build/lib/lean/LeanMarlPrefixInstanceV1.olean .lake/build/lib/lean/LeanMarlImitationGapV1.olean

.lake/build/lib/lean/LeanMarlReceiverFloorV1.olean: LeanMarlReceiverFloorV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean.tmp LeanMarlReceiverFloorV1.lean > logs/LeanMarlReceiverFloorV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlReceiverFloorV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean.tmp .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean; fi; echo "LeanMarlReceiverFloorV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlReceiverFloorV2.olean: LeanMarlReceiverFloorV2.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlReceiverFloorV2.olean.tmp LeanMarlReceiverFloorV2.lean > logs/LeanMarlReceiverFloorV2.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlReceiverFloorV2.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlReceiverFloorV2.olean.tmp .lake/build/lib/lean/LeanMarlReceiverFloorV2.olean; fi; echo "LeanMarlReceiverFloorV2 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlPrefixInstanceV1.olean: LeanMarlPrefixInstanceV1.lean .lake/build/lib/lean/LeanMarlReceiverFloorV2.olean
	@lake env lean -o .lake/build/lib/lean/LeanMarlPrefixInstanceV1.olean.tmp LeanMarlPrefixInstanceV1.lean > logs/LeanMarlPrefixInstanceV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlPrefixInstanceV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlPrefixInstanceV1.olean.tmp .lake/build/lib/lean/LeanMarlPrefixInstanceV1.olean; fi; echo "LeanMarlPrefixInstanceV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlImitationGapV1.olean: LeanMarlImitationGapV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlImitationGapV1.olean.tmp LeanMarlImitationGapV1.lean > logs/LeanMarlImitationGapV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlImitationGapV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlImitationGapV1.olean.tmp .lake/build/lib/lean/LeanMarlImitationGapV1.olean; fi; echo "LeanMarlImitationGapV1 exit=$$rc"; exit $$rc

