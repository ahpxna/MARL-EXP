all: .lake/build/lib/lean/LeanMarlNetFloorV1.olean .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean

.lake/build/lib/lean/LeanMarlNetFloorV1.olean: LeanMarlNetFloorV1.lean .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanMarlNetFloorV1.olean.tmp LeanMarlNetFloorV1.lean > logs/LeanMarlNetFloorV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlNetFloorV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlNetFloorV1.olean.tmp .lake/build/lib/lean/LeanMarlNetFloorV1.olean; fi; echo "LeanMarlNetFloorV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanMarlReceiverFloorV1.olean: LeanMarlReceiverFloorV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean.tmp LeanMarlReceiverFloorV1.lean > logs/LeanMarlReceiverFloorV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlReceiverFloorV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean.tmp .lake/build/lib/lean/LeanMarlReceiverFloorV1.olean; fi; echo "LeanMarlReceiverFloorV1 exit=$$rc"; exit $$rc

