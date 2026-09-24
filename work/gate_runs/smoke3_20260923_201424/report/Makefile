all: .lake/build/lib/lean/LeanPaperBTipV1.olean .lake/build/lib/lean/LeanSupportGeometryV4.olean

.lake/build/lib/lean/LeanPaperBTipV1.olean: LeanPaperBTipV1.lean .lake/build/lib/lean/LeanSupportGeometryV4.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBTipV1.olean.tmp LeanPaperBTipV1.lean > logs/LeanPaperBTipV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBTipV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBTipV1.olean.tmp .lake/build/lib/lean/LeanPaperBTipV1.olean; fi; echo "LeanPaperBTipV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanSupportGeometryV4.olean: LeanSupportGeometryV4.lean
	@lake env lean -o .lake/build/lib/lean/LeanSupportGeometryV4.olean.tmp LeanSupportGeometryV4.lean > logs/LeanSupportGeometryV4.log 2>&1; rc=$$?; echo $$rc > logs/LeanSupportGeometryV4.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanSupportGeometryV4.olean.tmp .lake/build/lib/lean/LeanSupportGeometryV4.olean; fi; echo "LeanSupportGeometryV4 exit=$$rc"; exit $$rc

