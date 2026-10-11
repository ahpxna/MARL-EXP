all: .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean

.lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean: LeanMarlLegacyViewDecoderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean.tmp LeanMarlLegacyViewDecoderV1.lean > logs/LeanMarlLegacyViewDecoderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlLegacyViewDecoderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean.tmp .lake/build/lib/lean/LeanMarlLegacyViewDecoderV1.olean; fi; echo "LeanMarlLegacyViewDecoderV1 exit=$$rc"; exit $$rc

