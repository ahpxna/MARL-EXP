all: .lake/build/lib/lean/LeanMarlSafeEditV1.olean

.lake/build/lib/lean/LeanMarlSafeEditV1.olean: LeanMarlSafeEditV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlSafeEditV1.olean.tmp LeanMarlSafeEditV1.lean > logs/LeanMarlSafeEditV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlSafeEditV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlSafeEditV1.olean.tmp .lake/build/lib/lean/LeanMarlSafeEditV1.olean; fi; echo "LeanMarlSafeEditV1 exit=$$rc"; exit $$rc

