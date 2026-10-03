all: .lake/build/lib/lean/LeanMarlMismatchW1V1.olean

.lake/build/lib/lean/LeanMarlMismatchW1V1.olean: LeanMarlMismatchW1V1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlMismatchW1V1.olean.tmp LeanMarlMismatchW1V1.lean > logs/LeanMarlMismatchW1V1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlMismatchW1V1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlMismatchW1V1.olean.tmp .lake/build/lib/lean/LeanMarlMismatchW1V1.olean; fi; echo "LeanMarlMismatchW1V1 exit=$$rc"; exit $$rc

