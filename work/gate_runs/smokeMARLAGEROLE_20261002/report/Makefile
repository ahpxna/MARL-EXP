all: .lake/build/lib/lean/LeanMarlAgeRoleV1.olean

.lake/build/lib/lean/LeanMarlAgeRoleV1.olean: LeanMarlAgeRoleV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlAgeRoleV1.olean.tmp LeanMarlAgeRoleV1.lean > logs/LeanMarlAgeRoleV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlAgeRoleV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlAgeRoleV1.olean.tmp .lake/build/lib/lean/LeanMarlAgeRoleV1.olean; fi; echo "LeanMarlAgeRoleV1 exit=$$rc"; exit $$rc

