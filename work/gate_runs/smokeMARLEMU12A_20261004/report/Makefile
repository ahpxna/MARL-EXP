all: .lake/build/lib/lean/LeanMarlPacketEmulatorV1.olean

.lake/build/lib/lean/LeanMarlPacketEmulatorV1.olean: LeanMarlPacketEmulatorV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanMarlPacketEmulatorV1.olean.tmp LeanMarlPacketEmulatorV1.lean > logs/LeanMarlPacketEmulatorV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanMarlPacketEmulatorV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanMarlPacketEmulatorV1.olean.tmp .lake/build/lib/lean/LeanMarlPacketEmulatorV1.olean; fi; echo "LeanMarlPacketEmulatorV1 exit=$$rc"; exit $$rc

