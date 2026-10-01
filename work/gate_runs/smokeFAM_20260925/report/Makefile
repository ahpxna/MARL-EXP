all: .lake/build/lib/lean/LeanPaperBFamilyDecoderV1.olean .lake/build/lib/lean/LeanPaperA6TwoSurrogatesV1.olean .lake/build/lib/lean/LeanPaperBFamilyLawV1.olean .lake/build/lib/lean/LeanPaperBParityDecoderV1.olean .lake/build/lib/lean/LeanPaperA6SurrogateAtV1.olean .lake/build/lib/lean/LeanPaperBFamilyChannelV1.olean .lake/build/lib/lean/LeanPaperBParityGapV1.olean .lake/build/lib/lean/LeanPaperBParityTestV1.olean .lake/build/lib/lean/LeanPaperBParityExperimentV1.olean .lake/build/lib/lean/LeanPaperA6OracleLearnerV1.olean .lake/build/lib/lean/LeanPaperACentredV1.olean .lake/build/lib/lean/LeanPaperBObstructionParityV1.olean .lake/build/lib/lean/LeanPaperBParityLawV1.olean .lake/build/lib/lean/LeanPaperBSchedTestV1.olean .lake/build/lib/lean/LeanPaperBParityChannelV1.olean .lake/build/lib/lean/LeanPaperBObstructionV1.olean .lake/build/lib/lean/LeanPaperBRateClosureV1.olean .lake/build/lib/lean/LeanPaperA6FixedDesignV1.olean .lake/build/lib/lean/LeanPaperARPairV1.olean .lake/build/lib/lean/LeanPaperBObstructionLawV1.olean .lake/build/lib/lean/LeanPaperBParityNormV1.olean .lake/build/lib/lean/LeanPaperBConcentrationV1.olean .lake/build/lib/lean/LeanPaperBScheduleV1.olean .lake/build/lib/lean/LeanPaperBParityChiSqV1.olean .lake/build/lib/lean/LeanPaperBProtocolV1.olean .lake/build/lib/lean/LeanPaperBEndgameV1.olean .lake/build/lib/lean/LeanPaperA7IdealRunV1.olean .lake/build/lib/lean/LeanPaperA7TailV1.olean .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean .lake/build/lib/lean/LeanPaperALowerKLV1.olean .lake/build/lib/lean/LeanPaperBParityV1.olean .lake/build/lib/lean/LeanPaperBPairRateV1.olean .lake/build/lib/lean/LeanPaperBChiSqV1.olean .lake/build/lib/lean/LeanPaperBKernelV1.olean .lake/build/lib/lean/LeanPaperBTipV1.olean .lake/build/lib/lean/LeanPaperBDecoderV1.olean .lake/build/lib/lean/LeanPaperA7IdealStopV1.olean .lake/build/lib/lean/LeanPaperA7WarmTrackV1.olean .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean .lake/build/lib/lean/LeanPaperBCubeV1.olean .lake/build/lib/lean/LeanPaperBAttainV1.olean .lake/build/lib/lean/LeanPaperBChannelPairV1.olean .lake/build/lib/lean/LeanSupportGeometryV4.olean .lake/build/lib/lean/LeanPaperA7IdealLearnerV1.olean .lake/build/lib/lean/LeanPaperA7GLRMeasV1.olean .lake/build/lib/lean/LeanPaperAStoppingV1.olean .lake/build/lib/lean/LeanPaperA7TrackingV1.olean .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean .lake/build/lib/lean/LeanPaperBRatesV1.olean .lake/build/lib/lean/LeanPaperBWorldsV1.olean .lake/build/lib/lean/LeanPaperA7NetOracleV1.olean .lake/build/lib/lean/LeanPaperA7DirectLowerV1.olean .lake/build/lib/lean/LeanPaperA7ProcessV1.olean .lake/build/lib/lean/LeanPaperA7CorrectV1.olean .lake/build/lib/lean/LeanUnifiedQueryOrderV1.olean .lake/build/lib/lean/LeanPaperBAttainmentV1.olean .lake/build/lib/lean/LeanPaperBRateKLV1.olean .lake/build/lib/lean/LeanPaperA7SqrtLipV1.olean .lake/build/lib/lean/LeanPaperA7FreeAccumV1.olean .lake/build/lib/lean/LeanPaperACertificatePerturbationV1.olean .lake/build/lib/lean/LeanPaperAStopJoinV1.olean .lake/build/lib/lean/LeanPaperA7StreamV1.olean .lake/build/lib/lean/LeanPaperBKLV1.olean .lake/build/lib/lean/LeanPaperAAdaptMartV1.olean .lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean .lake/build/lib/lean/LeanPaperAFreezeV1.olean .lake/build/lib/lean/LeanPaperAMartingaleV1.olean

.lake/build/lib/lean/LeanPaperBFamilyDecoderV1.olean: LeanPaperBFamilyDecoderV1.lean .lake/build/lib/lean/LeanPaperBFamilyLawV1.olean .lake/build/lib/lean/LeanPaperBParityDecoderV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBFamilyDecoderV1.olean.tmp LeanPaperBFamilyDecoderV1.lean > logs/LeanPaperBFamilyDecoderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBFamilyDecoderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBFamilyDecoderV1.olean.tmp .lake/build/lib/lean/LeanPaperBFamilyDecoderV1.olean; fi; echo "LeanPaperBFamilyDecoderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA6TwoSurrogatesV1.olean: LeanPaperA6TwoSurrogatesV1.lean .lake/build/lib/lean/LeanPaperA6SurrogateAtV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA6TwoSurrogatesV1.olean.tmp LeanPaperA6TwoSurrogatesV1.lean > logs/LeanPaperA6TwoSurrogatesV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA6TwoSurrogatesV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA6TwoSurrogatesV1.olean.tmp .lake/build/lib/lean/LeanPaperA6TwoSurrogatesV1.olean; fi; echo "LeanPaperA6TwoSurrogatesV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBFamilyLawV1.olean: LeanPaperBFamilyLawV1.lean .lake/build/lib/lean/LeanPaperBFamilyChannelV1.olean .lake/build/lib/lean/LeanPaperBParityGapV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBFamilyLawV1.olean.tmp LeanPaperBFamilyLawV1.lean > logs/LeanPaperBFamilyLawV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBFamilyLawV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBFamilyLawV1.olean.tmp .lake/build/lib/lean/LeanPaperBFamilyLawV1.olean; fi; echo "LeanPaperBFamilyLawV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityDecoderV1.olean: LeanPaperBParityDecoderV1.lean .lake/build/lib/lean/LeanPaperBParityTestV1.olean .lake/build/lib/lean/LeanPaperBParityExperimentV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityDecoderV1.olean.tmp LeanPaperBParityDecoderV1.lean > logs/LeanPaperBParityDecoderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityDecoderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityDecoderV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityDecoderV1.olean; fi; echo "LeanPaperBParityDecoderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA6SurrogateAtV1.olean: LeanPaperA6SurrogateAtV1.lean .lake/build/lib/lean/LeanPaperA6OracleLearnerV1.olean .lake/build/lib/lean/LeanPaperACentredV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA6SurrogateAtV1.olean.tmp LeanPaperA6SurrogateAtV1.lean > logs/LeanPaperA6SurrogateAtV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA6SurrogateAtV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA6SurrogateAtV1.olean.tmp .lake/build/lib/lean/LeanPaperA6SurrogateAtV1.olean; fi; echo "LeanPaperA6SurrogateAtV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBFamilyChannelV1.olean: LeanPaperBFamilyChannelV1.lean .lake/build/lib/lean/LeanPaperBObstructionParityV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBFamilyChannelV1.olean.tmp LeanPaperBFamilyChannelV1.lean > logs/LeanPaperBFamilyChannelV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBFamilyChannelV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBFamilyChannelV1.olean.tmp .lake/build/lib/lean/LeanPaperBFamilyChannelV1.olean; fi; echo "LeanPaperBFamilyChannelV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityGapV1.olean: LeanPaperBParityGapV1.lean .lake/build/lib/lean/LeanPaperBParityLawV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityGapV1.olean.tmp LeanPaperBParityGapV1.lean > logs/LeanPaperBParityGapV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityGapV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityGapV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityGapV1.olean; fi; echo "LeanPaperBParityGapV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityTestV1.olean: LeanPaperBParityTestV1.lean .lake/build/lib/lean/LeanPaperBSchedTestV1.olean .lake/build/lib/lean/LeanPaperBParityGapV1.olean .lake/build/lib/lean/LeanPaperBParityChannelV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityTestV1.olean.tmp LeanPaperBParityTestV1.lean > logs/LeanPaperBParityTestV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityTestV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityTestV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityTestV1.olean; fi; echo "LeanPaperBParityTestV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityExperimentV1.olean: LeanPaperBParityExperimentV1.lean .lake/build/lib/lean/LeanPaperBParityChannelV1.olean .lake/build/lib/lean/LeanPaperBObstructionV1.olean .lake/build/lib/lean/LeanPaperBRateClosureV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityExperimentV1.olean.tmp LeanPaperBParityExperimentV1.lean > logs/LeanPaperBParityExperimentV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityExperimentV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityExperimentV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityExperimentV1.olean; fi; echo "LeanPaperBParityExperimentV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA6OracleLearnerV1.olean: LeanPaperA6OracleLearnerV1.lean .lake/build/lib/lean/LeanPaperA6FixedDesignV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA6OracleLearnerV1.olean.tmp LeanPaperA6OracleLearnerV1.lean > logs/LeanPaperA6OracleLearnerV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA6OracleLearnerV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA6OracleLearnerV1.olean.tmp .lake/build/lib/lean/LeanPaperA6OracleLearnerV1.olean; fi; echo "LeanPaperA6OracleLearnerV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperACentredV1.olean: LeanPaperACentredV1.lean .lake/build/lib/lean/LeanPaperARPairV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperACentredV1.olean.tmp LeanPaperACentredV1.lean > logs/LeanPaperACentredV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperACentredV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperACentredV1.olean.tmp .lake/build/lib/lean/LeanPaperACentredV1.olean; fi; echo "LeanPaperACentredV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBObstructionParityV1.olean: LeanPaperBObstructionParityV1.lean .lake/build/lib/lean/LeanPaperBObstructionLawV1.olean .lake/build/lib/lean/LeanPaperBParityExperimentV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBObstructionParityV1.olean.tmp LeanPaperBObstructionParityV1.lean > logs/LeanPaperBObstructionParityV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBObstructionParityV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBObstructionParityV1.olean.tmp .lake/build/lib/lean/LeanPaperBObstructionParityV1.olean; fi; echo "LeanPaperBObstructionParityV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityLawV1.olean: LeanPaperBParityLawV1.lean .lake/build/lib/lean/LeanPaperBParityNormV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityLawV1.olean.tmp LeanPaperBParityLawV1.lean > logs/LeanPaperBParityLawV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityLawV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityLawV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityLawV1.olean; fi; echo "LeanPaperBParityLawV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBSchedTestV1.olean: LeanPaperBSchedTestV1.lean .lake/build/lib/lean/LeanPaperBConcentrationV1.olean .lake/build/lib/lean/LeanPaperBScheduleV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBSchedTestV1.olean.tmp LeanPaperBSchedTestV1.lean > logs/LeanPaperBSchedTestV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBSchedTestV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBSchedTestV1.olean.tmp .lake/build/lib/lean/LeanPaperBSchedTestV1.olean; fi; echo "LeanPaperBSchedTestV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityChannelV1.olean: LeanPaperBParityChannelV1.lean .lake/build/lib/lean/LeanPaperBParityChiSqV1.olean .lake/build/lib/lean/LeanPaperBProtocolV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityChannelV1.olean.tmp LeanPaperBParityChannelV1.lean > logs/LeanPaperBParityChannelV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityChannelV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityChannelV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityChannelV1.olean; fi; echo "LeanPaperBParityChannelV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBObstructionV1.olean: LeanPaperBObstructionV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBObstructionV1.olean.tmp LeanPaperBObstructionV1.lean > logs/LeanPaperBObstructionV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBObstructionV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBObstructionV1.olean.tmp .lake/build/lib/lean/LeanPaperBObstructionV1.olean; fi; echo "LeanPaperBObstructionV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBRateClosureV1.olean: LeanPaperBRateClosureV1.lean .lake/build/lib/lean/LeanPaperBEndgameV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBRateClosureV1.olean.tmp LeanPaperBRateClosureV1.lean > logs/LeanPaperBRateClosureV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBRateClosureV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBRateClosureV1.olean.tmp .lake/build/lib/lean/LeanPaperBRateClosureV1.olean; fi; echo "LeanPaperBRateClosureV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA6FixedDesignV1.olean: LeanPaperA6FixedDesignV1.lean .lake/build/lib/lean/LeanPaperA7IdealRunV1.olean .lake/build/lib/lean/LeanPaperA7TailV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA6FixedDesignV1.olean.tmp LeanPaperA6FixedDesignV1.lean > logs/LeanPaperA6FixedDesignV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA6FixedDesignV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA6FixedDesignV1.olean.tmp .lake/build/lib/lean/LeanPaperA6FixedDesignV1.olean; fi; echo "LeanPaperA6FixedDesignV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperARPairV1.olean: LeanPaperARPairV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperARPairV1.olean.tmp LeanPaperARPairV1.lean > logs/LeanPaperARPairV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperARPairV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperARPairV1.olean.tmp .lake/build/lib/lean/LeanPaperARPairV1.olean; fi; echo "LeanPaperARPairV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBObstructionLawV1.olean: LeanPaperBObstructionLawV1.lean .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean .lake/build/lib/lean/LeanPaperALowerKLV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBObstructionLawV1.olean.tmp LeanPaperBObstructionLawV1.lean > logs/LeanPaperBObstructionLawV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBObstructionLawV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBObstructionLawV1.olean.tmp .lake/build/lib/lean/LeanPaperBObstructionLawV1.olean; fi; echo "LeanPaperBObstructionLawV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityNormV1.olean: LeanPaperBParityNormV1.lean .lake/build/lib/lean/LeanPaperBParityV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityNormV1.olean.tmp LeanPaperBParityNormV1.lean > logs/LeanPaperBParityNormV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityNormV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityNormV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityNormV1.olean; fi; echo "LeanPaperBParityNormV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBConcentrationV1.olean: LeanPaperBConcentrationV1.lean .lake/build/lib/lean/LeanPaperBProtocolV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBConcentrationV1.olean.tmp LeanPaperBConcentrationV1.lean > logs/LeanPaperBConcentrationV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBConcentrationV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBConcentrationV1.olean.tmp .lake/build/lib/lean/LeanPaperBConcentrationV1.olean; fi; echo "LeanPaperBConcentrationV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBScheduleV1.olean: LeanPaperBScheduleV1.lean .lake/build/lib/lean/LeanPaperBProtocolV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBScheduleV1.olean.tmp LeanPaperBScheduleV1.lean > logs/LeanPaperBScheduleV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBScheduleV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBScheduleV1.olean.tmp .lake/build/lib/lean/LeanPaperBScheduleV1.olean; fi; echo "LeanPaperBScheduleV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityChiSqV1.olean: LeanPaperBParityChiSqV1.lean .lake/build/lib/lean/LeanPaperBParityLawV1.olean .lake/build/lib/lean/LeanPaperBPairRateV1.olean .lake/build/lib/lean/LeanPaperBChiSqV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityChiSqV1.olean.tmp LeanPaperBParityChiSqV1.lean > logs/LeanPaperBParityChiSqV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityChiSqV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityChiSqV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityChiSqV1.olean; fi; echo "LeanPaperBParityChiSqV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBProtocolV1.olean: LeanPaperBProtocolV1.lean .lake/build/lib/lean/LeanPaperBKernelV1.olean .lake/build/lib/lean/LeanPaperBChiSqV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBProtocolV1.olean.tmp LeanPaperBProtocolV1.lean > logs/LeanPaperBProtocolV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBProtocolV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBProtocolV1.olean.tmp .lake/build/lib/lean/LeanPaperBProtocolV1.olean; fi; echo "LeanPaperBProtocolV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBEndgameV1.olean: LeanPaperBEndgameV1.lean .lake/build/lib/lean/LeanPaperBKernelV1.olean .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean .lake/build/lib/lean/LeanPaperBTipV1.olean .lake/build/lib/lean/LeanPaperBDecoderV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBEndgameV1.olean.tmp LeanPaperBEndgameV1.lean > logs/LeanPaperBEndgameV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBEndgameV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBEndgameV1.olean.tmp .lake/build/lib/lean/LeanPaperBEndgameV1.olean; fi; echo "LeanPaperBEndgameV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7IdealRunV1.olean: LeanPaperA7IdealRunV1.lean .lake/build/lib/lean/LeanPaperA7IdealStopV1.olean .lake/build/lib/lean/LeanPaperA7WarmTrackV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7IdealRunV1.olean.tmp LeanPaperA7IdealRunV1.lean > logs/LeanPaperA7IdealRunV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7IdealRunV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7IdealRunV1.olean.tmp .lake/build/lib/lean/LeanPaperA7IdealRunV1.olean; fi; echo "LeanPaperA7IdealRunV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7TailV1.olean: LeanPaperA7TailV1.lean .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7TailV1.olean.tmp LeanPaperA7TailV1.lean > logs/LeanPaperA7TailV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7TailV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7TailV1.olean.tmp .lake/build/lib/lean/LeanPaperA7TailV1.olean; fi; echo "LeanPaperA7TailV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBSafeOrderV1.olean: LeanPaperBSafeOrderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean.tmp LeanPaperBSafeOrderV1.lean > logs/LeanPaperBSafeOrderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBSafeOrderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean.tmp .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean; fi; echo "LeanPaperBSafeOrderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperALowerKLV1.olean: LeanPaperALowerKLV1.lean .lake/build/lib/lean/LeanPaperBConcentrationV1.olean .lake/build/lib/lean/LeanPaperBObstructionV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperALowerKLV1.olean.tmp LeanPaperALowerKLV1.lean > logs/LeanPaperALowerKLV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperALowerKLV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperALowerKLV1.olean.tmp .lake/build/lib/lean/LeanPaperALowerKLV1.olean; fi; echo "LeanPaperALowerKLV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBParityV1.olean: LeanPaperBParityV1.lean .lake/build/lib/lean/LeanPaperBCubeV1.olean .lake/build/lib/lean/LeanPaperBAttainV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBParityV1.olean.tmp LeanPaperBParityV1.lean > logs/LeanPaperBParityV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBParityV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBParityV1.olean.tmp .lake/build/lib/lean/LeanPaperBParityV1.olean; fi; echo "LeanPaperBParityV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBPairRateV1.olean: LeanPaperBPairRateV1.lean .lake/build/lib/lean/LeanPaperBChannelPairV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBPairRateV1.olean.tmp LeanPaperBPairRateV1.lean > logs/LeanPaperBPairRateV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBPairRateV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBPairRateV1.olean.tmp .lake/build/lib/lean/LeanPaperBPairRateV1.olean; fi; echo "LeanPaperBPairRateV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBChiSqV1.olean: LeanPaperBChiSqV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBChiSqV1.olean.tmp LeanPaperBChiSqV1.lean > logs/LeanPaperBChiSqV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBChiSqV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBChiSqV1.olean.tmp .lake/build/lib/lean/LeanPaperBChiSqV1.olean; fi; echo "LeanPaperBChiSqV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBKernelV1.olean: LeanPaperBKernelV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBKernelV1.olean.tmp LeanPaperBKernelV1.lean > logs/LeanPaperBKernelV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBKernelV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBKernelV1.olean.tmp .lake/build/lib/lean/LeanPaperBKernelV1.olean; fi; echo "LeanPaperBKernelV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBTipV1.olean: LeanPaperBTipV1.lean .lake/build/lib/lean/LeanSupportGeometryV4.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBTipV1.olean.tmp LeanPaperBTipV1.lean > logs/LeanPaperBTipV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBTipV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBTipV1.olean.tmp .lake/build/lib/lean/LeanPaperBTipV1.olean; fi; echo "LeanPaperBTipV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBDecoderV1.olean: LeanPaperBDecoderV1.lean .lake/build/lib/lean/LeanPaperBSafeOrderV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBDecoderV1.olean.tmp LeanPaperBDecoderV1.lean > logs/LeanPaperBDecoderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBDecoderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBDecoderV1.olean.tmp .lake/build/lib/lean/LeanPaperBDecoderV1.olean; fi; echo "LeanPaperBDecoderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7IdealStopV1.olean: LeanPaperA7IdealStopV1.lean .lake/build/lib/lean/LeanPaperA7IdealLearnerV1.olean .lake/build/lib/lean/LeanPaperA7GLRMeasV1.olean .lake/build/lib/lean/LeanPaperAStoppingV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7IdealStopV1.olean.tmp LeanPaperA7IdealStopV1.lean > logs/LeanPaperA7IdealStopV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7IdealStopV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7IdealStopV1.olean.tmp .lake/build/lib/lean/LeanPaperA7IdealStopV1.olean; fi; echo "LeanPaperA7IdealStopV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7WarmTrackV1.olean: LeanPaperA7WarmTrackV1.lean .lake/build/lib/lean/LeanPaperA7TrackingV1.olean .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7WarmTrackV1.olean.tmp LeanPaperA7WarmTrackV1.lean > logs/LeanPaperA7WarmTrackV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7WarmTrackV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7WarmTrackV1.olean.tmp .lake/build/lib/lean/LeanPaperA7WarmTrackV1.olean; fi; echo "LeanPaperA7WarmTrackV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean: LeanPaperA7OracleSelectV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean.tmp LeanPaperA7OracleSelectV1.lean > logs/LeanPaperA7OracleSelectV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7OracleSelectV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean.tmp .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean; fi; echo "LeanPaperA7OracleSelectV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBCubeV1.olean: LeanPaperBCubeV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBCubeV1.olean.tmp LeanPaperBCubeV1.lean > logs/LeanPaperBCubeV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBCubeV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBCubeV1.olean.tmp .lake/build/lib/lean/LeanPaperBCubeV1.olean; fi; echo "LeanPaperBCubeV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBAttainV1.olean: LeanPaperBAttainV1.lean .lake/build/lib/lean/LeanPaperBCubeV1.olean .lake/build/lib/lean/LeanPaperBRatesV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBAttainV1.olean.tmp LeanPaperBAttainV1.lean > logs/LeanPaperBAttainV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBAttainV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBAttainV1.olean.tmp .lake/build/lib/lean/LeanPaperBAttainV1.olean; fi; echo "LeanPaperBAttainV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBChannelPairV1.olean: LeanPaperBChannelPairV1.lean .lake/build/lib/lean/LeanPaperBWorldsV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBChannelPairV1.olean.tmp LeanPaperBChannelPairV1.lean > logs/LeanPaperBChannelPairV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBChannelPairV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBChannelPairV1.olean.tmp .lake/build/lib/lean/LeanPaperBChannelPairV1.olean; fi; echo "LeanPaperBChannelPairV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanSupportGeometryV4.olean: LeanSupportGeometryV4.lean
	@lake env lean -o .lake/build/lib/lean/LeanSupportGeometryV4.olean.tmp LeanSupportGeometryV4.lean > logs/LeanSupportGeometryV4.log 2>&1; rc=$$?; echo $$rc > logs/LeanSupportGeometryV4.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanSupportGeometryV4.olean.tmp .lake/build/lib/lean/LeanSupportGeometryV4.olean; fi; echo "LeanSupportGeometryV4 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7IdealLearnerV1.olean: LeanPaperA7IdealLearnerV1.lean .lake/build/lib/lean/LeanPaperA7NetOracleV1.olean .lake/build/lib/lean/LeanPaperA7DirectLowerV1.olean .lake/build/lib/lean/LeanPaperA7ProcessV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7IdealLearnerV1.olean.tmp LeanPaperA7IdealLearnerV1.lean > logs/LeanPaperA7IdealLearnerV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7IdealLearnerV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7IdealLearnerV1.olean.tmp .lake/build/lib/lean/LeanPaperA7IdealLearnerV1.olean; fi; echo "LeanPaperA7IdealLearnerV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7GLRMeasV1.olean: LeanPaperA7GLRMeasV1.lean .lake/build/lib/lean/LeanPaperA7CorrectV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7GLRMeasV1.olean.tmp LeanPaperA7GLRMeasV1.lean > logs/LeanPaperA7GLRMeasV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7GLRMeasV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7GLRMeasV1.olean.tmp .lake/build/lib/lean/LeanPaperA7GLRMeasV1.olean; fi; echo "LeanPaperA7GLRMeasV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperAStoppingV1.olean: LeanPaperAStoppingV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperAStoppingV1.olean.tmp LeanPaperAStoppingV1.lean > logs/LeanPaperAStoppingV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperAStoppingV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperAStoppingV1.olean.tmp .lake/build/lib/lean/LeanPaperAStoppingV1.olean; fi; echo "LeanPaperAStoppingV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7TrackingV1.olean: LeanPaperA7TrackingV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7TrackingV1.olean.tmp LeanPaperA7TrackingV1.lean > logs/LeanPaperA7TrackingV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7TrackingV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7TrackingV1.olean.tmp .lake/build/lib/lean/LeanPaperA7TrackingV1.olean; fi; echo "LeanPaperA7TrackingV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7AccumulationV1.olean: LeanPaperA7AccumulationV1.lean .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean.tmp LeanPaperA7AccumulationV1.lean > logs/LeanPaperA7AccumulationV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7AccumulationV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean.tmp .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean; fi; echo "LeanPaperA7AccumulationV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBRatesV1.olean: LeanPaperBRatesV1.lean .lake/build/lib/lean/LeanUnifiedQueryOrderV1.olean .lake/build/lib/lean/LeanPaperBAttainmentV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBRatesV1.olean.tmp LeanPaperBRatesV1.lean > logs/LeanPaperBRatesV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBRatesV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBRatesV1.olean.tmp .lake/build/lib/lean/LeanPaperBRatesV1.olean; fi; echo "LeanPaperBRatesV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBWorldsV1.olean: LeanPaperBWorldsV1.lean .lake/build/lib/lean/LeanPaperBRateKLV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBWorldsV1.olean.tmp LeanPaperBWorldsV1.lean > logs/LeanPaperBWorldsV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBWorldsV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBWorldsV1.olean.tmp .lake/build/lib/lean/LeanPaperBWorldsV1.olean; fi; echo "LeanPaperBWorldsV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7NetOracleV1.olean: LeanPaperA7NetOracleV1.lean .lake/build/lib/lean/LeanPaperA7SqrtLipV1.olean .lake/build/lib/lean/LeanPaperA7FreeAccumV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7NetOracleV1.olean.tmp LeanPaperA7NetOracleV1.lean > logs/LeanPaperA7NetOracleV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7NetOracleV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7NetOracleV1.olean.tmp .lake/build/lib/lean/LeanPaperA7NetOracleV1.olean; fi; echo "LeanPaperA7NetOracleV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7DirectLowerV1.olean: LeanPaperA7DirectLowerV1.lean .lake/build/lib/lean/LeanPaperACertificatePerturbationV1.olean .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7DirectLowerV1.olean.tmp LeanPaperA7DirectLowerV1.lean > logs/LeanPaperA7DirectLowerV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7DirectLowerV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7DirectLowerV1.olean.tmp .lake/build/lib/lean/LeanPaperA7DirectLowerV1.olean; fi; echo "LeanPaperA7DirectLowerV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7ProcessV1.olean: LeanPaperA7ProcessV1.lean .lake/build/lib/lean/LeanPaperAStopJoinV1.olean .lake/build/lib/lean/LeanPaperA7StreamV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7ProcessV1.olean.tmp LeanPaperA7ProcessV1.lean > logs/LeanPaperA7ProcessV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7ProcessV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7ProcessV1.olean.tmp .lake/build/lib/lean/LeanPaperA7ProcessV1.olean; fi; echo "LeanPaperA7ProcessV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7CorrectV1.olean: LeanPaperA7CorrectV1.lean .lake/build/lib/lean/LeanPaperA7ProcessV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7CorrectV1.olean.tmp LeanPaperA7CorrectV1.lean > logs/LeanPaperA7CorrectV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7CorrectV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7CorrectV1.olean.tmp .lake/build/lib/lean/LeanPaperA7CorrectV1.olean; fi; echo "LeanPaperA7CorrectV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanUnifiedQueryOrderV1.olean: LeanUnifiedQueryOrderV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanUnifiedQueryOrderV1.olean.tmp LeanUnifiedQueryOrderV1.lean > logs/LeanUnifiedQueryOrderV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanUnifiedQueryOrderV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanUnifiedQueryOrderV1.olean.tmp .lake/build/lib/lean/LeanUnifiedQueryOrderV1.olean; fi; echo "LeanUnifiedQueryOrderV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBAttainmentV1.olean: LeanPaperBAttainmentV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBAttainmentV1.olean.tmp LeanPaperBAttainmentV1.lean > logs/LeanPaperBAttainmentV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBAttainmentV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBAttainmentV1.olean.tmp .lake/build/lib/lean/LeanPaperBAttainmentV1.olean; fi; echo "LeanPaperBAttainmentV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBRateKLV1.olean: LeanPaperBRateKLV1.lean .lake/build/lib/lean/LeanPaperBRatesV1.olean .lake/build/lib/lean/LeanPaperBKLV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBRateKLV1.olean.tmp LeanPaperBRateKLV1.lean > logs/LeanPaperBRateKLV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBRateKLV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBRateKLV1.olean.tmp .lake/build/lib/lean/LeanPaperBRateKLV1.olean; fi; echo "LeanPaperBRateKLV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7SqrtLipV1.olean: LeanPaperA7SqrtLipV1.lean .lake/build/lib/lean/LeanPaperA7OracleSelectV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7SqrtLipV1.olean.tmp LeanPaperA7SqrtLipV1.lean > logs/LeanPaperA7SqrtLipV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7SqrtLipV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7SqrtLipV1.olean.tmp .lake/build/lib/lean/LeanPaperA7SqrtLipV1.olean; fi; echo "LeanPaperA7SqrtLipV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7FreeAccumV1.olean: LeanPaperA7FreeAccumV1.lean .lake/build/lib/lean/LeanPaperA7AccumulationV1.olean .lake/build/lib/lean/LeanPaperA7TrackingV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7FreeAccumV1.olean.tmp LeanPaperA7FreeAccumV1.lean > logs/LeanPaperA7FreeAccumV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7FreeAccumV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7FreeAccumV1.olean.tmp .lake/build/lib/lean/LeanPaperA7FreeAccumV1.olean; fi; echo "LeanPaperA7FreeAccumV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperACertificatePerturbationV1.olean: LeanPaperACertificatePerturbationV1.lean .lake/build/lib/lean/LeanPaperA7StreamV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperACertificatePerturbationV1.olean.tmp LeanPaperACertificatePerturbationV1.lean > logs/LeanPaperACertificatePerturbationV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperACertificatePerturbationV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperACertificatePerturbationV1.olean.tmp .lake/build/lib/lean/LeanPaperACertificatePerturbationV1.olean; fi; echo "LeanPaperACertificatePerturbationV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperAStopJoinV1.olean: LeanPaperAStopJoinV1.lean .lake/build/lib/lean/LeanPaperAAdaptMartV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperAStopJoinV1.olean.tmp LeanPaperAStopJoinV1.lean > logs/LeanPaperAStopJoinV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperAStopJoinV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperAStopJoinV1.olean.tmp .lake/build/lib/lean/LeanPaperAStopJoinV1.olean; fi; echo "LeanPaperAStopJoinV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7StreamV1.olean: LeanPaperA7StreamV1.lean .lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7StreamV1.olean.tmp LeanPaperA7StreamV1.lean > logs/LeanPaperA7StreamV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7StreamV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7StreamV1.olean.tmp .lake/build/lib/lean/LeanPaperA7StreamV1.olean; fi; echo "LeanPaperA7StreamV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperBKLV1.olean: LeanPaperBKLV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperBKLV1.olean.tmp LeanPaperBKLV1.lean > logs/LeanPaperBKLV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperBKLV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperBKLV1.olean.tmp .lake/build/lib/lean/LeanPaperBKLV1.olean; fi; echo "LeanPaperBKLV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperAAdaptMartV1.olean: LeanPaperAAdaptMartV1.lean .lake/build/lib/lean/LeanPaperAFreezeV1.olean .lake/build/lib/lean/LeanPaperAMartingaleV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperAAdaptMartV1.olean.tmp LeanPaperAAdaptMartV1.lean > logs/LeanPaperAAdaptMartV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperAAdaptMartV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperAAdaptMartV1.olean.tmp .lake/build/lib/lean/LeanPaperAAdaptMartV1.olean; fi; echo "LeanPaperAAdaptMartV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean: LeanPaperA7ConfidenceV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean.tmp LeanPaperA7ConfidenceV1.lean > logs/LeanPaperA7ConfidenceV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperA7ConfidenceV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean.tmp .lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean; fi; echo "LeanPaperA7ConfidenceV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperAFreezeV1.olean: LeanPaperAFreezeV1.lean
	@lake env lean -o .lake/build/lib/lean/LeanPaperAFreezeV1.olean.tmp LeanPaperAFreezeV1.lean > logs/LeanPaperAFreezeV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperAFreezeV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperAFreezeV1.olean.tmp .lake/build/lib/lean/LeanPaperAFreezeV1.olean; fi; echo "LeanPaperAFreezeV1 exit=$$rc"; exit $$rc

.lake/build/lib/lean/LeanPaperAMartingaleV1.olean: LeanPaperAMartingaleV1.lean .lake/build/lib/lean/LeanPaperA7ConfidenceV1.olean
	@lake env lean -o .lake/build/lib/lean/LeanPaperAMartingaleV1.olean.tmp LeanPaperAMartingaleV1.lean > logs/LeanPaperAMartingaleV1.log 2>&1; rc=$$?; echo $$rc > logs/LeanPaperAMartingaleV1.exit; if [ $$rc -eq 0 ]; then mv .lake/build/lib/lean/LeanPaperAMartingaleV1.olean.tmp .lake/build/lib/lean/LeanPaperAMartingaleV1.olean; fi; echo "LeanPaperAMartingaleV1 exit=$$rc"; exit $$rc

