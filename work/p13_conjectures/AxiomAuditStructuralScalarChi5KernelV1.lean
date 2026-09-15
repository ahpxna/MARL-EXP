import «LeanStructuralScalarChi5KernelV1»

/-!
Audit of the kernel replacement for the ten `native_decide` steps.  Each name
must report exactly `[propext, Classical.choice, Quot.sound]`.  If any reports
`Lean.ofReduceBool`, the promotion failed and the χ≥5 witness remains a
compiled artifact.
-/

open CIGAMF.P13.StructuralScalarChi5Kernel

#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.opt1_abs_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.opt2_abs_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.opt3_abs_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.opt4_abs_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.opt5_abs_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.unique_abs1_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.unique_abs2_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.unique_abs3_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.unique_abs4_kernel
#print axioms CIGAMF.P13.StructuralScalarChi5Kernel.unique_abs5_kernel
