module

public import PrimeBHT.TimeFrequency.X1.RealLine.Dilation
public import PrimeBHT.Frozen.BhtOpR

/-!
# The real-line kernel and operator of `Dilation.lean` are the frozen M2 definitions

`Dilation.lean` defines `bhtKernelR` and `bhtOpR` as mirrors of the candidate statement; ruling R15 froze the
approved definitions `PrimeBHT.Statements.bhtKernelR` and `PrimeBHT.Statements.bhtOpR`. The mirrors are
definitionally equal to the frozen ones (same bodies), so every lemma about the mirrors applies to the frozen
definitions. Only the frozen DEFINITION modules are imported (not the quarantined theorem `bht_real_smooth`).
-/

namespace PrimeBHT.TimeFrequency.RealLine

theorem bhtKernelR_eq_frozen : bhtKernelR = PrimeBHT.Statements.bhtKernelR := rfl

theorem bhtOpR_eq_frozen : bhtOpR = PrimeBHT.Statements.bhtOpR := rfl

end PrimeBHT.TimeFrequency.RealLine
