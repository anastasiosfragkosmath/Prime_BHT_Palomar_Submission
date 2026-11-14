module



public import PrimeBHT.Smoke
public import PrimeBHT.VendorSmoke
public import PrimeBHT.Exponents
public import PrimeBHT.FixedAverage
public import PrimeBHT.Kernel
public import PrimeBHT.KernelFourier.Uniform
public import PrimeBHT.Lift
public import PrimeBHT.Interpolation
public import PrimeBHT.U3MaxMod
public import PrimeBHT.Periodic
public import PrimeBHT.PeriodicBlock
public import PrimeBHT.PeriodicAssembly
public import PrimeBHT.Decomposition
public import PrimeBHT.SingleScale
public import PrimeBHT.SingleScaleL1
public import PrimeBHT.ErrorTerms
public import PrimeBHT.Progression
public import PrimeBHT.FinalAssembly
public import PrimeBHT.GroupDecay
public import PrimeBHT.FinalGlue
public import PrimeBHT.FinalSum
public import PrimeBHT.Transference
public import PrimeBHT.TransferenceAssembly.Anchor
public import PrimeBHT.TransferenceAssembly.TwistedForm
public import PrimeBHT.TransferenceAssembly.Chart
public import PrimeBHT.TransferenceAssembly.ChartExpansion
public import PrimeBHT.TransferenceAssembly.ExactChart
public import PrimeBHT.TransferenceAssembly.X2
public import PrimeBHT.TransferenceAssembly.ChartLift
public import PrimeBHT.TransferenceAssembly.ChartLiftBounds
public import PrimeBHT.TransferenceAssembly.FinalBound
public import PrimeBHT.TransferenceAssembly.ChartCover
public import PrimeBHT.TransferenceAssembly.Duality
public import PrimeBHT.TransferenceAssembly.KernelData
public import PrimeBHT.TransferenceAssembly.BlockTransfer
public import PrimeBHT.TransferenceAssembly.Key0OfX2
public import PrimeBHT.Interface.X1Checks
public import PrimeBHT.Interface.X1Statement
public import PrimeBHT.Interface.X2Checks
public import PrimeBHT.TimeFrequency.X1.RealLine.Dilation
public import PrimeBHT.TimeFrequency.X1.RealLine.KernelDecomposition
public import PrimeBHT.TimeFrequency.X1.RealLine.FrozenLink
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley
public import PrimeBHT.TimeFrequency.X1.RealLine.Frame
public import PrimeBHT.TimeFrequency.X1.RealLine.Coefficients
public import PrimeBHT.TimeFrequency.X1.FromM1
public import PrimeBHT.TimeFrequency.X1.RealLine.Theta
public import PrimeBHT.TimeFrequency.X1.RealLine.ModelSum
public import PrimeBHT.TimeFrequency.X1.Transfer.Kernel
public import PrimeBHT.TimeFrequency.X1.Transfer.Embed
public import PrimeBHT.TimeFrequency.X1.Transfer.Perturb
public import PrimeBHT.TimeFrequency.X1.Transfer.Assemble
public import PrimeBHT.TimeFrequency.Interp.Discrete
public import PrimeBHT.TimeFrequency.Interp.Duality
public import PrimeBHT.TimeFrequency.Interp.Strong
public import PrimeBHT.TimeFrequency.Interp.Restricted.Form
public import PrimeBHT.TimeFrequency.Interp.Restricted.Interpolate
public import PrimeBHT.TimeFrequency.Interp.Restricted.Operator
public import PrimeBHT.TimeFrequency.Interp.Hull
public import PrimeBHT.BlockSum
public import PrimeBHT.MainBanach
public import PrimeBHT.MainConditional
public import PrimeBHT.Bridge.Key0
public import PrimeBHT.MainQuasiBanach

/-!
# PrimeBHT: Lean formalization of "The Bilinear Hilbert Transform Along the Primes"

Root module: imports every verified, sorry-free project module. The frozen main theorem
(`PrimeBHT.Frozen.MainTheorem`), the frozen `p:key0`, X1 and X2 (`PrimeBHT.Frozen.{Key0,X1,FiniteBV}`; all frozen anchors are
now SEALED, 2026-11-10) and their providers (`PrimeBHT.Proof.*`) are deliberately NOT imported here (import quarantine of the
frozen-anchor layer). The sealed main theorem is `PrimeBHT.Frozen.MainTheorem`. See `docs/STATUS.md`.
-/
