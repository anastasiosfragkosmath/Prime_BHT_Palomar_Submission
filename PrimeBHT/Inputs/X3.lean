module

public import PrimeBHT.ErrorTerms
public import PrimeCarleson.Frozen.VonMangoldtSubHeathBrownU3

/-!
# X3 from the earlier project (ruling R12)

`PrimeBHT.ErrorTerms.X3Statement` is the type of the sealed theorem
`PrimeCarleson.vonMangoldt_sub_heathBrown_U3` of the author's formalization of
*A Variation Norm Carleson Theorem Along the Primes*, whose import closure is included in
`PrimeCarleson/` and `vendor/` (copied unchanged from a pinned revision; see `lakefile.toml`).
-/

@[expose] public section

namespace PrimeBHT.Inputs

/-- X3, discharged by the sealed theorem of the earlier project. -/
theorem x3_of_lf : PrimeBHT.ErrorTerms.X3Statement :=
  PrimeCarleson.vonMangoldt_sub_heathBrown_U3

end PrimeBHT.Inputs
