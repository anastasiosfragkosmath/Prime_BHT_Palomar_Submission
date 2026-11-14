module

import PrimeCarleson.Frozen.GowersNormInterval

/-!
# Vendor smoke test

The library `PrimeCarleson` (the included closure of the author's formalization of
*A Variation Norm Carleson Theorem Along the Primes*, see `lakefile.toml`) is visible to `PrimeBHT`
modules, and the frozen `U^s([N])` norm is the one of that project.
-/

#check PrimeCarleson.gowersNormInterval
