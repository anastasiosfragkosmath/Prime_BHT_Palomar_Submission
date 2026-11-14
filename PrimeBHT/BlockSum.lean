module

public import PrimeBHT.BlockSum.Basic
public import PrimeBHT.BlockSum.Sum
public import PrimeBHT.BlockSum.Key0

/-!
# Block sum (blueprint N43) and the assembly of `p:key0` (N26), conditional on `BlockTransferBound`

* `PrimeBHT.BlockSum.Basic`: definitions (`aQ`, `NQ`, `KQ`, `hOp`, `uOp`), the hypothesis
  `BlockTransferBound`, N43(b) `exists_blockPartition_sqfree`, algebra of `bilin`, norm bridges.
* `PrimeBHT.BlockSum.Sum`: N43(c) `blockSum_bound_of_blockTransfer`.
* `PrimeBHT.BlockSum.Key0`: `exists_scale_le`, `key0_of_blockTransfer`, `p_key0_of_blockTransfer`.
-/
