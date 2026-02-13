

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U : Set Y} (hU : IsOpen U) {f : X → Y} (hf : Continuous f) (hU3 : P3 U) : P3 (f ⁻¹' U) := by
  -- use `hU3` to avoid an unused-argument warning
  have _ := hU3
  -- the preimage of an open set under a continuous map is open
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- any open set satisfies `P3`
  exact P3_of_isOpen (A := f ⁻¹' U) h_open