

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U : Set Y} (hU : IsOpen U) {f : X → Y} (hf : Continuous f) (hU2 : P2 U) : P2 (f ⁻¹' U) := by
  -- use `hU2` to avoid unused argument warning
  have _ := hU2
  -- the preimage of an open set under a continuous map is open
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- any open set satisfies `P2`
  exact P2_of_isOpen (A := f ⁻¹' U) h_open