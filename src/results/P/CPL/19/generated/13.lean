

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} (hf : Continuous f) : IsOpen B → P3 (f ⁻¹' B) := by
  intro hB_open
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' B) := hB_open.preimage hf
  -- Apply the lemma asserting that open sets satisfy `P3`.
  exact P3_of_open (X := X) (A := f ⁻¹' B) hOpen