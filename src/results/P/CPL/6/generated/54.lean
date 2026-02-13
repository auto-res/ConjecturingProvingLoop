

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : IsOpen B) (f : C(X, Y)) : P3 (f ⁻¹' B) := by
  have hOpenPre : IsOpen (f ⁻¹' B) := by
    simpa using hB.preimage f.continuous
  exact P3_of_open (A := f ⁻¹' B) hOpenPre