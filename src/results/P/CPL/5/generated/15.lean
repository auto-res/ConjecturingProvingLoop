

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : P3 B → P3 (e.symm '' B) := by
  exact (P3_image_homeomorph (e.symm)).1