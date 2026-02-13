

theorem P3_iff_P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P3 A ↔ Topology.P3 (e '' A) := by
  constructor
  · intro hA
    exact P3_image_homeomorph (e := e) (A := A) hA
  · intro hImg
    have h' : Topology.P3 ((e.symm) '' (e '' A)) :=
      P3_image_homeomorph (e := e.symm) (A := e '' A) hImg
    have hEq : ((e.symm) '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h'