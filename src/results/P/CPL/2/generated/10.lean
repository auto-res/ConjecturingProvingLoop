

theorem P3_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : Topology.P3 (X:=X) A := by
  intro x hx
  simpa [hA, interior_univ] using (Set.mem_univ x)

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P2 (X:=Y) B) : Topology.P2 (X:=X) (e ⁻¹' B) := by
  classical
  -- Step 1: transport `P2` through the inverse homeomorphism
  have hP2_image : Topology.P2 (X := X) (e.symm '' B) := by
    simpa using
      (Topology.P2_image_homeomorph (X := Y) (e := e.symm) (A := B) hB)
  -- Step 2: identify the image with the preimage
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp [e.symm_apply_apply]⟩
  -- Step 3: rewrite and finish
  simpa [h_eq] using hP2_image