

theorem P3_of_interior_univ {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = (⊤ : Set X)) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have : (x : X) ∈ (⊤ : Set X) := by
      simp
    simpa [h] using this
  exact
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int