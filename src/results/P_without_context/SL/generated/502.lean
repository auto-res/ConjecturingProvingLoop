

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
  Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  have h_subset₁ : closure (interior A) ⊆ closure A := by
    exact closure_mono (interior_subset : interior A ⊆ A)
  have h_subset₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_subset₁
  exact fun x hx => h_subset₂ (hP2 hx)