

theorem closed_P1_iff_closure_interior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    dsimp [Topology.P1] at hP1
    have h_subset₁ : closure (interior A) ⊆ A := by
      have h_int : interior A ⊆ A := interior_subset
      have h_clos : closure (interior A) ⊆ closure A := closure_mono h_int
      simpa [hA_closed.closure_eq] using h_clos
    exact Set.Subset.antisymm h_subset₁ hP1
  · intro h_eq
    dsimp [Topology.P1]
    have h : A ⊆ A := subset_rfl
    simpa [h_eq] using h