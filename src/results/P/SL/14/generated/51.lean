

theorem Topology.dense_iff_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      hDense.closure_eq
    have : interior (closure A) = interior ((Set.univ : Set X)) := by
      simpa [h_closure]
    simpa [interior_univ] using this
  · intro hInterior
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      have : interior (closure A) ⊆ closure A := interior_subset
      simpa [hInterior] using this
    have h_closure_eq : closure A = (Set.univ : Set X) := by
      have h_superset : closure A ⊆ (Set.univ : Set X) := by
        intro x hx
        simp
      exact Set.Subset.antisymm h_superset h_subset
    exact (dense_iff_closure_eq).2 h_closure_eq