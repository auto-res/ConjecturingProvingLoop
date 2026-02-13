

theorem Topology.closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A → closure (interior A) ⊆ A := by
  intro hClosed
  have hsubset :
      (closure (interior A) : Set X) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  simpa [hClosed.closure_eq] using hsubset