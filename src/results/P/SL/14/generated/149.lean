

theorem Topology.closureInteriorClosure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      closure (interior (closure A)) = closure A := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    exact Topology.closureInteriorClosure_subset_closure (X := X) (A := A)
  ·
    have : (closure A : Set X) ⊆ closure (interior (closure A)) := by
      -- From `P3` we have `A ⊆ interior (closure A)`.
      have h_subset : (A : Set X) ⊆ interior (closure A) := hP3
      -- Taking closures preserves inclusions.
      exact closure_mono h_subset
    simpa using this