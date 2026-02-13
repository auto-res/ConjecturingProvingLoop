

theorem Topology.closure_interior_eq_of_isClosed_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP1 : Topology.P1 A) :
    closure (interior A) = A := by
  apply Set.Subset.antisymm
  ·
    have hsubset : interior A ⊆ A := interior_subset
    have hclosure : closure (interior A) ⊆ closure A := closure_mono hsubset
    simpa [hA.closure_eq] using hclosure
  ·
    exact hP1