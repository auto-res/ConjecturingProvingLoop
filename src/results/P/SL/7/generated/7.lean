

theorem Topology.P1_closed_iff_closureInterior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P1 A ↔ closure (interior A) = A := by
  unfold Topology.P1
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have : closure (interior A) ⊆ closure A := closure_mono interior_subset
      simpa [hA.closure_eq] using this
    · exact hP1
  · intro hEq
    simpa [hEq] using (Set.Subset.rfl : A ⊆ A)