

theorem P1_closed_iff_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  dsimp [Topology.P1]
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have hSub : closure (interior A) ⊆ closure A :=
        closure_mono interior_subset
      simpa [hA_closed.closure_eq] using hSub
    ·
      exact hP1
  · intro hEq
    simpa [hEq] using (subset_rfl : A ⊆ A)