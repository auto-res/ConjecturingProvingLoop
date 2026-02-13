

theorem closure_interior_eq_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = A) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA] using (subset_rfl : A ⊆ A)