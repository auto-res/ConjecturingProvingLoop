

theorem P1_of_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hEq : closure A = closure (interior A)) :
    Topology.P1 A := by
  dsimp [Topology.P3, Topology.P1] at *
  have hint : interior (closure A) ⊆ closure (interior A) := by
    simpa [hEq] using (interior_subset : interior (closure A) ⊆ closure A)
  exact hP3.trans hint