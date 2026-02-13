

theorem P2_of_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hEq : closure A = closure (interior A)) :
    Topology.P2 A := by
  dsimp [Topology.P2, Topology.P3] at *
  have hsubset : interior (closure A) ⊆ interior (closure (interior A)) := by
    simpa [hEq]
  exact hP3.trans hsubset