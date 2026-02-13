

theorem Topology.P1_nonempty_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP1 hx⟩