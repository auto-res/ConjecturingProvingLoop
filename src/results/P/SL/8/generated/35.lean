

theorem Topology.P2_nonempty_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP2 hx⟩