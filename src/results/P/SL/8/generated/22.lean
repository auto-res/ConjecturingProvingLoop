

theorem Topology.P3_nonempty_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP3 hx⟩