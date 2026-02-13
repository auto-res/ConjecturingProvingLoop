

theorem Topology.interiorClosure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩