

theorem Topology.nonempty_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (A := A)) (hNon : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hNon with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩