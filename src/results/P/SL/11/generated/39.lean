

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hne : A.Nonempty) : (interior (closure A)).Nonempty := by
  rcases hne with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩