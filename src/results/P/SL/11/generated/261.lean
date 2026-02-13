

theorem closure_interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hne : A.Nonempty) : (closure (interior A)).Nonempty := by
  rcases hne with ⟨x, hxA⟩
  exact ⟨x, hP1 hxA⟩