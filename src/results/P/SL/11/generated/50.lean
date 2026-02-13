

theorem interior_closure_interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hne : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hne with ⟨x, hxA⟩
  exact ⟨x, hP2 hxA⟩