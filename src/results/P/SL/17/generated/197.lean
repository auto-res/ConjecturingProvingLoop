

theorem Topology.nonempty_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty →
      (interior (closure (interior A))).Nonempty := by
  intro hP2 hAne
  rcases hAne with ⟨x, hxA⟩
  exact ⟨x, hP2 hxA⟩