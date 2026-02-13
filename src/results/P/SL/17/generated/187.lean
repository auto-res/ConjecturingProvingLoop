

theorem Topology.nonempty_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hAne
  rcases hAne with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩