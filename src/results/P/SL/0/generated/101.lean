

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A : Set X).Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩