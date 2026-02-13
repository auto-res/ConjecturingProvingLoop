

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty → Topology.P3 (A : Set X) →
      (interior (closure (A : Set X))).Nonempty := by
  intro hA hP3
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩