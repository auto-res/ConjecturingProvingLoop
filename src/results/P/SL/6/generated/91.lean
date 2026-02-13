

theorem nonempty_interior_closure_of_nonempty_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → A.Nonempty →
      (interior (closure (A : Set X))).Nonempty := by
  intro hP3 hNon
  rcases hNon with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (A : Set X)) := hP3 hxA
  exact ⟨x, hxInt⟩