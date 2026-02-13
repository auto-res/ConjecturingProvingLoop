

theorem nonempty_interior_closure_interior_of_nonempty_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → A.Nonempty →
      (interior (closure (interior (A : Set X)))).Nonempty := by
  intro hP2 hNon
  rcases hNon with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  exact ⟨x, hxInt⟩