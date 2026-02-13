

theorem interior_closure_interior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (A : Set X).Nonempty →
      (interior (closure (interior (A : Set X)))).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  exact ⟨x, hx⟩