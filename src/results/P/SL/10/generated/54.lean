

theorem Topology.P2_nonempty_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior (closure (interior A))).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, hx⟩