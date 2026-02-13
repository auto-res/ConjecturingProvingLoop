

theorem Topology.P3_nonempty_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hxA⟩
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, hx_int⟩