

theorem Topology.P3_nonempty_implies_interior_closure_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hA_nonempty
  rcases hA_nonempty with ⟨x, hxA⟩
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, hx_int⟩