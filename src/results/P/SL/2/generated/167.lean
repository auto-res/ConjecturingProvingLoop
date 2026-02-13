

theorem Topology.isClosed_P3_nonempty_implies_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → A.Nonempty → (interior A).Nonempty := by
  intro hClosed hP3 hA_nonempty
  rcases hA_nonempty with ⟨x, hxA⟩
  have hx_int : x ∈ interior A := by
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hClosed.closure_eq] using this
  exact ⟨x, hx_int⟩