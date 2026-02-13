

theorem Topology.P1_nonempty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hA
  rcases hA with ⟨x, hx⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  classical
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  · have hIntEmpty : interior A = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hInt
    have hFalse : False := by
      have : x ∈ (∅ : Set X) := by
        simpa [hIntEmpty, closure_empty] using hx_cl
      simpa using this
    cases hFalse