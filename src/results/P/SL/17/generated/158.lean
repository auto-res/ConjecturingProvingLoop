

theorem Topology.nonempty_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  classical
  intro hP1 hAne
  rcases hAne with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  by_cases hIntEmpty : interior A = (∅ : Set X)
  · -- This case leads to a contradiction, since `x` cannot lie in `∅`.
    have hFalse : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using hx_cl
    exact False.elim hFalse
  · -- Here, `interior A` is non-empty.
    have h_ne : interior A ≠ (∅ : Set X) := hIntEmpty
    exact (Set.nonempty_iff_ne_empty).2 h_ne