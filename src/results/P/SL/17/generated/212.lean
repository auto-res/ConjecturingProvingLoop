

theorem Topology.nonempty_closure_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty ↔ (interior A).Nonempty := by
  constructor
  · intro hClNon
    by_cases hInt : (interior A).Nonempty
    · exact hInt
    ·
      exfalso
      rcases hClNon with ⟨x, hx_cl⟩
      -- If `interior A` is empty, its closure is also empty, contradicting `hx_cl`.
      have hIntEmpty : interior A = (∅ : Set X) := by
        apply Set.eq_empty_iff_forall_not_mem.2
        intro y hy
        have : (interior A).Nonempty := ⟨y, hy⟩
        exact (hInt this).elim
      have hFalse : x ∈ (∅ : Set X) := by
        simpa [hIntEmpty, closure_empty] using hx_cl
      cases hFalse
  · intro hIntNon
    rcases hIntNon with ⟨x, hx_int⟩
    exact ⟨x, subset_closure hx_int⟩