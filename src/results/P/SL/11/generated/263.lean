

theorem closure_interior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hInt
    have hIntEq : interior A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hInt
    have hClEq : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty]
    rcases hCl with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hClEq] using hx
    exact (Set.not_mem_empty x) this
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩