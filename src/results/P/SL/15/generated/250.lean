

theorem closureInterior_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A) : Set X).Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    -- If `interior A` were empty, its closure would also be empty,
    -- contradicting the existence of `x`.
    have : (interior A).Nonempty := by
      by_contra hIntEmpty
      have hIntEq : interior A = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hIntEmpty
      have : x ∈ (∅ : Set X) := by
        simpa [hIntEq, closure_empty] using hx
      exact this.elim
    exact this
  · rintro ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩