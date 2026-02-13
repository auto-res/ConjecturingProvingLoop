

theorem nonempty_of_closure_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hClosInt
  classical
  by_cases hInt : (interior (A : Set X)).Nonempty
  ·
    rcases hInt with ⟨y, hyInt⟩
    exact ⟨y, (interior_subset : interior (A : Set X) ⊆ A) hyInt⟩
  ·
    -- If `interior A` is empty, then its closure is also empty,
    -- contradicting the hypothesis.
    have hIntEq : interior (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hInt
    have hClosEq : closure (interior (A : Set X)) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty]
    rcases hClosInt with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hClosEq] using hx
    exact this.elim