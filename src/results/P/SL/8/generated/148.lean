

theorem interior_nonempty_iff_interiorClosureInterior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty ↔ (interior (closure (interior A))).Nonempty := by
  classical
  constructor
  · intro hIntA
    rcases hIntA with ⟨x, hx⟩
    have hSub : interior A ⊆ interior (closure (interior A)) := by
      have h₁ : interior A ⊆ closure (interior A) := subset_closure
      have h₂ := interior_mono h₁
      simpa [interior_interior] using h₂
    exact ⟨x, hSub hx⟩
  · intro hIntCl
    by_cases hIntA : (interior A).Nonempty
    · exact hIntA
    ·
      have hIntAEq : interior A = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hIntA
      have hIntClEq : interior (closure (interior A)) = (∅ : Set X) := by
        simpa [hIntAEq, closure_empty, interior_empty]
      rcases hIntCl with ⟨x, hx⟩
      have hFalse : False := by
        have : (x : X) ∈ (∅ : Set X) := by
          simpa [hIntClEq] using hx
        exact this
      exact (False.elim hFalse)