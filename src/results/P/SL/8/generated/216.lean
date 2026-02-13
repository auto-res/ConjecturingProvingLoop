

theorem closureInterior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hIntEmpty
    have hIntEq : interior A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hIntEmpty
    have hClEq : closure (interior A) = (∅ : Set X) := by
      simpa [hIntEq, closure_empty] using rfl
    rcases hCl with ⟨x, hx⟩
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hClEq] using hx
    exact this.elim
  · intro hInt
    exact hInt.mono (subset_closure : interior A ⊆ closure (interior A))