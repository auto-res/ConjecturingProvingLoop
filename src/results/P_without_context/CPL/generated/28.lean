

theorem P2_imp_P1 {A : Set X} (h : P2 A) : P1 A := by
  unfold P1 P2 at *
  exact Set.Subset.trans h interior_subset

theorem P2_imp_P3 {A : Set X} (h : P2 A) : P3 A := by
  unfold P2 P3 at *
  exact
    Set.Subset.trans h
      (interior_mono (by
        have h₁ : interior A ⊆ closure A :=
          (interior_subset : interior A ⊆ A).trans subset_closure
        simpa [closure_closure] using (closure_mono h₁)))

theorem P1_iff_closure_eq {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  unfold P1
  constructor
  · intro hP1
    have h1 : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    have h2 : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using this
    exact Set.Subset.antisymm h1 h2
  · intro hEq
    have hsubset : A ⊆ closure A := subset_closure
    simpa [hEq] using hsubset

theorem open_set_P3 {A : Set X} (hA : IsOpen A) : P3 A := by
  unfold P3
  exact interior_maximal subset_closure hA

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- We work with the unfolded definition of `P1`
  unfold P1 at *
  -- Take an arbitrary point in `A ∪ B`
  intro x hx
  -- Distinguish whether it comes from `A` or from `B`
  cases hx with
  | inl hAx =>
      -- If `x ∈ A`, use the hypothesis `hA`
      have hx₁ : x ∈ closure (interior A) := hA hAx
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      -- Hence the desired conclusion
      exact hsubset hx₁
  | inr hBx =>
      -- The case `x ∈ B` is analogous
      have hx₁ : x ∈ closure (interior B) := hB hBx
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx₁