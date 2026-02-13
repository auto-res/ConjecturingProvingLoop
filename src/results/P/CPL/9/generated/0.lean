

theorem P2_imp_P3 {A : Set X} : P2 A → P3 A := by
  intro h x hx
  exact (interior_mono (closure_mono interior_subset)) (h hx)

theorem P2_imp_P1 {A : Set X} : P2 A → P1 A := by
  intro h x hx
  exact interior_subset (h hx)

theorem P1_univ : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ]

theorem P2_univ : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_empty : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem union_P1 {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      have h₁ : x ∈ closure (interior A) := hA hA_mem
      have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h₂ h₁
  | inr hB_mem =>
      have h₁ : x ∈ closure (interior B) := hB hB_mem
      have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h₂ h₁