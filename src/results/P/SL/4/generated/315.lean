

theorem closure_diff_subset_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A ∩ closure (Bᶜ) := by
  intro x hx
  -- `A \ B` is contained in `A`, hence its closure is contained in `closure A`.
  have hA : x ∈ closure A := by
    have h_sub : (A \ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono h_sub) hx
  -- `A \ B` is also contained in `Bᶜ`, yielding membership in `closure (Bᶜ)`.
  have hB : x ∈ closure (Bᶜ) := by
    have h_sub : (A \ B : Set X) ⊆ Bᶜ := by
      intro y hy; exact hy.2
    exact (closure_mono h_sub) hx
  exact And.intro hA hB