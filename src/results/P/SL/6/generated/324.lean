

theorem closure_iUnion_closure_eq_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (S : ι → Set X) :
    closure (⋃ i, closure (S i) : Set X) = closure (⋃ i, S i) := by
  apply Set.Subset.antisymm
  · -- `⋃ i, closure (S i)` is contained in `closure (⋃ i, S i)`
    have hSub : (⋃ i, closure (S i) : Set X) ⊆ closure (⋃ i, S i) :=
      iUnion_closure_subset_closure_iUnion (S := S)
    -- Taking closures and simplifying yields the desired inclusion.
    simpa [closure_closure] using (closure_mono hSub)
  · -- Each `S i` is contained in `closure (S i)`, hence the unions satisfy the same.
    have hSub : (⋃ i, S i : Set X) ⊆ ⋃ i, closure (S i) := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxSi⟩
      exact Set.mem_iUnion.2 ⟨i, (subset_closure hxSi)⟩
    -- Monotonicity of `closure` gives the reverse inclusion.
    simpa using (closure_mono hSub)