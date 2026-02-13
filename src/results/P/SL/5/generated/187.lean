

theorem closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A \ interior B := by
  intro x hx
  -- `x` lies in `closure A` because `A \ B ⊆ A`.
  have hx_clA : x ∈ closure (A : Set X) := by
    have hsubset : (A \ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (closure_mono hsubset) hx
  -- Show `x ∉ interior B`; otherwise reach a contradiction.
  have hx_not_intB : x ∉ interior B := by
    intro hx_intB
    -- Use the neighbourhood characterization of the closure.
    have hmem := (mem_closure_iff).1 hx
    have hNon : ((interior B : Set X) ∩ (A \ B : Set X)).Nonempty :=
      hmem (interior B) isOpen_interior hx_intB
    rcases hNon with ⟨y, ⟨hy_intB, hy_A_diff_B⟩⟩
    have hy_in_B : y ∈ B := interior_subset hy_intB
    exact hy_A_diff_B.2 hy_in_B
  exact ⟨hx_clA, hx_not_intB⟩