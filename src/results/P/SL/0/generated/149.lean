

theorem closure_inter_subset_inter_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  -- `A ∩ B` is contained in `A`, so the closure relation is preserved.
  have hSubA : (A ∩ B : Set X) ⊆ (A : Set X) := by
    intro y hy
    exact hy.1
  have hxA : x ∈ closure (A : Set X) := (closure_mono hSubA) hx
  -- Symmetrically for `B`.
  have hSubB : (A ∩ B : Set X) ⊆ (B : Set X) := by
    intro y hy
    exact hy.2
  have hxB : x ∈ closure (B : Set X) := (closure_mono hSubB) hx
  exact And.intro hxA hxB