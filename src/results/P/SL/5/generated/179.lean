

theorem closure_inter_interior_subset_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `closure A`
  have hA : (A ∩ interior B : Set X) ⊆ A := Set.inter_subset_left
  have hxA : x ∈ closure A := (closure_mono hA) hx
  -- `closure B`
  have hB : (A ∩ interior B : Set X) ⊆ B := by
    intro y hy
    exact interior_subset hy.2
  have hxB : x ∈ closure B := (closure_mono hB) hx
  exact ⟨hxA, hxB⟩