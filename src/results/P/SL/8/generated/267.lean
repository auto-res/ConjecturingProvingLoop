

theorem closure_interior_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `interior A ∩ B` is contained in `A`.
  have hA : interior A ∩ B ⊆ A := by
    intro y hy
    exact interior_subset hy.1
  -- `interior A ∩ B` is also contained in `B`.
  have hB : interior A ∩ B ⊆ B := by
    intro y hy
    exact hy.2
  -- Monotonicity of `closure` yields the desired memberships.
  have hxA : x ∈ closure A := (closure_mono hA) hx
  have hxB : x ∈ closure B := (closure_mono hB) hx
  exact And.intro hxA hxB