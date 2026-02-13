

theorem Topology.closure_interior_inter_subset_inter_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  -- `interior A ∩ B` is contained in `interior A`
  have hSubIntA : (interior A ∩ B : Set X) ⊆ interior A := fun y hy => hy.1
  -- `interior A ∩ B` is also contained in `B`
  have hSubB : (interior A ∩ B : Set X) ⊆ B := fun y hy => hy.2
  -- Monotonicity of `closure` gives the two required memberships
  have hxIntA : x ∈ closure (interior A) := (closure_mono hSubIntA) hx
  have hxB : x ∈ closure B := (closure_mono hSubB) hx
  exact And.intro hxIntA hxB