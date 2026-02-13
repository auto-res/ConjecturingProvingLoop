

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `A ∩ interior B` is contained in `A`
  have hSubA : (A ∩ interior B : Set X) ⊆ A := fun z hz => hz.1
  -- `A ∩ interior B` is also contained in `B`
  have hSubB : (A ∩ interior B : Set X) ⊆ B := by
    intro z hz
    exact interior_subset hz.2
  -- Monotonicity of `closure`
  have hxA : x ∈ closure A := (closure_mono hSubA) hx
  have hxB : x ∈ closure B := (closure_mono hSubB) hx
  exact And.intro hxA hxB