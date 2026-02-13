

theorem Topology.iUnion_interior_closure_subset_interior_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (⋃ i, interior (closure (s i))) ⊆ interior (closure (⋃ i, s i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (s i)` is contained in `closure (⋃ j, s j)`.
  have hcl : closure (s i) ⊆ closure (⋃ j, s j) := by
    have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono hSub
  -- Applying monotonicity of `interior` to the inclusion of closures.
  have hInt :
      interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) :=
    interior_mono hcl
  exact hInt hx_i