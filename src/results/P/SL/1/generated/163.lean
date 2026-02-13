

theorem Topology.interior_closure_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  -- Show `closure (A i)` is contained in `closure (⋃ i, A i)`.
  have hsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` then yields the desired inclusion.
  have hIntSubset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono hsubset
  exact hIntSubset hxInt