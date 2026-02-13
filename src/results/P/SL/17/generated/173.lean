

theorem Topology.iUnion_closure_interiors_subset_closure_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (interior (A i))) ⊆ closure (interior (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hsubset : interior (A i) ⊆ interior (⋃ i, A i) :=
    interior_mono (Set.subset_iUnion A i)
  have hclosure : closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) :=
    closure_mono hsubset
  exact hclosure hx_i