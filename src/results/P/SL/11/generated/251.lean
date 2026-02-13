

theorem interior_closure_iUnion_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (A i)` is contained in the closure of the union.
  have hsubset_cl : closure (A i) ⊆ closure (⋃ j, A j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` upgrades the inclusion.
  have hsubset_int :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono hsubset_cl
  exact hsubset_int hx_i