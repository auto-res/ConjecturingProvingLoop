

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P3 (s i)) → Topology.P3 (⋃ i, s i) := by
  intro hP3
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hx_i⟩
  have hx_int : x ∈ interior (closure (s i)) := (hP3 i) hx_i
  have hsubset : interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) := by
    have hcl : closure (s i) ⊆ closure (⋃ j, s j) := by
      have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono hSub
    exact interior_mono hcl
  exact hsubset hx_int