

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P1 (s i)) → Topology.P1 (⋃ i, s i) := by
  intro hP1
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hx_i⟩
  have hx_closure : x ∈ closure (interior (s i)) := (hP1 i) hx_i
  have hsubset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    have hInt : interior (s i) ⊆ interior (⋃ j, s j) := by
      have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hSub
    exact closure_mono hInt
  exact hsubset hx_closure