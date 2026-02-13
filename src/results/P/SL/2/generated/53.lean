

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    (∀ i, Topology.P2 (s i)) → Topology.P2 (⋃ i, s i) := by
  intro hP2
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hx_i⟩
  have hx_int : x ∈ interior (closure (interior (s i))) := (hP2 i) hx_i
  have hsubset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    -- First, relate the interiors.
    have hInt : interior (s i) ⊆ interior (⋃ j, s j) := by
      have hSub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hSub
    -- Take closures of both sides.
    have hCl : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) :=
      closure_mono hInt
    -- Finally, take interiors again.
    exact interior_mono hCl
  exact hsubset hx_int