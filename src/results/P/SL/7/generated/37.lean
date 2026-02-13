

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (∀ i, Topology.P3 (F i)) → Topology.P3 (⋃ i, F i) := by
  classical
  intro hF
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_intFi : x ∈ interior (closure (F i)) := hF i hxFi
  have hSub : interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) := by
    apply interior_mono
    have : (closure (F i)) ⊆ closure (⋃ j, F j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hSub hx_intFi