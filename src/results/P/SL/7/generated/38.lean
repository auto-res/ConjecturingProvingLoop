

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (∀ i, Topology.P2 (F i)) → Topology.P2 (⋃ i, F i) := by
  classical
  intro hF
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_intFi : x ∈ interior (closure (interior (F i))) := hF i hxFi
  have hSub : interior (closure (interior (F i))) ⊆
      interior (closure (interior (⋃ j, F j))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hx_intFi