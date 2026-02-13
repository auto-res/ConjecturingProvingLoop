

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (∀ i, Topology.P1 (F i)) → Topology.P1 (⋃ i, F i) := by
  classical
  intro hF
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_closureFi : x ∈ closure (interior (F i)) := hF i hxFi
  have hSub : closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hx_closureFi