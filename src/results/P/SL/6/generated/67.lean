

theorem P1_iUnion_of_P1 {X : Type*} [TopologicalSpace X] {ι : Sort*}
    {S : ι → Set X} (hS : ∀ i, Topology.P1 (S i)) :
    Topology.P1 (⋃ i, S i) := by
  dsimp [Topology.P1] at hS ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_cl : x ∈ closure (interior (S i)) := (hS i) hx_i
  have hIncl : closure (interior (S i)) ⊆ closure (interior (⋃ i, S i)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hIncl hx_cl