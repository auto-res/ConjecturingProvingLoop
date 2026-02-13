

theorem P3_iUnion_of_P3
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, Topology.P3 (S i)) :
    Topology.P3 (⋃ i, S i) := by
  dsimp [Topology.P3] at hS ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Use `P3` for the chosen set `S i`.
  have hx_int : x ∈ interior (closure (S i)) := (hS i) hx_i
  -- Show this interior is contained in the desired interior.
  have hIncl :
      interior (closure (S i)) ⊆ interior (closure (⋃ i, S i)) := by
    apply interior_mono
    have : closure (S i) ⊆ closure (⋃ i, S i) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hIncl hx_int