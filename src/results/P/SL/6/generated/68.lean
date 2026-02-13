

theorem P2_iUnion_of_P2
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, Topology.P2 (S i)) :
    Topology.P2 (⋃ i, S i) := by
  dsimp [Topology.P2] at hS ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Use `P2` for the chosen set `S i`.
  have hx_int : x ∈ interior (closure (interior (S i))) := (hS i) hx_i
  -- Show this interior is contained in the desired interior.
  have hIncl :
      interior (closure (interior (S i)))
        ⊆ interior (closure (interior (⋃ i, S i))) := by
    apply interior_mono
    have : closure (interior (S i))
        ⊆ closure (interior (⋃ i, S i)) := by
      apply closure_mono
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hIncl hx_int