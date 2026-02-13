

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝔄) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxInt : x ∈ interior (closure A) := hA A hA_mem hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝔄)) := by
    apply interior_mono
    have : closure A ⊆ closure (⋃₀ 𝔄) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hxInt