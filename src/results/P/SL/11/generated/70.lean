

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝔄 : Set (Set X)}
    (hA : ∀ A, A ∈ 𝔄 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝔄) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hxCl : x ∈ closure (interior A) := hA A hA_mem hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝔄)) := by
    apply closure_mono
    have : interior A ⊆ interior (⋃₀ 𝔄) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact this
  exact hsubset hxCl