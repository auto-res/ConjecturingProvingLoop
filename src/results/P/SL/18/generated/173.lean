

theorem P2_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h : ∀ B, B ∈ A → Topology.P2 (B : Set X)) :
    Topology.P2 (⋃₀ A) := by
  classical
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBA, hxB⟩
  have hPB : (B : Set X) ⊆ interior (closure (interior B)) := h B hBA
  have hxInt : x ∈ interior (closure (interior B)) := hPB hxB
  have hIncl :
      interior (closure (interior B)) ⊆
        interior (closure (interior (⋃₀ A))) := by
    apply interior_mono
    have : closure (interior B) ⊆ closure (interior (⋃₀ A)) := by
      apply closure_mono
      have : interior (B : Set X) ⊆ interior (⋃₀ A) := by
        apply interior_mono
        exact Set.subset_sUnion_of_mem hBA
      exact this
    exact this
  exact hIncl hxInt