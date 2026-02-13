

theorem P3_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h : ∀ B, B ∈ A → Topology.P3 (B : Set X)) :
    Topology.P3 (⋃₀ A) := by
  classical
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBA, hxB⟩
  have hx_in : x ∈ interior (closure (B : Set X)) := h B hBA hxB
  have hIncl : interior (closure (B : Set X)) ⊆
      interior (closure (⋃₀ A)) := by
    apply interior_mono
    have hSub : (B : Set X) ⊆ ⋃₀ A :=
      Set.subset_sUnion_of_mem hBA
    exact closure_mono hSub
  exact hIncl hx_in