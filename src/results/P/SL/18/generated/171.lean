

theorem P1_sUnion {X : Type*} [TopologicalSpace X] (A : Set (Set X))
    (h : ∀ B, B ∈ A → Topology.P1 (B : Set X)) :
    Topology.P1 (⋃₀ A) := by
  classical
  dsimp [Topology.P1] at h ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBA, hxB⟩
  have hPB : (B : Set X) ⊆ closure (interior B) := h B hBA
  have hx_cl : x ∈ closure (interior B) := hPB hxB
  have hSub : (B : Set X) ⊆ ⋃₀ A := Set.subset_sUnion_of_mem hBA
  have hIntSub : interior B ⊆ interior (⋃₀ A) := by
    apply interior_mono
    exact hSub
  have h_mono : closure (interior B) ⊆ closure (interior (⋃₀ A)) :=
    closure_mono hIntSub
  exact h_mono hx_cl