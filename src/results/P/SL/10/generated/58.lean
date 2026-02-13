

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} :
    (∀ A, A ∈ S → Topology.P2 A) → Topology.P2 (⋃₀ S) := by
  intro h_all
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hP2A : Topology.P2 A := h_all A hAS
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hA_subset : A ⊆ ⋃₀ S := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hAS, hy⟩
  have h_int_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    have h_int : interior A ⊆ interior (⋃₀ S) :=
      interior_mono hA_subset
    have h_closure :
        closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
      closure_mono h_int
    exact interior_mono h_closure
  exact h_int_subset hx_int