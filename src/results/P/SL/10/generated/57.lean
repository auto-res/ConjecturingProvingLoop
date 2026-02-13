

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} :
    (∀ A, A ∈ S → Topology.P3 A) → Topology.P3 (⋃₀ S) := by
  intro h_all
  dsimp [Topology.P3] at h_all ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hP3A : Topology.P3 A := h_all A hAS
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have hA_subset : A ⊆ ⋃₀ S := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hAS, hy⟩
  have h_closure_subset : closure A ⊆ closure (⋃₀ S) :=
    closure_mono hA_subset
  have h_int_subset : interior (closure A) ⊆ interior (closure (⋃₀ S)) :=
    interior_mono h_closure_subset
  exact h_int_subset hx_int