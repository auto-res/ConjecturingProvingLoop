

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} :
    (∀ A, A ∈ S → Topology.P1 A) → Topology.P1 (⋃₀ S) := by
  intro h_all
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hP1A : Topology.P1 A := h_all A hAS
  have hx_clA : x ∈ closure (interior A) := hP1A hxA
  have hA_subset : A ⊆ ⋃₀ S := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hAS, hy⟩
  have h_int_subset : interior A ⊆ interior (⋃₀ S) :=
    interior_mono hA_subset
  have h_cl_subset : closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
    closure_mono h_int_subset
  exact h_cl_subset hx_clA