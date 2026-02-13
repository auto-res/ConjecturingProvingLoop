

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : (∀ A ∈ S, Topology.P1 A) → Topology.P1 (⋃₀ S) := by
  intro hP1
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hx_closure : x ∈ closure (interior A) := hP1 A hAS hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ S)) := by
    have h_int_subset : interior A ⊆ interior (⋃₀ S) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ S := Set.subset_sUnion_of_mem hAS
      exact interior_mono hA_subset
    exact closure_mono h_int_subset
  exact hsubset hx_closure

theorem P3_unionₛ {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : (∀ A ∈ S, Topology.P3 A) → Topology.P3 (⋃₀ S) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hx_int : x ∈ interior (closure A) := hP3 A hAS hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ S)) := by
    have h_closure_subset : closure A ⊆ closure (⋃₀ S) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ S := Set.subset_sUnion_of_mem hAS
      exact closure_mono hA_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int