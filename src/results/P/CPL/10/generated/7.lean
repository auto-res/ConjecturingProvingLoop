

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} (hS : ∀ A ∈ 𝒮, Topology.P3 A) : Topology.P3 (⋃₀ 𝒮) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := hS A hA_mem
  have hx_in : x ∈ interior (closure A) := hP3A hxA
  have hsubset :
      (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ 𝒮)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact hsubset hx_in

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P2 (f ⁻¹' U) := by
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  simpa using (Topology.P2_of_open h_open)