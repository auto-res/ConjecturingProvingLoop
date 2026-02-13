

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} (hS : ∀ A ∈ 𝒮, Topology.P2 A) : Topology.P2 (⋃₀ 𝒮) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := hS A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset :
      (interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (⋃₀ 𝒮))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact hsubset hx_in

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P3 (F i)) : Topology.P3 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hxi' : x ∈ interior (closure (F i)) := hF i hxi
  have hsubset :
      (interior (closure (F i)) : Set X) ⊆ interior (closure (⋃ i, F i)) := by
    apply interior_mono
    apply closure_mono
    exact Set.subset_iUnion _ i
  exact hsubset hxi'

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  intro x hx
  have h_int : x ∈ interior (interior A) := by
    simpa [isOpen_interior.interior_eq] using hx
  exact subset_closure h_int

theorem P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P3 (f ⁻¹' U) := by
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  simpa using (Topology.P3_of_open h_open)

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, closure A = Set.univ ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simp
  · simpa using Topology.P1_univ

theorem P1_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply le_antisymm
    · -- `closure (interior A)` is contained in `closure A`
      exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    · -- use `hP1 : A ⊆ closure (interior A)` to get the reverse inclusion
      have : (A : Set X) ⊆ closure (interior A) := hP1
      simpa [closure_closure] using (closure_mono this)
  · intro hEq
    -- we must show `A ⊆ closure (interior A)`
    intro x hx
    -- `x` is in the closure of `A`
    have hx_closure : x ∈ closure A := subset_closure hx
    -- rewrite using the equality of closures
    simpa [hEq] using hx_closure