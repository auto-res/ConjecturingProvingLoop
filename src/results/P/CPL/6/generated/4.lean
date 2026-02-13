

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, Topology.P1 (A i)) → Topology.P1 (⋃ i, A i) := by
  intro hP1
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hx1 : x ∈ closure (interior (A i)) := (hP1 i) hxAi
  have hsubset_interior : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono hsubset_interior
  exact hsubset hx1

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} : (∀ i, Topology.P2 (A i)) → Topology.P2 (⋃ i, A i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxAi⟩
  have hx1 : x ∈ interior (closure (interior (A i))) := (hP2 i) hxAi
  have hsubset_interior : interior (A i) ⊆ interior (⋃ j, A j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono hsubset_interior
  exact (interior_mono hsubset) hx1

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} : (∀ A ∈ 𝓢, Topology.P1 A) → Topology.P1 (⋃₀ 𝓢) := by
  intro hP1
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hx1 : x ∈ closure (interior A) := (hP1 A hAS) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝓢 := by
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
  have hsubset_interior : interior A ⊆ interior (⋃₀ 𝓢) :=
    interior_mono hA_subset
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ 𝓢)) :=
    closure_mono hsubset_interior
  exact hsubset hx1