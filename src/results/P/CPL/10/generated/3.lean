

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure A ∪ closure B) := by
  have hA_closure : Topology.P1 (closure A) := Topology.P1_of_closure hA
  have hB_closure : Topology.P1 (closure B) := Topology.P1_of_closure hB
  simpa using Topology.P1_union hA_closure hB_closure

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A := by
  intro x hx
  -- Since `A` is open, its interior is `A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  -- `interior A` is open and contained in its closure, therefore contained
  -- in the interior of that closure
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  exact hsubset hx_int

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} (hS : ∀ A ∈ 𝒮, Topology.P1 A) : Topology.P1 (⋃₀ 𝒮) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := hS A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have hsubset : (closure (interior A) : Set X) ⊆ closure (interior (⋃₀ 𝒮)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact hsubset hx_closure

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  intro x hx
  -- `interior A` is open and contained in its closure,
  -- hence contained in the interior of that closure
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  exact hsubset hx