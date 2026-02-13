

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  intro x hx
  exact (interior_maximal subset_closure hA) hx

theorem P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P1 (f ⁻¹' U) := by
  intro x hx
  -- The preimage of an open set is open
  have h_open : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- Hence its interior is itself
  have h_int_eq : interior (f ⁻¹' U) = f ⁻¹' U := h_open.interior_eq
  -- So `x` lies in the interior
  have hx_int : x ∈ interior (f ⁻¹' U) := by
    simpa [h_int_eq] using hx
  -- Therefore `x` is in the closure of the interior
  exact subset_closure hx_int

theorem exists_compact_P1 {X : Type*} [TopologicalSpace X] : ∃ K : Set X, IsCompact K ∧ Topology.P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  intro x hx
  cases hx

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {F : ι → Set X} (hF : ∀ i, Topology.P1 (F i)) : Topology.P1 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ closure (interior (F i)) := hF i hxFi
  have hsubset :
      (closure (interior (F i)) : Set X) ⊆ closure (interior (⋃ i, F i)) := by
    apply closure_mono
    apply interior_mono
    exact Set.subset_iUnion _ i
  exact hsubset hxi