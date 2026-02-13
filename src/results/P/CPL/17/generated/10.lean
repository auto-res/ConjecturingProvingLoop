

theorem P2_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  exact P2_of_open (A := Aᶜ) h_open

theorem P3_iff_P2_for_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    -- `P3` together with closedness implies openness
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have hx_int_cl : x ∈ interior (closure A) := hP3 hx
      have h_closure : closure A = A := hA.closure_eq
      simpa [h_closure] using hx_int_cl
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact h_subset
    have h_open : IsOpen A := by
      simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
    exact P2_of_open (A := A) h_open
  · intro hP2
    exact P2_implies_P3 (A := A) hP2

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : Topology.P3 A := by
  intro x hxA
  -- `closure A` is the whole space because `A` is dense
  have hClosure : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _
      simp
    · intro y _
      exact hA y
  -- hence its interior is also the whole space
  have hInterior : interior (closure A) = (Set.univ : Set X) := by
    simpa [hClosure, interior_univ]
  -- conclude
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInterior] using this

theorem P2_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P2 (f i)) → Topology.P2 (⋃ i, f i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (interior (f i))) := hP2 i hxi
  have hsubset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    -- First, show `interior (f i)` is contained in `interior (⋃ j, f j)`.
    have h_int_subset : interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    -- Then, use monotonicity of `closure` and `interior`.
    have h_closure_subset :
        closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) :=
      closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : (∀ A ∈ S, Topology.P2 A) → Topology.P2 (⋃₀ S) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := (hP2 A hAS) hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    -- First, show `interior A ⊆ interior (⋃₀ S)`.
    have h_int_subset : interior A ⊆ interior (⋃₀ S) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ S := Set.subset_sUnion_of_mem hAS
      exact interior_mono hA_subset
    -- Then lift this inclusion through `closure` and `interior`.
    have h_closure_subset :
        closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
      closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem exists_compact_P3_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ Topology.P3 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · exact P3_empty (X := X)