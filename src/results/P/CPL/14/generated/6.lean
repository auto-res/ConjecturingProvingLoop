

theorem P3_sUnion {X} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P3 A) → P3 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP3A : P3 A := hAll A hAℱ
  have hx_intA : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ ℱ)) := by
    have hsubset_closure : closure A ⊆ closure (⋃₀ ℱ) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ ℱ := Set.subset_sUnion_of_mem hAℱ
      exact closure_mono hA_subset
    exact interior_mono hsubset_closure
  exact hsubset hx_intA

theorem P2_bUnion {X I} [TopologicalSpace X] {F : I → Set X} : (∀ i, P2 (F i)) → P2 (⋃ i, F i) := by
  intro hAll
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  -- Apply `P2` for the chosen index `i`.
  have hx_int : x ∈ interior (closure (interior (F i))) := (hAll i) hxFi
  -- Establish the inclusion chains needed for monotonicity.
  have hsubset_int : interior (F i) ⊆ interior (⋃ j, F j) :=
    interior_mono (Set.subset_iUnion _ _)
  have hsubset_closure :
      closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
    closure_mono hsubset_int
  have hsubset :
      interior (closure (interior (F i))) ⊆
      interior (closure (interior (⋃ j, F j))) :=
    interior_mono hsubset_closure
  exact hsubset hx_int

theorem P2_iff_P1_of_closure_open {X} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P1_of_P2 hP2
  · intro hP1
    intro x hxA
    -- `closure A ⊆ closure (interior A)`
    have h_closure_subset : (closure (A) : Set X) ⊆ closure (interior A) := by
      simpa [closure_closure] using
        (closure_mono (hP1 : (A : Set X) ⊆ closure (interior A)))
    -- Since `closure A` is open, it is contained in the interior of `closure (interior A)`
    have h_closure_subset_int :
        (closure (A) : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal h_closure_subset h
    -- `x` belongs to `closure A`, hence to the desired interior
    have hx_closure : x ∈ closure A := subset_closure hxA
    exact h_closure_subset_int hx_closure