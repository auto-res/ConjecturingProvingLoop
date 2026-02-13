

theorem P3_sUnion_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, IsOpen A) : P3 (⋃₀ 𝒜) := by
  -- Each open set in `𝒜` satisfies `P3`.
  have hP3 : ∀ A ∈ 𝒜, P3 A := by
    intro A hA_mem
    exact P3_of_isOpen (A := A) (hA A hA_mem)
  -- Apply the `P3_sUnion` lemma with this information.
  simpa using P3_sUnion (X := X) (𝒜 := 𝒜) hP3

theorem P1_sigma_set {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P1 A) : P1 {x : X | ∃ A ∈ S, x ∈ A} := by
  -- First, obtain `P1` for the union `⋃₀ S`.
  have hP1 : P1 (⋃₀ S) := P1_sUnion (X := X) (𝒜 := S) h
  -- Identify the σ–set with this union.
  have h_eq : ({x : X | ∃ A ∈ S, x ∈ A} : Set X) = ⋃₀ S := by
    ext x
    constructor
    · rintro ⟨A, hAS, hAx⟩
      exact Set.mem_sUnion.2 ⟨A, hAS, hAx⟩
    · intro hx
      rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hAx⟩
      exact ⟨A, hAS, hAx⟩
  -- Transfer the `P1` property along this equality.
  simpa [h_eq] using hP1

theorem P1_iterate_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (closure (interior A))) := by
  intro x hx
  -- First, rewrite `hx` using idempotence of `closure`.
  have hx' : x ∈ closure (interior A) := by
    simpa [closure_closure] using hx
  -- Show that `closure (interior A)` is contained in the needed closure.
  have h_subset :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) := by
    -- Since `interior A` is open and contained in its closure,
    -- it is contained in the interior of that closure.
    have h_in :
        (interior A : Set X) ⊆ interior (closure (interior A)) :=
      interior_maximal
        (subset_closure :
          (interior A : Set X) ⊆ closure (interior A))
        isOpen_interior
    -- Taking closures preserves the inclusion.
    exact closure_mono h_in
  -- Apply the inclusion to obtain the desired membership.
  have hx'' := h_subset hx'
  simpa [closure_closure] using hx''