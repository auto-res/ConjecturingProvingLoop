

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hsubset :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact hsubset (hA hAx)
  | inr hBx =>
      have hsubset :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact hsubset (hB hBx)

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_cl : x ∈ closure (interior (s i)) := (h i) hxi
  have hsubset :
      closure (interior (s i)) ⊆
        closure (interior (⋃ j, s j)) := by
    exact
      closure_mono
        (interior_mono
          (Set.subset_iUnion _ i))
  exact hsubset hx_cl

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : ι → Set X} (h : ∀ i, P3 (s i)) : P3 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx₁ : x ∈ interior (closure (s i)) := (h i) hxi
  have hsubset :
      interior (closure (s i)) ⊆
        interior (closure (⋃ j, s j)) := by
    exact
      interior_mono
        (closure_mono
          (Set.subset_iUnion _ i))
  exact hsubset hx₁

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_int

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  simpa [hA.interior_eq] using (subset_closure hx)

theorem P3_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ P2 A := by
  -- Useful rewrites and inclusions stemming from `hA`
  have h_closure_eq : closure A = A := hA.closure_eq
  have h_int_eq : interior (closure A) = interior A := by
    simpa [h_closure_eq]
  have h_closure_subset : closure (interior A) ⊆ A := by
    have : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [h_closure_eq] using this
  have h_int_subset : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h_closure_subset
  have h_subset_int : interior A ⊆ interior (closure (interior A)) := by
    have h_sub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal h_sub isOpen_interior
  -- Now prove the equivalence
  constructor
  · intro hP3
    intro x hx
    -- From `P3` we enter `interior A`
    have hx_intA : x ∈ interior A := by
      have h := hP3 hx
      simpa [h_int_eq] using h
    -- Expand to the larger interior required by `P2`
    exact h_subset_int hx_intA
  · intro hP2
    intro x hx
    -- `hP2` gives the larger interior; shrink it to `interior A`
    have hx_intA : x ∈ interior A := h_int_subset (hP2 hx)
    -- Rewrite back to `interior (closure A)` for `P3`
    simpa [h_int_eq] using hx_intA

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P3 A) : P3 (⋃₀ S) := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hP3A : P3 A := h A hAS
  have hx_int_clA : x ∈ interior (closure A) := hP3A hxA
  have hsubset :
      interior (closure A) ⊆ interior (closure (⋃₀ S)) := by
    have hsub : (A : Set X) ⊆ ⋃₀ S := by
      intro y hy
      exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
    exact interior_mono (closure_mono hsub)
  exact hsubset hx_int_clA

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P2 A) : P2 (⋃₀ S) := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hP2A : P2 A := h A hAS
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  -- We will prove that `interior (closure (interior A))` is contained in
  -- `interior (closure (interior (⋃₀ S)))`.
  -- First, note that `interior A ⊆ ⋃₀ S`.
  have hsub0 : (interior A : Set X) ⊆ ⋃₀ S := by
    intro y hy
    have hyA : y ∈ A := interior_subset hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hyA⟩
  -- Hence `interior A ⊆ interior (⋃₀ S)`.
  have hsub_int : (interior A : Set X) ⊆ interior (⋃₀ S) := by
    simpa [interior_interior] using (interior_mono hsub0)
  -- Taking closures and then interiors gives the desired inclusion.
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    exact
      interior_mono
        (closure_mono hsub_int)
  exact hsubset hx_int