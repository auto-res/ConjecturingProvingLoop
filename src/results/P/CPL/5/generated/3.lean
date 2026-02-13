

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {s : ι → Set X} (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx₁ : x ∈ interior (closure (interior (s i))) := (h i) hxi
  have hsubset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    exact
      interior_mono
        (closure_mono
          (interior_mono
            (Set.subset_iUnion _ i)))
  exact hsubset hx₁

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} (h : ∀ A ∈ S, P1 A) : P1 (⋃₀ S) := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hP1 : P1 A := h A hAS
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Show that `interior A ⊆ interior (⋃₀ S)`.
  have hsub : (interior A : Set X) ⊆ interior (⋃₀ S) := by
    -- First, `interior A ⊆ ⋃₀ S`.
    have hsub0 : (interior A : Set X) ⊆ ⋃₀ S := by
      intro y hy
      have hyA : y ∈ A := interior_subset hy
      exact Set.mem_sUnion.mpr ⟨A, hAS, hyA⟩
    -- Then take interiors on both sides.
    have hsub1 : interior (interior A) ⊆ interior (⋃₀ S) :=
      interior_mono hsub0
    simpa [interior_interior] using hsub1
  -- Take closures to obtain the desired inclusion.
  have hsubset_cl :
      closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
    closure_mono hsub
  exact hsubset_cl hx_cl

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : P3 A := by
  intro x hx
  simpa [hA.closure_eq, interior_univ]