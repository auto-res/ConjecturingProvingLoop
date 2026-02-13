

theorem P3_of_closure_open {X} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : P3 A := by
  intro x hxA
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [h.interior_eq] using hx_closure

theorem P3_of_interior_eq {X} [TopologicalSpace X] {A : Set X} (h : interior A = A) : P3 A := by
  intro x hxA
  -- turn the hypothesis into a membership of `interior A`
  have hx_int : x ∈ interior A := by
    simpa [h] using hxA
  -- `interior A` is contained in `interior (closure A)`
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_int

theorem P1_of_closure_eq {X} [TopologicalSpace X] {A : Set X} (h : closure A = closure (interior A)) : P1 A := by
  intro x hx
  have hx_closure : x ∈ closure (A : Set X) := subset_closure hx
  simpa [h] using hx_closure

theorem P2_sUnion {X} [TopologicalSpace X] {ℱ : Set (Set X)} (h : ∀ A ∈ ℱ, P2 A) : P2 (⋃₀ ℱ) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAℱ, hxA⟩
  have hP2A : P2 A := h A hAℱ
  have hx_intA : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset_int : interior A ⊆ interior (⋃₀ ℱ) :=
    interior_mono (Set.subset_sUnion_of_mem hAℱ)
  have hsubset_closure :
      closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) :=
    closure_mono hsubset_int
  have hsubset :
      interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ ℱ))) :=
    interior_mono hsubset_closure
  exact hsubset hx_intA

theorem P1_iUnion {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P1 (F i)) : P1 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_cl : x ∈ closure (interior (F i)) := (h i) hxFi
  have hsubset_int : interior (F i) ⊆ interior (⋃ j, F j) :=
    interior_mono (Set.subset_iUnion _ _)
  have hsubset_cl : closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) :=
    closure_mono hsubset_int
  exact hsubset_cl hx_cl