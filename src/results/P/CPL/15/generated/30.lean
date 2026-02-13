

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P2_subset_P3 (A := A) hP2
  · intro hP3
    exact P2_of_P3_and_closed (A := A) hP3 hA

theorem P1_Union_closures {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, closure (A i)) := by
  intro x hx
  -- pick the index witnessing the union
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `P1 (A i)` yields `closure (A i) ⊆ closure (interior (A i))`
  have h_closure_subset :
      (closure (A i) : Set X) ⊆ closure (interior (A i)) :=
    (P1_dense_iff (X := X) (A := A i)).1 (h i)
  have hx₁ : x ∈ closure (interior (A i)) := h_closure_subset hx_i
  -- show that `interior (A i)` is contained in the interior of the big union
  have h_int_subset_int :
      (interior (A i) : Set X) ⊆ interior (⋃ j, closure (A j)) := by
    intro y hy
    rcases mem_interior.1 hy with ⟨U, hU_sub, hU_open, hyU⟩
    have hU_sub' : (U : Set X) ⊆ ⋃ j, closure (A j) := by
      intro z hz
      have hzAi : (z : X) ∈ A i := hU_sub hz
      have hz_cl : (z : X) ∈ closure (A i) := subset_closure hzAi
      exact Set.mem_iUnion.2 ⟨i, hz_cl⟩
    exact mem_interior.2 ⟨U, hU_sub', hU_open, hyU⟩
  -- take closures on both sides
  have h_subset :
      (closure (interior (A i)) : Set X) ⊆
        closure (interior (⋃ j, closure (A j))) :=
    closure_mono h_int_subset_int
  exact h_subset hx₁

theorem exists_compact_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ K, IsCompact K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  exact Set.empty_subset _

theorem P3_iff_dense_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ closure A = closure (interior A) := by
  constructor
  · intro _hP3
    simpa [hA.interior_eq]
  · intro _hEq
    exact P3_open (A := A) hA