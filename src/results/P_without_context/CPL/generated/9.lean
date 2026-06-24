

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro h
  exact Set.Subset.trans h interior_subset

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_clA : x ∈ closure (interior A) := hA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsub : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          exact Set.subset_union_left
        exact closure_mono hsub
      exact hsubset hx_clA
  | inr hxB =>
      -- `x ∈ B`
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsub : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          exact Set.subset_union_right
        exact closure_mono hsub
      exact hsubset hx_clB

theorem dense_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  · exact closure_mono interior_subset
  ·
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this

theorem interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → interior (closure (interior A)) = interior (closure A) := by
  intro hP2
  have hP1 : P1 A := P2_imp_P1 hP2
  have hcl : closure (interior A) = closure A := dense_of_P1 hP1
  simpa [hcl]

theorem P1_iff_P2_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  constructor
  · intro _hP1
    -- `A` is an open subset of `closure A`, hence it is contained in the interior of `closure A`.
    have hsub : (A : Set X) ⊆ interior (closure A) := by
      simpa using interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    simpa [P2, hA.interior_eq] using hsub
  · intro hP2
    exact P2_imp_P1 hP2

theorem exists_subset_P2_of_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} (hA : A.Nonempty) : ∃ B : Set X, B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  intro x hx
  exact hx.elim