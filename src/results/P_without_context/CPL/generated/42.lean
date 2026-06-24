

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact hP2.trans interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  exact hP2.trans (interior_mono (closure_mono interior_subset))

theorem interior_closure_inclusion {X : Type*} [TopologicalSpace X] (A : Set X) : interior (closure (interior A)) ⊆ closure A := by
  exact interior_subset.trans (closure_mono interior_subset)

theorem closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  · exact closure_mono interior_subset
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h

theorem P1_iff_dense_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using h
    ·
      exact closure_mono interior_subset
  · intro hEq
    have : (A : Set X) ⊆ closure A := subset_closure
    simpa [hEq] using this

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  dsimp [P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hxA' : x ∈ interior (closure A) := hA hxA
      have hAincl : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact (interior_mono hAincl) hxA'
  | inr hxB =>
      have hxB' : x ∈ interior (closure B) := hB hxB
      have hBincl : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact (interior_mono hBincl) hxB'

theorem exists_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · exact Set.empty_subset _
  · dsimp [P2]; exact Set.empty_subset _