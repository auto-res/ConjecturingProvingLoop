

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) : P2 A → P1 A := by
  intro hP2
  intro x hxA
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) (hP2 hxA)

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono this
  exact hsubset (hP2 hxA)

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) : interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  have h₁ : x ∈ interior (closure A) := by
    have hmono : closure (interior A) ⊆ closure A := closure_mono interior_subset
    have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hmono
    exact hsubset hx
  exact (interior_subset : interior (closure A) ⊆ closure A) h₁

theorem P3_iff_exists_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    exact hP3
  · rintro ⟨U, hU_open, hA_sub_U, hU_sub_closure⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    have hU_sub_int : U ⊆ interior (closure A) :=
      interior_maximal hU_sub_closure hU_open
    exact hU_sub_int hxU

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) : P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure A ⊆ closure (interior A)`
      have hclosed : IsClosed (closure (interior A)) := isClosed_closure
      exact closure_minimal hP1 hclosed
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
  · intro hEq
    -- need to show `A ⊆ closure (interior A)`
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [hEq] using hx_closure

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa using hx

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  exact Set.empty_subset _