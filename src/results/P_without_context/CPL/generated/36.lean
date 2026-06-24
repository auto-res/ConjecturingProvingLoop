

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact hP2.trans interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  have h_closure_subset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure_subset
  exact hP2.trans h_int_subset

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  -- Unfold `P3` in the hypotheses to get the subset conditions
  simp [P3] at hA hB
  -- Construct the required inclusion
  have hGoal : (A ∪ B : Set X) ⊆ interior (closure (A ∪ B)) := by
    intro x hx
    cases hx with
    | inl hxA =>
        -- `x` comes from `A`
        have hxA' : x ∈ interior (closure A) := hA hxA
        -- `A` is contained in `A ∪ B`
        have h_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        -- Monotonicity of closure and interior
        have h_closure_subset : closure A ⊆ closure (A ∪ B) :=
          closure_mono h_subset
        have h_int_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
          interior_mono h_closure_subset
        exact h_int_subset hxA'
    | inr hxB =>
        -- `x` comes from `B`
        have hxB' : x ∈ interior (closure B) := hB hxB
        -- `B` is contained in `A ∪ B`
        have h_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        -- Monotonicity of closure and interior
        have h_closure_subset : closure B ⊆ closure (A ∪ B) :=
          closure_mono h_subset
        have h_int_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
          interior_mono h_closure_subset
        exact h_int_subset hxB'
  -- Repackage the inclusion as `P3 (A ∪ B)`
  simpa [P3] using hGoal

theorem P1_top {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [P1, interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem exists_dense_subset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B : Set X, B ⊆ A ∧ Topology.P2 B := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · intro x hx
    cases hx
  · intro x hx
    cases hx

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply subset_antisymm
    · exact closure_mono (interior_subset : interior A ⊆ A)
    ·
      have : closure A ⊆ closure (interior A) := by
        have h' : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
        simpa [closure_closure] using h'
      exact this
  · intro h_eq
    have : (A : Set X) ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure A := subset_closure
      simpa [h_eq] using hA
    exact this