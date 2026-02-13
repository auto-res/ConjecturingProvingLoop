

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P1 A := by
  intro hP2
  exact Set.Subset.trans hP2 interior_subset

theorem openSet_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  simpa [P1, hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A)

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [P3] at *
  refine
    Set.union_subset
      (Set.Subset.trans hA <|
        interior_mono <|
          closure_mono (by
            intro x hx
            exact Or.inl hx))
      (Set.Subset.trans hB <|
        interior_mono <|
          closure_mono (by
            intro x hx
            exact Or.inr hx))

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    have h₂ : (closure A : Set X) ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    exact Set.Subset.antisymm h₁ h₂
  · intro h_eq
    have h : (A : Set X) ⊆ closure (interior A) := by
      have hA : (A : Set X) ⊆ closure A := subset_closure
      simpa [h_eq] using hA
    simpa [P1] using h