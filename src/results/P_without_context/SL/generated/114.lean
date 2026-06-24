

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  have hIncl : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hSub : closure (interior A) ⊆ closure A := by
      have hIntSub : interior A ⊆ A := interior_subset
      exact closure_mono hIntSub
    exact interior_mono hSub
  exact hIncl hxInt