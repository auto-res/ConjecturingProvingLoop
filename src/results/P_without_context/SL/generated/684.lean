

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hA
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure
  exact Set.Subset.trans hA h1