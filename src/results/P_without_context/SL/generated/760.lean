

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A :=
by
  intro hA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hA.trans hsubset