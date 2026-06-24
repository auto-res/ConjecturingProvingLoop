

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A :=
by
  intro hP2
  dsimp [P2, P3] at *
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := hP2 hxA
  have hSubset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  exact (interior_mono hSubset) hx1