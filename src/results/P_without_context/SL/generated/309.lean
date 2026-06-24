

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  dsimp [P2, P3] at hP2 ⊢
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsubset : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hsubset
  exact hmono hx'