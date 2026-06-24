

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A :=
by
  intro hP2
  dsimp [P2, P1] at *
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_cl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int
  exact hx_cl