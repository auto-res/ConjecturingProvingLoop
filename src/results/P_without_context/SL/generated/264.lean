

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P3 (X := X) A := by
  intro hP2
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have hSubset : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hx₂ : x ∈ interior (closure A) := (interior_mono hSubset) hx₁
  exact hx₂