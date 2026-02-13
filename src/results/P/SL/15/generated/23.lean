

theorem P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  have h_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  have hx' : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  have h_mono : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int_subset : interior A ⊆ interior (closure A) := by
      have h_subset : A ⊆ closure A := subset_closure
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact h_mono hx'