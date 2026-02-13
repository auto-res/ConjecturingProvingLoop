

theorem P1_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  simpa using ((P1_iff_closure_eq_closure_interior (A := A)).1 hP1).symm

theorem exists_dense_open_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U : Set X, IsOpen U ∧ closure U = closure A := by
  intro hP2
  refine ⟨interior A, isOpen_interior, ?_⟩
  simpa using (P2_implies_closure_eq (A := A) hP2).symm

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ Topology.P1 A ∧ Topology.P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_implies_P1 (A := A) hP2, P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    intro x hxA
    have hEq : closure A = closure (interior A) :=
      (P1_iff_closure_eq_closure_interior (A := A)).1 hP1
    have hx : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using hx

theorem P3_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 A := by
  intro x hxA
  exact h (subset_closure hxA)