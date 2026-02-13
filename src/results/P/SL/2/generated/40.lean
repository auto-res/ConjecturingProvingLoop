

theorem Topology.P2_iff_closure_interior_eq_closure_and_P3 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (closure (interior A) = closure A ∧ Topology.P3 A) := by
  -- We will shuttle between the existing equivalences
  -- `P2 A ↔ P1 A ∧ P3 A` and `P1 A ↔ closure (interior A) = closure A`.
  have h₁ := (Topology.P2_iff_P1_and_P3 (A := A))
  have h₂ := (Topology.P1_iff_closure_interior_eq_closure (A := A))
  constructor
  · intro hP2
    -- From `P2`, obtain `P1` and `P3`.
    rcases (h₁).1 hP2 with ⟨hP1, hP3⟩
    -- Turn `P1` into the closure equality.
    have hEq : closure (interior A) = closure A := (h₂).1 hP1
    exact ⟨hEq, hP3⟩
  · rintro ⟨hEq, hP3⟩
    -- The closure equality gives `P1`.
    have hP1 : Topology.P1 A := (h₂).2 hEq
    -- Combine `P1` and `P3` to recover `P2`.
    exact (h₁).2 ⟨hP1, hP3⟩