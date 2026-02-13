

theorem Topology.P2_iff_P3_and_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P3 A ∧ closure A = closure (interior A)) := by
  -- First, express `P2` in terms of `P1` and `P3`.
  have h1 : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) :=
    Topology.P2_iff_P1_and_P3 (A := A)
  -- Next, replace `P1` by the closure equality using the existing equivalence.
  have h2 : Topology.P1 A ↔ closure A = closure (interior A) :=
    Topology.P1_iff_closure_eq_closure_interior (A := A)
  have h3 :
      (Topology.P1 A ∧ Topology.P3 A) ↔
        (closure A = closure (interior A) ∧ Topology.P3 A) := by
    simpa using (and_congr h2 (Iff.rfl))
  -- Finally, reorder the conjuncts to match the desired statement.
  have h4 :
      (closure A = closure (interior A) ∧ Topology.P3 A) ↔
        (Topology.P3 A ∧ closure A = closure (interior A)) := by
    constructor
    · intro h; exact And.symm h
    · intro h; exact And.symm h
  -- Chain the equivalences.
  simpa using h1.trans (h3.trans h4)