

theorem P2_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure A) := by
  intro hP3
  -- Use the equivalence between `P3` and openness for closed sets.
  have hOpen : IsOpen (closure A) :=
    (Topology.P3_closure_iff_open (A := A)).1 hP3
  -- Translate openness back to `P2` via the corresponding equivalence.
  exact (Topology.P2_closure_iff_open (A := A)).2 hOpen