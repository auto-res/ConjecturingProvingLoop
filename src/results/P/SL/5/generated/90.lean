

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  dsimp [Topology.P1] at *
  intro x hx
  have hsubset :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    Topology.P3_closure_subset (X := X) (A := A) hA
  exact hsubset hx