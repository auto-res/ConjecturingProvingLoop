

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    Topology.P1 A ∧ Topology.P3 A := by
  have hA : A ⊆ interior (closure (interior A)) := h
  have h1 : A ⊆ closure (interior A) :=
    Set.Subset.trans hA interior_subset
  have h2 : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h3 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h2
  have h4 : A ⊆ interior (closure A) :=
    Set.Subset.trans hA h3
  exact And.intro h1 h4