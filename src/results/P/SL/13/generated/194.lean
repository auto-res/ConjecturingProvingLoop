

theorem Topology.P1_implies_interior_closure_subset_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A →
      interior (closure (A : Set X)) ⊆ closure (interior A) := by
  intro hP1
  -- Translate `P1` into the equality of the two closures.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)).1 hP1
  intro x hx
  -- Rewrite `hx` using `h_eq`.
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [h_eq] using hx
  -- Conclude with the basic inclusion `interior ⊆ closure`.
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) hx'