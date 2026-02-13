

theorem P1_closure_subset_of_superset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1 : Topology.P1 (X := X) A) (hSub : closure (interior A) ⊆ B) :
    closure (A : Set X) ⊆ B := by
  intro x hx
  have hx' : x ∈ closure (interior A) := by
    have hsubset := Topology.P1_closure_subset (X := X) (A := A) hP1
    exact hsubset hx
  exact hSub hx'