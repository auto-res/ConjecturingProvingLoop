

theorem Topology.frontier_eq_closure_inter_compl_of_isOpen' {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    frontier A = closure A ∩ Aᶜ := by
  have h := Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hA
  simpa [Set.diff_eq] using h