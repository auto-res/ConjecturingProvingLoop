

theorem Topology.boundary_complement {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior A = closure (Aᶜ) \ interior (Aᶜ) := by
  classical
  calc
    closure (A : Set X) \ interior A
        = closure (A : Set X) ∩ closure (Aᶜ) := by
          simpa using
            (Topology.closure_inter_closureCompl_eq_closure_diff_interior
              (A := A)).symm
    _ = closure (Aᶜ) ∩ closure (A : Set X) := by
          simp [Set.inter_comm]
    _ = closure (Aᶜ) \ interior (Aᶜ) := by
          simpa using
            (Topology.closure_inter_closureCompl_eq_closure_diff_interior
              (A := Aᶜ))