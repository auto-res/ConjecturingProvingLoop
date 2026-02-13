

theorem frontier_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (Aᶜ : Set X) = frontier (A : Set X) := by
  classical
  -- Express the closure and interior of a complement via complements.
  have h_cl : closure (Aᶜ : Set X) = (interior (A : Set X))ᶜ :=
    Topology.closure_compl_eq_compl_interior (A := A)
  have h_int : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (A := A)
  -- Substitute the formulas and simplify.
  simp [frontier, h_cl, h_int, Set.diff_eq, Set.compl_compl,
        Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]