

theorem Topology.Dense.inter_nonempty_of_open
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Dense (A : Set X)) (hU : IsOpen U) (hU_non : U.Nonempty) :
    ((A : Set X) ∩ U).Nonempty := by
  classical
  rcases hU_non with ⟨x, hxU⟩
  -- Since `A` is dense, every point of the space belongs to the closure of `A`.
  have hx_closure : (x : X) ∈ closure (A : Set X) := by
    -- `closure A = univ`
    have h_closure_eq : closure (A : Set X) = (Set.univ : Set X) := hA.closure_eq
    simpa [h_closure_eq] using (by trivial)
  -- Apply the characterization of closure with respect to the open set `U`.
  have h_inter : ((U : Set X) ∩ A).Nonempty :=
    (mem_closure_iff).1 hx_closure U hU hxU
  -- Reorder the intersection to match the goal.
  simpa [Set.inter_comm] using h_inter