

theorem dense_inter_open_nonempty {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hA : closure (A : Set X) = (Set.univ : Set X))
    (hU : IsOpen (U : Set X)) (hU_nonempty : (U : Set X).Nonempty) :
    ((A ∩ U) : Set X).Nonempty := by
  -- Choose a point `x` in the non-empty open set `U`.
  rcases hU_nonempty with ⟨x, hxU⟩
  -- Since `A` is dense, `x` lies in the closure of `A`.
  have hx_closureA : (x : X) ∈ closure (A : Set X) := by
    simpa [hA] using (Set.mem_univ (x : X))
  -- The neighbourhood characterisation of closure yields
  -- that `U` meets `A`.
  have h_inter : ((U : Set X) ∩ A).Nonempty :=
    (mem_closure_iff.1 hx_closureA) U hU hxU
  -- Reorder the intersection to obtain the required statement.
  simpa [Set.inter_comm] using h_inter